#!/usr/bin/env python3
"""Run one frozen shifted-squares replay on an already qualified Linux guest."""

import argparse
import hashlib
import json
import os
import platform
import re
import resource
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path


SOURCE = "4da472744c0425ec520e6e96e364170e1c3a977e"
CHECKSUMS = "50fec9ac86e86288630055372b415594741e06e1e51cc47a9602a74375e94280"
LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
LEAN = "/opt/lean/bin/lean"
EXPORT = "/inputs/export.ndjson"
PRIMITIVES = (
    "Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble "
    "Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat "
    "List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
).split()
CHECKERS = {
    "leanchecker": ["leanchecker", "--silent", "--from-export", EXPORT],
    "leanchecker-paranoid": ["leanchecker-paranoid", "--silent", "--from-export", EXPORT],
    "lean4lean": ["lean4lean", "--import", EXPORT],
    "nanoda": ["nanoda_bin", "/inputs/nanoda.json"],
    "con-leche": ["con-leche", EXPORT],
    "con-ron": ["con-ron", EXPORT],
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def save(path, value):
    with path.open("x") as out:
        json.dump(value, out, sort_keys=True, indent=2)
        out.write("\n")


def sha(path):
    with Path(path).open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def manifest(root, *, links=False):
    rows = {}
    for path in sorted(root.rglob("*")):
        name = str(path.relative_to(root))
        if path.is_symlink():
            require(links, f"Unexpected symlink {name}")
            value = os.readlink(path)
            content = value.encode()
            rows[name] = [len(content), hashlib.sha256(content).hexdigest(), "120000"]
        elif path.is_file():
            mode = "100755" if path.stat().st_mode & 0o111 else "100644"
            rows[name] = [path.stat().st_size, sha(path), mode]
    return rows


def keep_bounded():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    resource.setrlimit(resource.RLIMIT_FSIZE, (1024**3, 1024**3))


def binding(option, source, target):
    return [option, str(source), target]


def verify_dependencies(package, deps):
    recipe = load(package / "frozen/mathlib-recipe.json")
    received = load(deps / "receipts/dependencies.json")
    rows = recipe["packages"]
    require([p["name"] for p in rows] == [p["name"] for p in received], "Wrong dependency names")
    recorded = {}
    for pin, summary in zip(rows, received, strict=True):
        name = pin["name"]
        receipt = load(deps / "receipts" / (name + ".json"))
        require(
            (receipt["package"], receipt["commit"], receipt["git_tree"], receipt["source_tree_digest"])
            == (name, pin["commit"], pin["tree"], pin["source_tree_digest"]),
            f"{name}: receipt identity differs",
        )
        expect = {}
        for f in receipt["files"]:
            require(f["path"] not in expect, f"{name}: duplicate receipt file")
            expect[f["path"]] = [f["size_bytes"], f["sha256"], f["mode"]]
        recorded[name] = manifest(deps / "packages" / name, links=True)
        require(recorded[name] == expect, f"{name}: transferred package bytes/modes differ")
        require(summary["files"] == len(expect), f"{name}: receipt coverage mismatch")
        for filename, key in ((pin["config_file"], "config_sha256"),
                              ("lean-toolchain", "toolchain_sha256"),
                              ("lake-manifest.json", "manifest_sha256")):
            require(expect[filename][1] == pin[key], f"{name}: {filename} not pinned")
    return recorded


def graph(rows):
    result = {}
    for row in rows:
        require(set(row) == {"name", "references"}, "Malformed graph row")
        name = row["name"]
        refs = row["references"]
        require(isinstance(name, str) and name and name not in result
                and isinstance(refs, list) and all(isinstance(n, str) and n for n in refs),
                "Malformed or duplicate logical unit")
        result[name] = frozenset(refs)
    require(result and all(refs <= result.keys() for refs in result.values()), "Incomplete logical closure")
    return result


def coverage(inventory, observed, config):
    require(inventory["schema_version"] == "LogicalInventoryV2", "Wrong logical inventory version")
    modules = [m["name"] for m in inventory["modules"]]
    require(modules == config["root_modules"] and len(set(modules)) == 61, "Wrong module scope")
    ownership = {}
    for row in inventory["modules"]:
        for name in row["declarations"]:
            require(name not in ownership, f"Duplicate project declaration {name}")
            ownership[name] = row["name"]
    excluded = {}
    for row in inventory["excluded"]:
        require(row["module"] in modules and row["safety"] in ("unsafe", "partial")
                and row["name"] not in excluded and row["name"] not in ownership,
                "Incorrect nonlogical partition")
        excluded[row["name"]] = [row["module"], row["safety"]]
    expected = graph(inventory["units"])
    actual = graph(observed["units"])
    require(ownership.keys() <= expected.keys() and not excluded.keys() & expected.keys(),
            "Project partition differs from logical closure")
    required = config["target_declarations"] + config["protected_definitions"]
    require(set(required) <= ownership.keys(), "Endpoint or protected definition is not project-owned")
    missing = sorted(expected.keys() - actual.keys())
    extra = sorted(actual.keys() - expected.keys())
    conflicts = sorted(n for n in expected.keys() & actual.keys() if expected[n] != actual[n])
    require(not (missing or extra or conflicts),
            f"Export coverage mismatch. Missing {missing[:8]}. Extra {extra[:8]}. Conflicts {conflicts[:8]}.")
    return ownership, excluded, expected


class Replay:
    def __init__(self, args):
        self.args = args
        self.stage_dir = args.output / "stage"
        self.inputs = self.stage_dir / "inputs"
        self.work = args.output / "work"
        self.logs = args.output / "logs"
        self.results = args.output / "results"
        self.cache = args.output / "dependency-build"
        self.sources = args.output / "dependency-sources"
        self.export_dirs = args.output / "exports"
        self.bwrap = shutil.which("bwrap")
        npm = Path("/usr/bin/npm").resolve()
        self.npm_mask = [str(npm)] if npm.is_file() and npm.is_relative_to("/usr") else []
        self.hash_binds = []
        self.stage_status = {}
        self.config = load(args.package / "frozen/project-config.json")
        self.recipe = load(args.package / "frozen/mathlib-recipe.json")
        self.comparison = load(args.package / "frozen/comparison.json")

    def run(self, label, argv):
        stdout = self.logs / (label + ".stdout")
        stderr = self.logs / (label + ".stderr")
        start = time.monotonic()
        expired = False
        print(f"START {label}", flush=True)
        with stdout.open("xb") as out, stderr.open("xb") as err:
            with subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                                  start_new_session=True, preexec_fn=keep_bounded) as child:
                try:
                    status = child.wait(timeout=self.args.stage_seconds)
                except subprocess.TimeoutExpired:
                    expired = True
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    status = child.wait()
        record = {
            "argv": argv, "status": status, "timeout": expired, "seconds": time.monotonic() - start,
            "stdout": [stdout.stat().st_size, sha(stdout)],
            "stderr": [stderr.stat().st_size, sha(stderr)],
        }
        save(self.results / (label + ".json"), record)
        self.stage_status[label] = not expired and status == 0
        print(f"END {label} {status} {record['seconds']:.1f}s", flush=True)
        require(self.stage_status[label], f"{label} failed; see {stderr}")
        return stdout

    def isolated(self, work, extra, argv, threads=1):
        return [
            self.bwrap, "--unshare-user", "--unshare-pid", "--unshare-net", "--unshare-ipc",
            "--unshare-uts", "--unshare-cgroup", "--disable-userns", "--cap-drop", "ALL",
            "--new-session", "--die-with-parent", "--clearenv",
            "--setenv", "LANG", "C", "--setenv", "TMPDIR", "/work",
            "--setenv", "PATH", "/opt/lean/bin:/usr/bin:/bin",
            "--setenv", "LEAN_NUM_THREADS", str(threads),
            "--setenv", "LEAN_STACK_SIZE_KB", "16384", "--setenv", "LEAN_ABORT_ON_PANIC", "1",
            "--setenv", "LAKE_NO_CACHE", "true", "--ro-bind", "/usr", "/usr",
            *(arg for path in self.npm_mask for arg in ("--ro-bind", "/dev/null", path)),
            "--symlink", "usr/bin", "/bin", "--symlink", "usr/lib", "/lib",
            "--symlink", "usr/lib64", "/lib64", "--proc", "/proc", "--dir", "/dev",
            "--dev-bind", "/dev/null", "/dev/null", "--dev-bind", "/dev/zero", "/dev/zero",
            "--dev-bind", "/dev/urandom", "/dev/urandom", "--bind", str(work), "/work",
            "--symlink", "work", "/tmp", "--ro-bind", str(self.args.toolchain), "/opt/lean",
            *extra, "--remount-ro", "/", "--chdir", "/work", "--", *argv,
        ]

    def builder(self, label, role, argv, *, writable_packages=False):
        current = self.work / role
        current.mkdir(exist_ok=True)
        extra = ["--dir", "/inputs"]
        extra += binding("--ro-bind", self.sources, "/inputs/packages")
        for name in self.config["environment_packages"]:
            option = "--bind" if writable_packages else "--ro-bind"
            extra += binding(option, self.cache / name, f"/inputs/packages/{name}/.lake")
        extra += self.hash_binds
        if role == "hashes":
            extra += binding("--ro-bind", self.results / "hash-inputs.json", "/inputs/hash-inputs.json")
            extra += binding("--ro-bind", self.inputs / "HashInputs.lean", "/inputs/HashInputs.lean")
        elif role == "challenge":
            extra += binding("--ro-bind", self.args.challenge, "/inputs/EndpointChallenge.lean")
        else:
            (current / "lake").mkdir(exist_ok=True)
            source = "dependency-build" if role == "dependencies" else "proofs/" + role
            extra += binding("--ro-bind", self.inputs / source, "/inputs/" + source)
            extra += binding("--bind", current / "lake", "/inputs/" + source + "/.lake")
            extra += binding("--ro-bind", self.inputs / "overrides.json", "/inputs/overrides.json")
            for name in ("Build.py", "Inventory.lean", "project-config.json"):
                extra += binding("--ro-bind", self.inputs / name, "/inputs/" + name)
        return self.run(label, self.isolated(current, extra, argv, threads=2))

    def judge(self, label, role, argv, reference=None, comparison=None):
        work = self.work / label
        work.mkdir()
        extra = ["--dir", "/inputs", "--dir", "/trusted"]
        extra += binding("--ro-bind", self.stage_dir / "trusted/Inspect.lean", "/trusted/Inspect.lean")
        extra += binding("--ro-bind", self.inputs / "nanoda.json", "/inputs/nanoda.json")
        extra += binding("--ro-bind", self.export_file(role), EXPORT)
        if reference is not None:
            extra += ["--dir", "/challenge"]
            extra += binding("--ro-bind", self.export_file(reference), "/challenge/export.ndjson")
            extra += binding("--ro-bind", comparison, "/challenge/comparison.json")
        return self.run(label, self.isolated(work, extra, argv))

    def export_file(self, role):
        return self.export_dirs / role / "export.ndjson"

    def proofwidgets(self):
        widget = self.sources / "proofwidgets/widget"
        prefix = "/inputs/packages/proofwidgets/widget/"
        pairs = [
            [prefix + "package.json", True], [prefix + "package-lock.json", False],
            [prefix + "rollup.config.js", True], [prefix + "tsconfig.json", True],
        ]
        pairs += [[prefix + str(p.relative_to(widget)), True]
                  for p in sorted((widget / "src").rglob("*"))
                  if p.is_file() and p.suffix in (".ts", ".tsx", ".js", ".jsx")]
        save(self.results / "hash-inputs.json", pairs)
        path = self.builder("proofwidgets-hashes", "hashes",
                            [LEAN, "-j1", "-s16384", "-M0", "--run", "/inputs/HashInputs.lean"])
        rows = load(path)
        require([row["path"] for row in rows] == [p[0] for p in pairs], "Wrong widget hash selection")
        generated = self.args.output / "widget-hashes"
        generated.mkdir()
        for i, row in enumerate(rows):
            require(re.fullmatch(r"[0-9a-f]{1,16}", row["hash"]), "Invalid widget hash")
            path = generated / str(i)
            path.write_text(row["hash"])
            target = row["path"] + ".hash"
            (self.sources / target.removeprefix("/inputs/packages/")).touch(exist_ok=False)
            self.hash_binds += binding("--ro-bind", path, target)

    def main(self):
        args = self.args
        require(sys.platform == "linux" and os.geteuid() != 0 and self.bwrap,
                "Requires Linux with bubblewrap and an unprivileged caller")
        require(shutil.disk_usage(args.output.parent).free >= args.free_gib * 1024**3, "Free disk bound")
        args.output.mkdir()
        for directory in (self.work, self.logs, self.results, self.cache, self.export_dirs):
            directory.mkdir()
        require(sha(args.package / "SHA256SUMS") == CHECKSUMS, "Wrong frozen checksum manifest")
        for row in (args.package / "SHA256SUMS").read_text().splitlines():
            checksum, path = row.split("  ", 1)
            require(sha(args.package / path) == checksum, f"Incorrect frozen bytes {path}")
        self.run("stage", [sys.executable, "-I", "-B", str(args.package / "stage_inputs.py"),
                           "stage", str(self.stage_dir)])
        staging_manifest = manifest(self.stage_dir)
        dependencies = verify_dependencies(args.package, args.deps)
        shutil.copytree(args.deps / "packages", self.sources, symlinks=True)
        require(all(manifest(self.sources / n, links=True) == data for n, data in dependencies.items()),
                "Staged dependency sources differ from verified transfer")
        metadata = load(args.package / "frozen/tools.json")
        tools = {target: sha(args.toolchain / target.removeprefix("/opt/lean/"))
                 for target in metadata if target.startswith("/opt/lean/")}
        tool_exact = all(tools[name] == metadata[name] for name in tools)
        require(tool_exact or args.allow_binary_variance,
                "Tool binaries differ from frozen Linux amd64. Record and explicitly allow a platform variance.")
        version = self.run("lean-version", [str(args.toolchain / "bin/lean"), "--version"]).read_text()
        require("version 4.35.0," in version and LEAN_COMMIT in version, "Wrong Lean compiler version/commit")
        save(self.results / "environment.json", {
            "input_pr_head": SOURCE, "lean_version": version.strip(), "exact_tool_binaries": tool_exact,
            "tools": tools, "host": list(platform.uname()), "python": sys.version,
            "python_sha256": sha(sys.executable), "bwrap": self.bwrap, "bwrap_sha256": sha(self.bwrap),
            "os_release": Path("/etc/os-release").read_text(),
            "masked_npm_paths": self.npm_mask,
            "free_at_start_bytes": shutil.disk_usage(args.output).free,
            "stage_timeout_seconds": args.stage_seconds, "file_size_limit_bytes": 1024**3,
        })
        preflight = self.work / "preflight"
        preflight.mkdir()
        outer_net = os.readlink("/proc/self/ns/net")
        self.run("isolation", self.isolated(preflight, [], ["/usr/bin/python3", "-I", "-B", "-c",
            "import os, shutil, sys; from pathlib import Path; "
            "assert os.readlink('/proc/self/ns/net') != sys.argv[1]; "
            "assert not Path('/home').exists() and 'HOME' not in os.environ; "
            "assert shutil.which('npm') is None; "
            "assert 'CapEff:\\t0000000000000000' in Path('/proc/self/status').read_text(); "
            "assert os.statvfs('/').f_flag & os.ST_RDONLY; "
            "assert len(Path('/proc/net/dev').read_text().strip().splitlines()) == 3; "
            "Path('/work/control').write_text('isolated'); print('ISOLATION_OK')", outer_net]))
        for name in self.config["environment_packages"]:
            (self.cache / name).mkdir()
            (self.sources / name / ".lake").mkdir()
        self.proofwidgets()
        mount_sources = manifest(self.sources, links=True)
        lake = ["/opt/lean/bin/lake", "--no-cache", "--fail-fast", "--packages=/inputs/overrides.json"]
        self.builder("dependencies", "dependencies", [*lake, "-d", "/inputs/dependency-build", "build",
                     *("+" + n + ":olean" for n in self.config["dependency_modules"])],
                     writable_packages=True)
        dep_build = manifest(self.cache)
        require(dep_build, "Empty dependency build")
        save(self.results / "compiled-dependencies.json", dep_build)
        proof_results = {}
        for role in ("reference", "positive"):
            self.builder("build-inventory-" + role, role, ["/usr/bin/python3", "-I", "-B", "/inputs/Build.py", role])
            work = self.work / role
            compiled = manifest(work / "build/lib/lean")
            require(all(name.replace(".", "/") + ".olean" in compiled for name in self.config["root_modules"]),
                    "One or more configured root oleans missing")
            save(self.results / (role + "-compiled.json"), compiled)
            destination = self.export_dirs / role
            destination.mkdir()
            (work / "export.ndjson").rename(self.export_file(role))
            parsed = self.judge("parse-" + role, role,
                               [LEAN, "-j1", "-s16384", "-M0", "--run", "/trusted/Inspect.lean", EXPORT])
            proof_results[role] = coverage(load(work / "inventory.json"), load(parsed), self.config)
        require(proof_results["reference"] == proof_results["positive"],
                "Reference/candidate declaration ownership, exclusions or graph differ")
        errors = []
        try:
            self.statement_check("compare-historical", "reference", self.inputs / "comparison.json")
        except ValueError as error:
            errors.append(str(error))
        export_identity = {role: {"bytes": self.export_file(role).stat().st_size, "sha256": sha(self.export_file(role))}
                           for role in proof_results}
        for name, argv in CHECKERS.items():
            try:
                self.judge(name, "positive", ["/opt/lean/bin/" + argv[0], *argv[1:]])
            except ValueError as error:
                errors.append(str(error))
        supplemental_error = None
        try:
            self.check_challenge()
        except ValueError as error:
            supplemental_error = str(error)
        require(manifest(self.stage_dir) == staging_manifest, "Frozen staged inputs changed")
        require(verify_dependencies(args.package, args.deps) == dependencies, "Dependency sources changed")
        require(manifest(self.sources, links=True) == mount_sources, "Mounted dependency sources changed")
        require(manifest(self.cache) == dep_build, "Compiled dependency bytes changed during replay")
        require(all(sha(self.export_file(role)) == row["sha256"] for role, row in export_identity.items()),
                "Serialized export bytes changed during replay")
        frozen = load(args.package / "frozen-inputs.json")
        expected = {"bytes": frozen["historical_export_bytes"], "sha256": frozen["historical_export_sha256"]}
        owners, deferred, logical = proof_results["positive"]
        save(self.results / "summary.json", {
            "status": "REPLAY_STAGE_FAILURE" if errors else "FRESH_SCOPED_REPLAY",
            "proof_scope": "all 61 builds, logical declaration closure, three endpoint statements",
            "selected_theorem_owners": {n: owners[n] for n in self.config["target_declarations"]},
            "logical_units": len(logical), "nonlogical_exclusions": deferred,
            "exports": export_identity, "historical_export": expected,
            "historical_export_bytes_match": export_identity["positive"] == expected,
            "fresh_export_bytes_match": export_identity["reference"] == export_identity["positive"],
            "exact_tool_binaries": tool_exact, "historical_reference_independent": False,
            "stage_results": self.stage_status, "errors": errors,
            "supplemental_error": supplemental_error,
        })
        require(not errors and not supplemental_error, "One or more replay stages failed")

    def statement_check(self, label, reference, comparison):
        parsed = self.judge(label, "positive",
                            [LEAN, "-j1", "-s16384", "-M0", "--run", "/trusted/Inspect.lean",
                             "/challenge/export.ndjson", EXPORT, "/challenge/comparison.json"],
                            reference=reference, comparison=comparison)
        data = load(parsed)
        config = load(comparison)
        require(data["targets"] == self.config["target_declarations"] and data["binder_annotations_checked"],
                "Missing exact endpoint checks")
        require(data["protected_definition_names"] == config["protected_definition_names"],
                "Protected definition check differs")
        require(set(data["used_axioms"]) <= set(self.comparison["permitted_axioms"]),
                "Disallowed axiom in candidate logical closure")
        save(self.results / (label + "-axioms.json"), data["used_axioms"])

    def check_challenge(self):
        if self.args.challenge is None:
            return
        role = "challenge"
        work = self.work / role
        search = "/work:" + ":".join(
            f"/inputs/packages/{name}/.lake/build/lib/lean" for name in self.config["environment_packages"]
        )
        env = ["/usr/bin/env", "LEAN_PATH=" + search]
        self.builder("build-endpoint-challenge", role,
                     [*env, LEAN, "-j1", "-s16384", "-M0", "--root=/inputs",
                      "-o", "/work/EndpointChallenge.olean", "/inputs/EndpointChallenge.lean"])
        exported = self.builder("export-endpoint-challenge", role,
                                [*env, "/opt/lean/bin/leanexport", "EndpointChallenge", "--",
                                 *self.config["target_declarations"], "Erdos364.sm2LucasReal", *PRIMITIVES])
        (self.export_dirs / role).mkdir()
        shutil.copyfile(exported, self.export_file(role))
        self.statement_check("compare-endpoint-challenge", role, self.args.challenge_comparison)


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("package", "deps", "toolchain", "output"):
        parser.add_argument(name, type=lambda name: Path(name).resolve())
    parser.add_argument("--stage-seconds", type=int, required=True)
    parser.add_argument("--free-gib", type=float, required=True)
    parser.add_argument("--allow-binary-variance", action="store_true")
    parser.add_argument("--challenge", type=lambda name: Path(name).resolve())
    parser.add_argument("--challenge-comparison", type=lambda name: Path(name).resolve())
    args = parser.parse_args()
    require(args.stage_seconds > 0 and args.free_gib >= 5, "Invalid resource envelope")
    require(bool(args.challenge) == bool(args.challenge_comparison), "Supply both challenge inputs")
    Replay(args).main()


if __name__ == "__main__":
    cli()
