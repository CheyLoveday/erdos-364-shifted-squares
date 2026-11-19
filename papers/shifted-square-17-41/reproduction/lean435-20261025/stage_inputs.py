#!/usr/bin/env python3
"""Check and stage one frozen selection. Never download, build, or run Lean."""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import tarfile

ROOT = Path(__file__).resolve().parent
SOURCE_SHA256 = "6b6e03af11d97237a5c3616ccd2ae5985f95a8940a3c373bca208bdb64bd3001"
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_bytes())


def safe_path(name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and str(path) == name, "Noncanonical input path")
    require(all(p not in ("", ".", "..") for p in path.parts), "Unsafe input path")
    require("\\" not in name and bool(path.parts), "Unsafe input path")
    return path


def archive_files(archive, config):
    expected = {r["path"]: r for r in config["reference_files"]}
    require(len(expected) == len(config["reference_files"]) == 61, "Expected 61 unique files")
    result = {}
    with tarfile.open(archive, "r:") as source:
        for member in source:
            safe_path(member.name)
            require(member.isfile() and not member.sparse, "Only regular source files allowed")
            require(member.name in expected and member.name not in result, "Unexpected/duplicate member")
            row = expected[member.name]
            require(member.size == row["size_bytes"], "Source size mismatch")
            raw = source.extractfile(member).read()
            require(digest(raw) == row["sha256"], "Source SHA-256 mismatch: " + member.name)
            result[member.name] = raw
    require(set(result) == set(expected), "Missing source member")
    require(all(p.endswith(".lean") for p in result), "Unexpected source type")
    require(sorted(p[:-5].replace("/", ".") for p in result) == config["root_modules"],
            "Source files and selected roots differ")
    return result


def check(root=ROOT):
    manifest = read_json(root / "frozen-inputs.json")
    require(manifest["source_archive_sha256"] == SOURCE_SHA256, "Historical archive identity changed")
    names = set()
    for row in manifest["files"]:
        safe_path(row["path"])
        require(row["path"] not in names, "Duplicate frozen input")
        names.add(row["path"])
        path = root / row["path"]
        require(not path.is_symlink() and path.is_file(), "Missing/nonregular frozen input")
        raw = path.read_bytes()
        require(len(raw) == row["bytes"] and digest(raw) == row["sha256"],
                "Frozen input identity mismatch: " + row["path"])
    require(names == {"frozen/" + n for n in (
        "source.tar", "project-config.json", "comparison.json", "nanoda.json",
        "tools.json", "environment.json", "mathlib-recipe.json", "lean-recipe.json"
    )} | {"helpers/" + n for n in ("Build.py", "Inventory.lean", "Inspect.lean", "HashInputs.lean")},
        "Frozen input allowlist changed")
    config = read_json(root / "frozen/project-config.json")
    recipe = read_json(root / "frozen/mathlib-recipe.json")
    environment = read_json(root / "frozen/environment.json")
    lean = read_json(root / "frozen/lean-recipe.json")
    comparison = read_json(root / "frozen/comparison.json")
    nanoda = read_json(root / "frozen/nanoda.json")
    require(digest((root / "frozen/source.tar").read_bytes()) == SOURCE_SHA256
            == config["reference_bundle_digest"], "Archive/reference binding differs")
    require(digest((root / "frozen/environment.json").read_bytes())
            == config["environment_receipt_digest"], "Environment binding differs")
    require(digest((root / "frozen/mathlib-recipe.json").read_bytes())
            == environment["spec_digest"], "Dependency recipe binding differs")
    # The base recipe identifier was computed from canonical JSON, not pretty bytes.
    canonical = (json.dumps(lean, sort_keys=True, separators=(",", ":")) + "\n").encode()
    require(digest(canonical) == recipe["base_lean_recipe_digest"], "Base Lean recipe differs")
    require(lean["lean"]["version"] == "4.35.0"
            and recipe["toolchain"] == "leanprover/lean4:v4.35.0"
            and lean["platform"] == recipe["platform"] == "linux/amd64", "Wrong toolchain/platform")
    require(config["lean_options"] == {"autoImplicit": False, "maxRecDepth": 100000}
            and config["module_exclusions"] == [] and config["project_scope"] == "project_all",
            "Frozen compiler options/scope differ")
    require([p["name"] for p in recipe["packages"]] == config["environment_packages"]
            and len(recipe["packages"]) == 9, "Dependency selection differs")
    mathlib = next(p for p in recipe["packages"] if p["name"] == "mathlib")
    require(mathlib["manifest_sha256"] == environment["dependency_manifest_digest"],
            "Mathlib manifest binding differs")
    require(comparison["theorem_names"] == config["target_declarations"]
            and len(comparison["theorem_names"]) == 3
            and comparison["permitted_axioms"] == AXIOMS
            and comparison["protected_definition_names"] == config["protected_definitions"] == []
            and comparison["definition_holes"] == [], "Comparison selection differs")
    require(nanoda["permitted_axioms"] == AXIOMS
            and nanoda["unpermitted_axiom_hard_error"] is False,
            "Historical Nanoda configuration differs")
    files = archive_files(root / "frozen/source.tar", config)
    return config, recipe, files


def project_lakefile(config, role):
    # Exact spelling used by the October ProjectConfiguration.lakefile method.
    lines = ['name = "service_project"', 'version = "0.0.0"',
             'buildDir = "/work/build"', 'packagesDir = "/work/packages"',
             'srcDir = "/inputs/proofs/' + role + '/source"', '[[lean_lib]]',
             'name = "ServiceProject"', 'roots = ' + json.dumps(config["root_modules"])]
    for name in config["environment_packages"]:
        lines += ['[[require]]', 'name = ' + json.dumps(name),
                  'path = ' + json.dumps('/inputs/packages/' + name)]
    lines += ['[leanOptions]'] + [json.dumps(k) + ' = ' + json.dumps(v)
                                for k, v in sorted(config["lean_options"].items())]
    return ("\n".join(lines) + "\n").encode()


def stage(destination, root=ROOT):
    config, recipe, files = check(root)
    destination = Path(destination).absolute()
    require(not destination.exists() and not destination.is_symlink(), "Output must be new")
    require(not destination.resolve().is_relative_to(root.resolve()), "Output must be outside package")
    destination.mkdir(parents=True)
    records = []

    def put(name, raw, source):
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as out:
            out.write(raw)
        records.append({"path": name, "bytes": len(raw), "sha256": digest(raw), "source": source})

    def data(name, obj, source):
        put(name, (json.dumps(obj, sort_keys=True, indent=2) + "\n").encode(), source)

    for name in ("project-config.json", "comparison.json", "nanoda.json"):
        put("inputs/" + name, (root / "frozen" / name).read_bytes(), "frozen/" + name)
    for name in ("Build.py", "Inventory.lean", "HashInputs.lean"):
        put("inputs/" + name, (root / "helpers" / name).read_bytes(), "helpers/" + name)
    put("trusted/Inspect.lean", (root / "helpers/Inspect.lean").read_bytes(), "helpers/Inspect.lean")
    entries = [{"type": "path", "name": p["name"], "dir": "/inputs/packages/" + p["name"],
                "inherited": False, "configFile": p["config_file"], "manifestFile": "lake-manifest.json"}
               for p in recipe["packages"]]
    manifest = {"version": "1.1.0", "packagesDir": "/work/packages", "name": "service_project",
                "lakeDir": ".lake", "packages": entries}
    overrides = {"schemaVersion": "1.3.0", "packages": [
        {k: v for k, v in row.items() if k != "manifestFile"} for row in entries]}
    data("inputs/overrides.json", overrides, "frozen/mathlib-recipe.json; path mapping only")
    for role in ("reference", "positive"):
        base = "inputs/proofs/" + role + "/"
        for path, raw in sorted(files.items()):
            put(base + "source/" + path, raw, "frozen/source.tar:" + path)
        put(base + "lakefile.toml", project_lakefile(config, role), "frozen/project-config.json")
        data(base + "lake-manifest.json", manifest, "frozen/mathlib-recipe.json; path mapping only")
        aggregate = "\n".join("import " + ".".join("«" + p + "»" for p in n.split("."))
                              for n in config["root_modules"]) + "\n"
        put(base + "_FormalCodeProjectRoot.lean", aggregate.encode(), "frozen/project-config.json:root_modules")
        (destination / base / ".lake").mkdir()
    dependencies = ('name = "service_dependencies"\nversion = "0.0.0"\n'
                    'buildDir = "/work/dependency-build"\npackagesDir = "/work/packages"\n'
                    + "\n".join('[[require]]\nname = ' + json.dumps(n) + '\npath = '
                                + json.dumps('/inputs/packages/' + n)
                                for n in config["environment_packages"]) + "\n")
    put("inputs/dependency-build/lakefile.toml", dependencies.encode(), "frozen/mathlib-recipe.json")
    data("inputs/dependency-build/lake-manifest.json", {**manifest, "name": "service_dependencies"},
         "frozen/mathlib-recipe.json; path mapping only")
    (destination / "inputs/dependency-build/.lake").mkdir()
    summary = {"status": "STAGED_INPUTS_ONLY", "build": "NOT_RUN", "six_checkers": "NOT_RUN",
               "source_archive_sha256": SOURCE_SHA256, "source_modules_per_role": len(files),
               "dependency_packages": len(recipe["packages"]), "target_declarations": config["target_declarations"],
               "generator": "stage_inputs.py", "generator_sha256": digest((root / "stage_inputs.py").read_bytes()),
               "generation_command": "python3 stage_inputs.py stage NEW_OUTPUT_DIRECTORY",
               "files": records}
    (destination / "staging-receipt.json").write_text(json.dumps(summary, indent=2) + "\n")
    return {k: v for k, v in summary.items() if k != "files"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("check", help="Check frozen inputs without writing or running code")
    staging = commands.add_parser("stage", help="Materialise inputs in a new directory; do not execute them")
    staging.add_argument("output", type=Path)
    args = parser.parse_args()
    if args.command == "stage":
        print(json.dumps(stage(args.output), indent=2))
    else:
        config, recipe, files = check()
        print(json.dumps({"input_identity": "PASS", "source_files": len(files),
                          "dependency_pins": len(recipe["packages"]),
                          "selected_endpoints": len(config["target_declarations"]),
                          "build": "NOT_RUN", "six_checkers": "NOT_RUN"}, indent=2))


if __name__ == "__main__":
    main()
