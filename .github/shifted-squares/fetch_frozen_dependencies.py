#!/usr/bin/env python3
"""Materialize only the public Git objects selected by the frozen dependency recipe."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import shutil
import subprocess
import tempfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def metadata(raw):
    return (json.dumps(raw, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()


def get_git_rows(encoded):
    rows = []
    for line in encoded.split(b"\0"):
        if not line:
            continue
        descriptor, raw_path = line.split(b"\t", 1)
        mode, kind, blob, size = descriptor.decode("ascii").split()
        path = raw_path.decode("utf-8")
        pure = PurePosixPath(path)
        require(str(pure) == path and not pure.is_absolute()
                and not ({".", "..", ".git", ".lake"} & set(pure.parts))
                and "\\" not in path, f"Out-of-scope Git path {path}")
        require((mode, kind) in {("040000", "tree"), ("100644", "blob"), ("100755", "blob"),
                                ("120000", "blob")}, f"Unsupported Git entry {path}")
        rows.append([path, mode, kind, blob, int(size) if kind == "blob" else None])
    return sorted(rows, key=lambda row: row[0].encode())


def materialize(command, git_env, entries, destination):
    destination.mkdir()
    by_name = {row[0]: row for row in entries}
    require(len(by_name) == len(entries), "Duplicate path")
    for path, _, kind, _, _ in entries:
        if kind == "tree":
            (destination / path).mkdir()
    with subprocess.Popen([*command, "cat-file", "--batch"], env=git_env,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as blobs:
        records = []
        for path, mode, kind, blob, size in entries:
            if kind != "blob":
                continue
            require(0 <= size <= 16 * 1024**2, f"Oversize blob at {path}")
            blobs.stdin.write(blob.encode() + b"\n")
            blobs.stdin.flush()
            header = f"{blob} blob {size}\n".encode()
            require(blobs.stdout.readline() == header, f"Missing pinned blob at {path}")
            raw = blobs.stdout.read(size)
            require(len(raw) == size and blobs.stdout.read(1) == b"\n", f"Truncated blob at {path}")
            git_body = f"blob {size}\0".encode() + raw
            require(hashlib.sha1(git_body, usedforsecurity=False).hexdigest() == blob,
                    f"Git object hash differs at {path}")
            target = destination / path
            if mode == "120000":
                link = raw.decode("utf-8")
                selected = posixpath.normpath(posixpath.join(posixpath.dirname(path), link))
                require(link and not link.startswith("/") and "\\" not in link
                        and selected in by_name and by_name[selected][1] in ("100644", "100755"),
                        f"Unpinned symbolic link at {path}")
                target.symlink_to(link)
            else:
                with target.open("xb") as out:
                    out.write(raw)
                target.chmod(0o700 if mode == "100755" else 0o600)
            records.append({"path": path, "mode": mode, "size_bytes": size,
                            "git_blob": blob, "sha256": sha(raw)})
        blobs.stdin.close()
        require(blobs.wait(timeout=30) == 0, "Git blob stream failed")
    return records


def prepare(pin, output):
    git_env = {
        "PATH": "/usr/bin:/bin", "LC_ALL": "C", "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_TERMINAL_PROMPT": "0", "GIT_ATTR_NOSYSTEM": "1",
    }
    git = shutil.which("git")
    require(git, "Git required for public object acquisition")
    name = pin["name"]
    commit = pin["commit"]
    with tempfile.TemporaryDirectory(prefix=name + "-git-", dir=output) as work:
        command = [git, "-C", work]

        def run(*args):
            return subprocess.run([*command, *args], env=git_env, stdin=subprocess.DEVNULL,
                                  stdout=subprocess.PIPE, check=True, timeout=180).stdout

        run("init", "--quiet")
        run("fetch", "--quiet", "--depth=1", "--no-tags", "--no-recurse-submodules",
            "https://github.com/" + pin["repository"] + ".git", commit)
        require(run("rev-parse", "FETCH_HEAD").decode().strip() == commit, f"{name}: commit differs")
        tree = run("rev-parse", commit + "^{tree}").decode().strip()
        require(tree == pin["tree"], f"{name}: root Git tree differs")
        entries = get_git_rows(run("ls-tree", "-r", "-t", "-l", "-z", "--full-tree", commit))
        tree_metadata = {
            "schema_version": "PinnedSourceTreeV1", "package": name, "commit": commit,
            "tree": tree, "entries": entries,
        }
        require(sha(metadata(tree_metadata)) == pin["source_tree_digest"],
                f"{name}: complete Git tree metadata hash differs")
        destination = output / "packages" / name
        files = materialize(command, git_env, entries, destination)
        config = {
            pin["config_file"]: pin["config_sha256"],
            "lean-toolchain": pin["toolchain_sha256"],
            "lake-manifest.json": pin["manifest_sha256"],
        }
        for path, digest in config.items():
            require(sha((destination / path).read_bytes()) == digest, f"{name}: {path} differs")
        report = {
            "schema_version": "PreparedRawSourceV1", "package": name, "commit": commit,
            "git_tree": tree, "source_tree_digest": pin["source_tree_digest"], "files": files,
            "qualification": "RAW_SOURCE_BYTES_ONLY", "pinned_configuration_hashes": config,
        }
        (output / "receipts" / (name + ".json")).write_bytes(metadata(report))
    print(f"{name}: {len(files)} pinned Git blobs", flush=True)
    return {"name": name, "files": len(files), "commit": commit, "tree": tree,
            "source_tree_digest": pin["source_tree_digest"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("recipe", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    raw = args.recipe.read_bytes()
    require(sha(raw) == "b69e6425f952a21738765a9d2a2527f6935a15020243bdf658a9df629b9a72b0",
            "Wrong frozen dependency recipe")
    args.output.mkdir()
    (args.output / "packages").mkdir()
    (args.output / "receipts").mkdir()
    with ThreadPoolExecutor(max_workers=5) as pool:
        rows = list(pool.map(lambda p: prepare(p, args.output), json.loads(raw)["packages"]))
    (args.output / "receipts/dependencies.json").write_bytes(metadata(rows))


if __name__ == "__main__":
    main()
