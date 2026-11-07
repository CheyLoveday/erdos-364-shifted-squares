#!/usr/bin/env python3
"""Focused offline controls for source identity and non-overwriting staging."""

import io
import json
from pathlib import Path
import shutil
import tarfile
import tempfile

import stage_inputs as stage


def rejected(operation):
    try:
        operation()
    except ValueError:
        return
    raise AssertionError("Expected rejection")


def main():
    config, recipe, originals = stage.check()
    controls = []
    with tempfile.TemporaryDirectory(prefix="lean435-staging-check-") as directory:
        root = Path(directory)
        first, second = root / "first", root / "second"
        stage.stage(first)
        stage.stage(second)
        a = json.loads((first / "staging-receipt.json").read_bytes())
        b = json.loads((second / "staging-receipt.json").read_bytes())
        assert a == b
        for row in a["files"]:
            left, right = (first / row["path"]).read_bytes(), (second / row["path"]).read_bytes()
            assert left == right and stage.digest(left) == row["sha256"]
        controls.append("two fresh stagings are byte-identical, including generated receipts")
        for role in ("reference", "positive"):
            for name, raw in originals.items():
                assert (first / "inputs/proofs" / role / "source" / name).read_bytes() == raw
        controls.append("both staged 61-file selections match every frozen source byte")
        prior = (first / "staging-receipt.json").read_bytes()
        rejected(lambda: stage.stage(first))
        assert (first / "staging-receipt.json").read_bytes() == prior
        controls.append("existing output is rejected without alteration")
        linked = root / "linked-output"
        linked.symlink_to(root / "absent-target", target_is_directory=True)
        rejected(lambda: stage.stage(linked))
        assert not (root / "absent-target").exists()
        controls.append("dangling output symlink is rejected")
        damaged = root / "damaged-package"
        shutil.copytree(stage.ROOT, damaged)
        with (damaged / "frozen/source.tar").open("r+b") as output:
            output.seek(1024)
            old = output.read(1)
            output.seek(1024)
            output.write(bytes([old[0] ^ 1]))
        rejected(lambda: stage.check(damaged))
        controls.append("corrupted archive bytes fail the frozen input check")
        name = next(iter(originals))
        for kind in ("missing", "duplicate", "traversal", "symlink"):
            archive = root / (kind + ".tar")
            with tarfile.open(archive, "w") as output:
                if kind == "missing":
                    pass
                else:
                    member = tarfile.TarInfo("../escape.lean" if kind == "traversal" else name)
                    if kind == "symlink":
                        member.type = tarfile.SYMTYPE
                        member.linkname = "../escape.lean"
                        output.addfile(member)
                    else:
                        member.size = len(originals[name])
                        output.addfile(member, io.BytesIO(originals[name]))
                        if kind == "duplicate":
                            output.addfile(member, io.BytesIO(originals[name]))
            rejected(lambda: stage.archive_files(archive, config))
            assert not (root / "escape.lean").exists()
            controls.append(kind + " source member rejected before extraction")
    print(json.dumps({"status": "PASS", "scope": "offline input and staging controls only",
                      "source_modules_per_role": len(originals), "dependency_pins": len(recipe["packages"]),
                      "controls": controls, "build": "NOT_RUN", "six_checkers": "NOT_RUN",
                      "scratch": "only this check's temporary directories removed"}, indent=2))


if __name__ == "__main__":
    main()
