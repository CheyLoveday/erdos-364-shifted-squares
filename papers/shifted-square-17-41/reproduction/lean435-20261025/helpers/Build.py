"""Trusted multi-module build/export driver; runs only in the isolated builder."""

import json
import os
import subprocess
import sys
from pathlib import Path

PRIMITIVES = (
    "Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble "
    "Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat "
    "List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
).split()


def main(args):
    if len(args) not in (1, 2) or args[0] not in ("reference", "positive"):
        raise ValueError("Unknown build role")
    case = args[0]
    mode = args[1] if len(args) == 2 else "all"
    if mode not in {"all", "inventory", "export"}:
        raise ValueError("Unknown producer phase")
    config = json.loads(Path("/inputs/project-config.json").read_bytes())
    root = "/inputs/proofs/" + case
    command = [
        "/opt/lean/bin/lake",
        "--no-cache",
        "--fail-fast",
        "--packages=/inputs/overrides.json",
        "-d",
        root,
        "--file=" + root + "/lakefile.toml",
    ]
    if mode == "all":
        code = subprocess.run(
            [*command, "build", *("+" + n + ":olean" for n in config["root_modules"])],
            stdin=subprocess.DEVNULL,
        ).returncode
        if code:
            return code
    env = dict(os.environ)
    env["LEAN_PATH"] = ":".join(
        [
            "/work/build/lib/lean",
            *(
                "/inputs/packages/" + n + "/.lake/build/lib/lean"
                for n in config["environment_packages"]
            ),
        ]
    )
    aggregate = "_FormalCodeProjectRoot"
    if mode != "export":
        code = subprocess.run(
            [
                "/opt/lean/bin/lean",
                "-j1",
                "-s16384",
                "-M0",
                "--root=" + root,
                "-o",
                "/work/build/lib/lean/" + aggregate + ".olean",
                root + "/" + aggregate + ".lean",
            ],
            env=env,
            stdin=subprocess.DEVNULL,
        ).returncode
        if code:
            return code
        with Path("/work/inventory.json").open("xb") as output:
            code = subprocess.run(
                ["/opt/lean/bin/lean", "-j1", "-s16384", "-M0", "--run", "/inputs/Inventory.lean"],
                env=env,
                stdout=output,
                stdin=subprocess.DEVNULL,
            ).returncode
        if code:
            return code
    if mode == "inventory":
        return 0
    inventory = json.loads(Path("/work/inventory.json").read_bytes())
    if inventory.get("schema_version") != "LogicalInventoryV2":
        raise ValueError("Fresh logical declaration inventory required before export")
    roots = sorted(
        {n for row in inventory["modules"] for n in row["declarations"]}
        | set(config["target_declarations"])
        | set(config["protected_definitions"])
    )
    # Split exports use a separate bounded disk sink, never the compiled tmpfs.
    # Historical compound producers keep their original path for evidence replay.
    destination = "/output/export.ndjson" if mode == "export" else "/work/export.ndjson"
    with Path(destination).open("xb") as output:
        return subprocess.run(
            ["/opt/lean/bin/leanexport", aggregate, "--", *roots, *PRIMITIVES],
            env=env,
            stdout=output,
            stdin=subprocess.DEVNULL,
        ).returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
