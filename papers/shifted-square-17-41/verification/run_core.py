#!/usr/bin/env python3
"""Replay the imported Paper I core; this is not the final article/export gate.

Reuse the historical bounded process runner without its private-history gate.
The mathematical checks remain the existing GP, Python and Lean programs.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
from datetime import UTC, datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ENTRY = "Erdos364/DicksonLucas/ShiftedSquarePropagation.lean"
AUDIT = "papers/shifted-square-17-41/verification/PaperTheoremAxiomAudit.lean"
LEGACY = "papers/shifted-square-17-41/evidence/reproduce.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def checked_bytes(root: Path, relative: str) -> bytes:
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts, "unsafe source path")
    current = root
    for part in path.parts:
        current /= part
        require(not current.is_symlink(), f"symlink source: {relative}")
    require(current.is_file(), f"missing source: {relative}")
    require(current.stat().st_size <= 10 * 1024 * 1024, f"oversized source: {relative}")
    return current.read_bytes()


def source_inventory(root: Path) -> dict[str, str]:
    manifest_path = "papers/shifted-square-17-41/verification/imports.json"
    manifest = json.loads(checked_bytes(root, manifest_path))
    hashes: dict[str, str] = {}
    for item in manifest["sources"]:
        path = item["path"]
        require(path not in hashes, f"duplicate source: {path}")
        digest = hashlib.sha256(checked_bytes(root, path)).hexdigest()
        require(digest == item["sha256"], f"source hash mismatch: {path}")
        hashes[path] = digest
    visited: set[str] = set()

    def visit(path: str) -> None:
        if path in visited:
            return
        require(path in hashes, f"undeclared Lean dependency: {path}")
        visited.add(path)
        source = checked_bytes(root, path).decode()
        for line in source.splitlines():
            if line.startswith("import "):
                for module in line.partition("--")[0].split()[1:]:
                    if module.startswith("Erdos364."):
                        visit(module.replace(".", "/") + ".lean")
                    else:
                        require(
                            module.startswith("Mathlib."),
                            f"unexpected import: {module}",
                        )

    visit(ENTRY)
    listed = {p for p in hashes if p.startswith("Erdos364/") and p.endswith(".lean")}
    require(visited == listed, "Lean dependency closure differs from import map")
    for path in (manifest_path, "papers/shifted-square-17-41/verification/run_core.py"):
        hashes[path] = hashlib.sha256(checked_bytes(root, path)).hexdigest()
    return hashes


def validate_axioms(output: str, expected: set[str]) -> None:
    rows = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", output, re.DOTALL)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", output)
    parsed: dict[str, set[str]] = {}
    for name, body in rows + [(name, "") for name in empty]:
        require(name not in parsed, f"duplicate axiom row: {name}")
        parsed[name] = {s.strip() for s in body.split(",") if s.strip()}
    require(set(parsed) == expected, "axiom declaration inventory mismatch")
    for name, axioms in parsed.items():
        require(axioms <= ALLOWED_AXIOMS, f"unapproved axiom for {name}: {axioms}")


def clean_environment() -> dict[str, str]:
    # Deliberately omit PYTHONPATH, PYTHONHOME, LEAN_PATH and Lake overrides.
    env = {k: os.environ[k] for k in ("PATH", "HOME", "TMPDIR", "ELAN_HOME") if k in os.environ}
    env.update(
        LC_ALL="C",
        LANG="C",
        TZ="UTC",
        PYTHONDONTWRITEBYTECODE="1",
        PYTHONHASHSEED="0",
        GIT_CONFIG_NOSYSTEM="1",
    )
    return env


def load_runner():
    spec = importlib.util.spec_from_file_location("paper1_historical_runner", ROOT / LEGACY)
    require(spec is not None and spec.loader is not None, "missing bounded runner")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.command_environment = clean_environment
    return module


def normalise(value: bytes) -> str:
    text = value.decode("utf-8", errors="replace").replace(str(ROOT), "<SOURCE_ROOT>")
    home = os.environ.get("HOME")
    return text.replace(home, "<HOME>") if home else text


def commands() -> list[tuple[str, list[str], str, int]]:
    base = "experiments/sm2_four_translate/interpolation/"
    verify = "papers/shifted-square-17-41/verification/"
    return [
        (
            "gp17",
            ["gp", "-q", "-f", "experiments/sm2_outer_seventeen/outer17_verify.gp"],
            "OUTER17_CERTIFICATE_OK",
            120,
        ),
        (
            "gp41",
            ["gp", "-q", "-f", base + "outer41_verify.gp"],
            "OUTER41_CERTIFICATE_OK",
            120,
        ),
        (
            "independent-gp",
            ["gp", "-q", "-f", verify + "replay/independent_fixed_fields.gp"],
            "PAPER1_FIXED_FIELD_REPLAY_OK",
            120,
        ),
        (
            "jacobi-block",
            [sys.executable, "-B", base + "outer41_jacobi_block.py", "--self-test"],
            "OUTER41_JACOBI_BLOCK_OK",
            120,
        ),
        (
            "jacobi-certificate",
            [
                sys.executable,
                "-B",
                base + "outer41_jacobi_certificate.py",
                "--self-test",
            ],
            "OUTER41_JACOBI_CERTIFICATE_OK",
            120,
        ),
        (
            "jacobi-telescope",
            [sys.executable, "-B", base + "outer41_jacobi_telescope.py", "--self-test"],
            "OUTER41_JACOBI_LOCAL_OK",
            120,
        ),
        (
            "independent-finite",
            [sys.executable, "-B", verify + "replay/independent_finite.py"],
            "PAPER1_INDEPENDENT_FINITE_OK",
            120,
        ),
        (
            "propagation",
            [sys.executable, "-B", "experiments/shifted_square_propagation/replay.py"],
            "SHIFTED_SQUARE_PROPAGATION_OK",
            120,
        ),
        (
            "lean-build",
            [
                "lake",
                "--no-cache",
                "build",
                "Erdos364.DicksonLucas.ShiftedSquarePropagation",
            ],
            "lean",
            1800,
        ),
        ("axioms", ["lake", "--no-cache", "env", "lean", AUDIT], "axioms", 120),
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path, required=True, help="new directory for fresh records"
    )
    args = parser.parse_args()
    hashes = source_inventory(ROOT)
    runner = load_runner()
    args.output.mkdir(parents=True, exist_ok=False)
    identity = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    (args.output / "sources.json").write_text(json.dumps(hashes, indent=2, sort_keys=True) + "\n")
    expected = set(re.findall(r"^#print axioms (\S+)", (ROOT / AUDIT).read_text(), re.MULTILINE))
    environment = {
        "timestamp_utc": datetime.now(UTC).isoformat(),
        "source_sha256": identity,
    }
    for name, argv in (
        ("python", [sys.executable, "--version"]),
        ("gp", ["gp", "--version-short"]),
        ("lean", ["lean", "--version"]),
        ("lake", ["lake", "--version"]),
    ):
        rc, out, err = runner.run_bounded_process(argv, timeout=20, maximum=262144, context=name)
        require(rc == 0, f"version probe failed: {name}")
        environment[name] = normalise(out + err).strip()
    (args.output / "environment.json").write_text(json.dumps(environment, indent=2) + "\n")
    results = []
    for name, argv, oracle, timeout in commands():
        record = {
            "command": name,
            "argv": [normalise(s.encode()) for s in argv],
            "source_sha256": identity,
            "status": "FAIL",
        }
        try:
            rc, out, err = runner.run_bounded_process(
                argv, timeout=timeout, maximum=10 * 1024 * 1024, context=name
            )
            record.update(exit_code=rc, stdout=normalise(out), stderr=normalise(err))
            require(rc == 0, f"command failed: {name}")
            output = record["stdout"] + "\n" + record["stderr"]
            require(
                re.search(r"(^|\n).*error:", output, re.IGNORECASE) is None,
                f"error diagnostic: {name}",
            )
            if oracle == "axioms":
                validate_axioms(output, expected)
            elif oracle != "lean":
                require(output.count(oracle) == 1, f"success marker mismatch: {name}")
            record["status"] = "PASS"
        except (ValueError, runner.EvidenceError) as error:
            record["error"] = str(error)
        (args.output / (name + ".json")).write_text(json.dumps(record, indent=2) + "\n")
        results.append({"command": name, "status": record["status"]})
        print(name, record["status"], flush=True)
    require(source_inventory(ROOT) == hashes, "sources changed during verification")
    (args.output / "summary.json").write_text(json.dumps(results, indent=2) + "\n")
    return 0 if all(r["status"] == "PASS" for r in results) else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as error:
        print(f"PAPER1_CORE_FAIL: {error}", file=sys.stderr)
        raise SystemExit(1) from None
