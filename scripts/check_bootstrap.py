"""Fail-closed checks for the Issue 164 Tranche 0 bootstrap."""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUIRED_FILES = (
    "README.md",
    "AUTHORITY.md",
    "TRUST.md",
    "CITATION.cff",
    ".gitattributes",
    ".gitignore",
    "Makefile",
    "evidence/PROMOTION_LEDGER.md",
    "evidence/RELEASE_GATES.md",
    "evidence/hashes/SHA256SUMS",
    "docs/SOFTWARE_REQUIREMENTS_FROM_PAPER1.md",
)
REQUIRED_DIRECTORIES = (
    "paper/article",
    "paper/article/figures",
    "paper/supplement",
    "paper/supplement/sections",
    "paper/supplement/figures",
    "proofs/human",
    "formal/lean/Evidence",
    "certificates/common",
    "certificates/field-17",
    "certificates/field-41",
    "certificates/propagation",
    "computations/gp/field-17",
    "computations/gp/field-41",
    "computations/python/field-17",
    "computations/python/field-41",
    "computations/python/propagation",
    "evidence/hashes",
    "scripts",
    ".github/workflows",
)
LEDGER_COLUMNS = (
    "Object ID",
    "Evidence role",
    "LAB source repository",
    "LAB source path",
    "LAB source commit",
    "LAB blob/SHA-256",
    "Companion destination",
    "Destination SHA-256",
    "Manuscript use",
    "Dependency IDs",
    "Transformation",
    "Semantic review",
    "Rights status",
    "Verification command",
    "Review status",
    "Notes",
)
REQUIREMENTS_COLUMNS = (
    "Task performed manually",
    "What was repetitive, fragile, or error-prone",
    "Invariant checked",
    "Actual input/output shape",
    "Minimum future capability",
    "Why automation would or would not help",
)
SLASH = "/"
URI_SEPARATOR = ":" + SLASH + SLASH
FORBIDDEN_TEXT = re.compile(
    "(?:"
    + "|".join(
        re.escape(value)
        for value in (
            "file" + URI_SEPARATOR,
            SLASH + "Users" + SLASH,
            SLASH + "private" + SLASH,
            "s3" + URI_SEPARATOR,
            "gs" + URI_SEPARATOR,
            "az" + URI_SEPARATOR,
            "ghp" + "_",
            "github" + "_pat" + "_",
        )
    )
    + r"|-----BEGIN [A-Z ]*PRIVATE KEY-----)",
    re.IGNORECASE,
)
FORBIDDEN_SUFFIXES = {".tex", ".bib", ".lean", ".gp"}
FORBIDDEN_ROOT_NAMES = {"LICENSE", "LICENCE", "COPYING", ".gitmodules"}


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)


def text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return ""


def visible_files() -> list[Path]:
    result: list[Path] = []
    for directory, directories, filenames in os.walk(ROOT, followlinks=False):
        current = Path(directory)
        for item in list(directories):
            candidate = current / item
            if candidate.is_symlink():
                result.append(candidate)
                directories.remove(item)
        directories[:] = [
            item
            for item in directories
            if item not in {".git", "build", "staging", ".stage-arxiv"}
        ]
        for filename in filenames:
            result.append(current / filename)
    return result


def main() -> int:
    errors = 0
    for relative in REQUIRED_FILES:
        if not (ROOT / relative).is_file():
            fail(f"missing required file: {relative}")
            errors += 1
    for relative in REQUIRED_DIRECTORIES:
        if not (ROOT / relative).is_dir():
            fail(f"missing required directory: {relative}")
            errors += 1
    for name in FORBIDDEN_ROOT_NAMES:
        if (ROOT / name).exists():
            fail(f"forbidden bootstrap path present: {name}")
            errors += 1

    ledger = text(ROOT / "evidence/PROMOTION_LEDGER.md")
    for column in LEDGER_COLUMNS:
        if column not in ledger:
            fail(f"promotion ledger lacks column: {column}")
            errors += 1
    requirement_log = text(ROOT / "docs/SOFTWARE_REQUIREMENTS_FROM_PAPER1.md")
    for column in REQUIREMENTS_COLUMNS:
        if column not in requirement_log:
            fail(f"software requirements log lacks column: {column}")
            errors += 1

    for path in visible_files():
        relative = path.relative_to(ROOT)
        if path.is_symlink():
            fail(f"symlink is not permitted in bootstrap: {relative}")
            errors += 1
            continue
        if path.name in FORBIDDEN_ROOT_NAMES:
            fail(f"forbidden bootstrap path present: {relative}")
            errors += 1
        if path.suffix in FORBIDDEN_SUFFIXES:
            fail(f"Tranche 0 must not contain substantive source: {relative}")
            errors += 1
        data = path.read_bytes()
        if len(data) > 1_000_000:
            fail(f"bootstrap file exceeds one MiB: {relative}")
            errors += 1
            continue
        if data.startswith(b"version https://git-lfs.github.com/spec/v1"):
            fail(f"Git LFS pointer is not permitted: {relative}")
            errors += 1
        rendered = data.decode("utf-8", errors="replace")
        if FORBIDDEN_TEXT.search(rendered):
            fail(f"private path, URI, or credential-like text: {relative}")
            errors += 1

    if errors:
        return 1
    print("Tranche 0 bootstrap checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
