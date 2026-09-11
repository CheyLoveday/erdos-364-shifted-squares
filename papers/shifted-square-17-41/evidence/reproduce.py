#!/usr/bin/env python3
"""Fail-closed reproduction gate for the Paper I evidence freeze."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import platform
import re
import selectors
import signal
import stat
import subprocess
import sys
import tempfile
import time
import tomllib
from collections.abc import Callable, Iterable, Mapping
from pathlib import Path, PurePosixPath
from typing import Any

EVIDENCE_ROOT = Path(__file__).resolve().parent
REPOSITORY_ROOT = EVIDENCE_ROOT.parents[2]
MANIFEST_PATH = EVIDENCE_ROOT / "MANIFEST.toml"
HASH_PATH = EVIDENCE_ROOT / "hashes" / "SHA256SUMS"
SCHEMA = "erdos364.paper1-evidence.v1"
RECORD_SCHEMA = "erdos364.paper1-command-record.v1"
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
MANIFEST_MAX_BYTES = 256 * 1024
PROBE_OUTPUT_MAX_BYTES = 256 * 1024
PROCESS_TERMINATION_GRACE_SECONDS = 0.1

PRIVATE_PATTERNS = (
    re.compile("/" + "Users" + "/"),
    re.compile("/" + "private" + "/"),
    re.compile("file" + "://", re.IGNORECASE),
    re.compile(r"(?:" + "s3|gs|az" + r")://", re.IGNORECASE),
    re.compile(r"blob\.core\.windows\.net", re.IGNORECASE),
)
SECRET_PATTERNS = (
    re.compile(r"ghp_[A-Za-z0-9]{20,}"),
    re.compile(r"sk-[A-Za-z0-9]{20,}"),
    re.compile(r"AKIA[0-9A-Z]{16}"),
    re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----"),
)

EXPECTED_BUDGETS = {
    "total_seconds": 3600,
    "command_seconds": 600,
    "build_seconds": 1200,
    "max_record_bytes": 10485760,
    "max_input_bytes": 10485760,
}
EXPECTED_TOOLS = {
    "lean": "4.31.0",
    "lean_commit": "68218e876d2a38b1985b8590fff244a83c321783",
    "lake": "5.0.0",
    "mathlib_commit": "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f",
    "pari_gp": "2.17.3",
    "python": "3.13.12",
    "platform": "Darwin-25.6.0-arm64",
}
EXPECTED_EVIDENCE_ROLES = [
    "FORMAL_DECLARATION",
    "HUMAN_DERIVED_COROLLARY",
    "EXACT_GP_CERTIFICATE",
    "INDEPENDENT_GP_REPLAY",
    "EXACT_JSON_REPLAY",
    "REGRESSION_REPLAY",
    "SOURCE_ADAPTER",
]
EXPECTED_PROHIBITED_CLAIMS = [
    "canonical acceptance",
    "Ledger admission",
    "public release",
    "whole OuterLarge closure",
    "whole RankDefect closure",
    "atomic closure",
    "full leaf closure",
    "uniform prime theorem",
    "terminal status above 1/4",
]
EXPECTED_DETECTORS = {
    17: [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1],
    41: [
        -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
        3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
        -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5,
    ],
}
EXPECTED_REFERENCE_SYMBOLS = {
    17: [-1, 1],
    41: [1, -1, -1, -1, 1],
}
EXPECTED_FINITE_OBJECT_IDS = {
    "outer17-polynomial-detector",
    "outer41-polynomial-detector",
    "reference-values-factorizations",
    "discriminants-signatures",
    "dyadic-decomposition-valuations",
    "reference-hilbert-products",
    "outer17-prs-chain",
    "fixed41-block-data",
    "fixed41-certificate-data",
    "fixed41-telescope-data",
    "exceptional-specialisations",
    "ss41-a2-boundary",
    "propagation-finite-identity",
}
EXPECTED_STATUS_DISPOSITIONS = {
    "BLOCKED_REVIEW_LINEAGE",
    "EXCLUDED_OPEN_RESEARCH",
    "EXCLUDED_SUPERSEDED",
}
EXPECTED_HOSTILE_MUTATIONS = [
    ("M01", "degree-17 coefficient", "degree-17-source"),
    ("M02", "degree-41 coefficient", "degree-41-source"),
    ("M03", "detector coefficient", "detector-at-four"),
    (
        "M04",
        "replace outer41 reference_factors[1] value 1373 with 1381",
        "outer41-reference-factor-product",
    ),
    ("M05", "dyadic ramification index", "dyadic-degree-sum"),
    ("M06", "denominator valuation", "dyadic-valuation-row"),
    ("M07", "reference Hilbert symbol", "hilbert-product"),
    ("M08", "fixed-17 pseudo-remainder sign", "fixed-17-source-digest"),
    (
        "M09",
        "replace outer41 factor_thirteen_value 13 with 1",
        "factor-thirteen-local-row",
    ),
    ("M10", "selected-41 adapter divisibility", "selected-41-signature"),
    ("M11", "theorem prose quantifier", "theorem-prose-crosswalk"),
    ("M12", "expected output hash", "payload-result-digest"),
]

THEOREM_AXIOM_NAMES = [
    "Erdos364.no_sm2LucasReal_seventeen_square_of_mod_eight_two",
    "Erdos364.noSm2OuterSeventeenBlocks",
    "Erdos364.ss41_shiftedSquare_impossible",
    "Erdos364.no_outerLarge_selected_fortyOne",
    "Erdos364.no_rankDefect_selected_fortyOne",
    "Erdos364.sm2LucasReal_mod_four_two_of_odd",
    "Erdos364.sm2LucasReal_mod_eight_six_of_index_mod_four_one",
    "Erdos364.no_sm2LucasReal_seventeen_square_of_mod_four_two",
    "Erdos364.no_sm2LucasReal_fortyOne_square_of_mod_four_two",
    "Erdos364.sm2LucasReal_mul_of_odd_right",
    "Erdos364.no_sm2LucasReal_shiftedSquare_of_odd_index_factor",
    "Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_index_factor",
]
SUPPORT_AXIOM_NAMES = [
    "Erdos364.sm2UpperNegativeUnit_pow_re",
    "Erdos364.Sm2LowerSquareUpperSourceGenerator.root_real_mod_eight",
    "Erdos364.sm2LowerSquareSource_iff_exists_generatorResidual",
    "Erdos364.pellRank_dvd_kernel",
]
ALL_AXIOM_NAMES = THEOREM_AXIOM_NAMES + SUPPORT_AXIOM_NAMES

EVIDENCE_BASE_FILES = {
    "MANIFEST.toml",
    "STATUS_AUDIT.md",
    "THEOREM_CROSSWALK.md",
    "CLAIM_CEILING.md",
    "TRUST.md",
    "REPRODUCE.md",
    "PUBLIC_RIGHTS_PRIVACY.md",
    "reviews/review-lineage.md",
    "reproduce.py",
    "reproduce.sh",
    "lean/PaperTheoremAxiomAudit.lean",
    "replay/independent_finite.py",
    "replay/independent_fixed_fields.gp",
}
ASSURANCE_RECORDS = {
    "assurance/hostile-output.txt",
    "assurance/integrity-output.txt",
}
EXPECTED_COMMANDS = {
    "focused-outer17": (
        ["lake", "env", "lean", "Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean"],
        "lean/focused-outer17-output.txt",
        600,
        "lean-success",
    ),
    "focused-outer41": (
        ["lake", "env", "lean", "Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean"],
        "lean/focused-outer41-output.txt",
        600,
        "lean-success",
    ),
    "focused-propagation": (
        ["lake", "env", "lean", "Erdos364/DicksonLucas/ShiftedSquarePropagation.lean"],
        "lean/focused-propagation-output.txt",
        600,
        "lean-success",
    ),
    "root-build": (
        ["lake", "env", "lean", "Erdos364.lean"],
        "lean/root-build-output.txt",
        600,
        "lean-success",
    ),
    "full-build": (
        ["lake", "build", "Erdos364"],
        "lean/full-build-output.txt",
        1200,
        "lake-success",
    ),
    "axiom-audit": (
        [
            "lake",
            "env",
            "lean",
            "papers/shifted-square-17-41/evidence/lean/PaperTheoremAxiomAudit.lean",
        ],
        "lean/axiom-output.txt",
        600,
        "axiom-exact",
    ),
    "pari-outer17": (
        ["gp", "-q", "-f", "experiments/sm2_outer_seventeen/outer17_verify.gp"],
        "pari/outer17-output.txt",
        600,
        "OUTER17_CERTIFICATE_OK",
    ),
    "pari-outer41": (
        ["gp", "-q", "-f", "experiments/sm2_four_translate/interpolation/outer41_verify.gp"],
        "pari/outer41-output.txt",
        600,
        "OUTER41_CERTIFICATE_OK",
    ),
    "pari-independent": (
        [
            "gp",
            "-q",
            "-f",
            "papers/shifted-square-17-41/evidence/replay/independent_fixed_fields.gp",
        ],
        "pari/independent-output.txt",
        600,
        "PAPER1_FIXED_FIELD_REPLAY_OK",
    ),
    "jacobi-block": (
        [
            "python3",
            "-B",
            "experiments/sm2_four_translate/interpolation/outer41_jacobi_block.py",
            "--self-test",
        ],
        "replays/jacobi-block-output.txt",
        600,
        "OUTER41_JACOBI_BLOCK_OK",
    ),
    "jacobi-certificate": (
        [
            "python3",
            "-B",
            "experiments/sm2_four_translate/interpolation/outer41_jacobi_certificate.py",
            "--self-test",
        ],
        "replays/jacobi-certificate-output.txt",
        600,
        "OUTER41_JACOBI_CERTIFICATE_OK",
    ),
    "jacobi-telescope": (
        [
            "python3",
            "-B",
            "experiments/sm2_four_translate/interpolation/outer41_jacobi_telescope.py",
            "--self-test",
        ],
        "replays/jacobi-telescope-output.txt",
        600,
        "OUTER41_JACOBI_LOCAL_OK",
    ),
    "independent-finite": (
        [
            "python3",
            "-B",
            "papers/shifted-square-17-41/evidence/replay/independent_finite.py",
        ],
        "replays/independent-finite-output.txt",
        600,
        "PAPER1_INDEPENDENT_FINITE_OK",
    ),
    "propagation": (
        ["python3", "-B", "experiments/shifted_square_propagation/replay.py"],
        "replays/propagation-output.txt",
        600,
        "SHIFTED_SQUARE_PROPAGATION_OK",
    ),
}
EXPECTED_RECORDS = {command_id: values[1] for command_id, values in EXPECTED_COMMANDS.items()}

EXPECTED_SOURCE_ROLES = {
    "lean-toolchain": "toolchain-pin",
    "lake-manifest.json": "dependency-pin",
    "lakefile.toml": "build-input",
    "Erdos364.lean": "root-export",
    "Erdos364/DicksonLucas/ShiftedSquarePropagation.lean": "maintained-lean",
    "Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean": "maintained-lean",
    "Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean": "maintained-lean",
    "Erdos364/SquareMiddle/Sm2LowerSquareGeneratorRank.lean": "lean-support",
    "Erdos364/SquareMiddle/Sm2LowerSquareUpperNormOneOrbit.lean": "lean-support",
    "Erdos364/SquareMiddle/Sm2LowerSquareUpperSourceGenerator.lean": "lean-support",
    "Erdos364/SquareMiddle/PellDivisibilityRank.lean": "lean-support",
    "experiments/sm2_outer_seventeen/outer17_verify.gp": "exact-gp-certificate",
    "experiments/sm2_four_translate/interpolation/outer41_verify.gp": "exact-gp-certificate",
    "experiments/sm2_four_translate/interpolation/outer41_jacobi_block.py": "exact-json-replay",
    "experiments/sm2_four_translate/interpolation/outer41_jacobi_block.json": "exact-json-payload",
    "experiments/sm2_four_translate/interpolation/outer41_jacobi_certificate.py": "exact-json-replay",
    "experiments/sm2_four_translate/interpolation/outer41_jacobi_certificate.json": "exact-json-payload",
    "experiments/sm2_four_translate/interpolation/outer41_jacobi_telescope.py": "exact-json-replay",
    "experiments/sm2_four_translate/interpolation/outer41_jacobi_telescope.json": "exact-json-payload",
    "experiments/shifted_square_propagation/replay.py": "regression-replay",
    "experiments/shifted_square_propagation/expected.json": "regression-payload",
    "papers/shifted-square-17-41/hilbert-obstruction-lamport.md": "certified-human-proof",
    "papers/shifted-square-17-41/fixed-field-obligation-table.md": "human-crosswalk",
    "papers/shifted-square-17-41/hilbert-jacobi-crosswalk.md": "human-crosswalk",
    "papers/shifted-square-17-41/source-theorem.md": "certified-human-proof",
    "papers/shifted-square-17-41/theorem-formal-crosswalk.md": "theorem-crosswalk",
    "problems/square-middle/sm2-lower-square/outer-seventeen-certificate.md": "certified-human-proof",
    "problems/square-middle/sm2-lower-square/outer-forty-one-certificate.md": "certified-human-proof",
    "problems/square-middle/sm2-lower-square/outer-forty-one-jacobi-certificate.md": "certified-human-proof",
    "problems/square-middle/sm2-lower-square/shifted-square-propagation-lamport.md": "certified-human-proof",
    "problems/square-middle/sm2-lower-square/problem.md": "current-status-authority",
}

PROVED_STATUSES = ("MAINTAINED_LEAN", "CERTIFIED_HUMAN_PROOF", "PAPER_CANDIDATE")
EXPECTED_THEOREM_STATUS_ROLES = {
    "Erdos364.no_sm2LucasReal_seventeen_square_of_mod_eight_two": (
        ("MAINTAINED_LEAN", "CERTIFIED_HUMAN_PROOF", "EXACT_GP_REPLAY", "PAPER_CANDIDATE"),
        "FORMAL_DECLARATION",
    ),
    "Erdos364.noSm2OuterSeventeenBlocks": (
        ("MAINTAINED_LEAN", "PAPER_CANDIDATE"),
        "SOURCE_ADAPTER",
    ),
    "Erdos364.ss41_shiftedSquare_impossible": (
        ("MAINTAINED_LEAN", "CERTIFIED_HUMAN_PROOF", "EXACT_GP_REPLAY", "PAPER_CANDIDATE"),
        "FORMAL_DECLARATION",
    ),
    "Erdos364.no_outerLarge_selected_fortyOne": (
        ("MAINTAINED_LEAN", "PAPER_CANDIDATE"),
        "SOURCE_ADAPTER",
    ),
    "Erdos364.no_rankDefect_selected_fortyOne": (
        ("MAINTAINED_LEAN", "PAPER_CANDIDATE"),
        "SOURCE_ADAPTER",
    ),
    "Erdos364.sm2LucasReal_mod_four_two_of_odd": (PROVED_STATUSES, "FORMAL_DECLARATION"),
    "Erdos364.sm2LucasReal_mod_eight_six_of_index_mod_four_one": (
        PROVED_STATUSES,
        "FORMAL_DECLARATION",
    ),
    "Erdos364.no_sm2LucasReal_seventeen_square_of_mod_four_two": (
        PROVED_STATUSES,
        "FORMAL_DECLARATION",
    ),
    "Erdos364.no_sm2LucasReal_fortyOne_square_of_mod_four_two": (
        PROVED_STATUSES,
        "FORMAL_DECLARATION",
    ),
    "Erdos364.sm2LucasReal_mul_of_odd_right": (PROVED_STATUSES, "FORMAL_DECLARATION"),
    "Erdos364.no_sm2LucasReal_shiftedSquare_of_odd_index_factor": (
        PROVED_STATUSES,
        "FORMAL_DECLARATION",
    ),
    "Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_index_factor": (
        PROVED_STATUSES,
        "FORMAL_DECLARATION",
    ),
    "PaperI.complete_source_full_index_corollary": (
        ("CERTIFIED_HUMAN_PROOF", "PAPER_CANDIDATE"),
        "HUMAN_DERIVED_COROLLARY",
    ),
}

EXPECTED_STATUS_OBJECTS = {
    "paper1-maintained-formal-surface": (
        "papers/shifted-square-17-41/theorem-formal-crosswalk.md",
        ("MAINTAINED_LEAN", "CERTIFIED_HUMAN_PROOF", "EXACT_GP_REPLAY", "PAPER_CANDIDATE"),
        "BLOCKED_REVIEW_LINEAGE",
        "whole current crosswalk",
    ),
    "remaining-three-terminals": (
        "problems/square-middle/sm2-lower-square/problem.md",
        ("OPEN_RESEARCH",),
        "EXCLUDED_OPEN_RESEARCH",
        "remaining three terminal statements only",
    ),
    "historical-outer41-status": (
        "problems/square-middle/sm2-lower-square/outer-forty-one-certificate.md",
        ("SUPERSEDED_STATUS_TEXT",),
        "EXCLUDED_SUPERSEDED",
        "draft-era status paragraphs explicitly superseded by the later fixed theorem",
    ),
    "historical-jacobi-status": (
        "problems/square-middle/sm2-lower-square/outer-forty-one-jacobi-certificate.md",
        ("SUPERSEDED_STATUS_TEXT",),
        "EXCLUDED_SUPERSEDED",
        "early global-open and old issue-ownership passages only",
    ),
}


class EvidenceError(RuntimeError):
    """A fail-closed evidence validation failure."""


def require(condition: bool, message: str) -> None:
    """Raise a stable evidence error when a contract condition is false."""

    if not condition:
        raise EvidenceError(message)


def expect_keys(value: Mapping[str, Any], keys: set[str], context: str) -> None:
    """Reject missing and unknown keys in a manifest object."""

    actual = set(value)
    require(actual == keys, f"{context} keys: expected {sorted(keys)}, got {sorted(actual)}")


def require_nonempty_text(value: object, context: str) -> str:
    """Require a single-line, nonempty metadata string."""

    require(isinstance(value, str) and bool(value.strip()), f"{context} must be nonempty text")
    require("\n" not in value and "\r" not in value, f"{context} must be single-line text")
    return value


def sha256_bytes(raw: bytes) -> str:
    """Return a lowercase SHA-256 digest."""

    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(value: object) -> bytes:
    """Return the repository's unique JSON encoding."""

    return (
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("ascii")
        + b"\n"
    )


def pretty_json_bytes(value: object) -> bytes:
    """Return the deterministic command-record JSON encoding."""

    return (json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n").encode("ascii")


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Decode a JSON object while rejecting duplicate keys."""

    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def relative_file(relative: str, *, must_exist: bool = True) -> Path:
    """Resolve a repository-relative regular file without path escape or symlinks."""

    pure = PurePosixPath(relative)
    require(not pure.is_absolute(), f"absolute path forbidden: {relative}")
    require(".." not in pure.parts and "." not in pure.parts, f"path traversal forbidden: {relative}")
    candidate = REPOSITORY_ROOT.joinpath(*pure.parts)
    current = REPOSITORY_ROOT
    for part in pure.parts:
        current = current / part
        require(not current.is_symlink(), f"symlink forbidden in evidence input: {relative}")
    if must_exist:
        require(candidate.is_file(), f"missing regular file: {relative}")
        resolved = candidate.resolve(strict=True)
        require(
            resolved.is_relative_to(REPOSITORY_ROOT.resolve(strict=True)),
            f"path escapes repository: {relative}",
        )
    return candidate


def read_path_bounded(path: Path, maximum: int, label: str) -> bytes:
    """Read at most ``maximum`` bytes from one regular, non-symlink file."""

    require(isinstance(maximum, int) and maximum >= 0, f"invalid byte budget: {label}")
    flags = os.O_RDONLY
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise EvidenceError(f"cannot open bounded input: {label}") from error
    try:
        metadata = os.fstat(descriptor)
        require(stat.S_ISREG(metadata.st_mode), f"input is not a regular file: {label}")
        require(metadata.st_size <= maximum, f"input exceeds byte budget: {label}")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(64 * 1024, maximum - total + 1))
            if not chunk:
                break
            total += len(chunk)
            require(total <= maximum, f"input exceeds byte budget: {label}")
            chunks.append(chunk)
        return b"".join(chunks)
    except OSError as error:
        raise EvidenceError(f"cannot read bounded input: {label}") from error
    finally:
        os.close(descriptor)


def read_bounded(relative: str, maximum: int) -> bytes:
    """Read a bounded regular repository file."""

    path = relative_file(relative)
    return read_path_bounded(path, maximum, relative)


def read_text(relative: str, maximum: int) -> str:
    """Read strict UTF-8 text under the input byte limit."""

    raw = read_bounded(relative, maximum)
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"non-UTF-8 input: {relative}") from error


def load_manifest() -> dict[str, Any]:
    """Load and structurally validate the one manifest."""

    raw = read_path_bounded(MANIFEST_PATH, MANIFEST_MAX_BYTES, "MANIFEST.toml")
    try:
        value = tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise EvidenceError(f"cannot decode MANIFEST.toml: {error}") from error
    expect_keys(
        value,
        {
            "schema",
            "bundle_id",
            "issue",
            "source_commit",
            "source_tree",
            "maintained_internal_terminal_count",
            "claim_ceiling",
            "status_vocabulary",
            "allowed_axioms",
            "evidence_roles",
            "prohibited_claims",
            "budgets",
            "tools",
            "finite",
            "finite_objects",
            "payloads",
            "theorems",
            "status_objects",
            "sources",
            "commands",
            "hostile_mutations",
        },
        "manifest",
    )
    require(value["schema"] == SCHEMA, "manifest schema mismatch")
    require(value["bundle_id"] == "paper1-shifted-square-17-41", "bundle id mismatch")
    require(value["issue"] == 122, "issue id mismatch")
    require(isinstance(value["source_commit"], str), "source commit must be text")
    require(HEX40.fullmatch(value["source_commit"]) is not None, "invalid source commit")
    require(HEX40.fullmatch(value["source_tree"]) is not None, "invalid source tree")
    require(
        value["maintained_internal_terminal_count"] == "1/4",
        "maintained internal terminal count changed",
    )
    require(value["claim_ceiling"] == "paper-candidate-evidence-only", "claim ceiling changed")
    require(
        value["status_vocabulary"]
        == [
            "MAINTAINED_LEAN",
            "CERTIFIED_HUMAN_PROOF",
            "EXACT_GP_REPLAY",
            "PAPER_CANDIDATE",
            "OPEN_RESEARCH",
            "SUPERSEDED_STATUS_TEXT",
        ],
        "status vocabulary mismatch",
    )
    require(
        value["allowed_axioms"] == ["propext", "Classical.choice", "Quot.sound"],
        "allowed axiom set changed",
    )
    require(value["evidence_roles"] == EXPECTED_EVIDENCE_ROLES, "evidence role vocabulary changed")
    require(
        value["prohibited_claims"] == EXPECTED_PROHIBITED_CLAIMS,
        "prohibited claim ceiling changed",
    )
    expect_keys(
        value["budgets"],
        {
            "total_seconds",
            "command_seconds",
            "build_seconds",
            "max_record_bytes",
            "max_input_bytes",
        },
        "budgets",
    )
    expect_keys(
        value["tools"],
        {"lean", "lean_commit", "lake", "mathlib_commit", "pari_gp", "python", "platform"},
        "tools",
    )
    require(value["budgets"] == EXPECTED_BUDGETS, "evidence budgets changed")
    require(value["tools"] == EXPECTED_TOOLS, "tool pin contract changed")
    require(HEX40.fullmatch(value["tools"]["lean_commit"]) is not None, "invalid Lean commit")
    require(HEX40.fullmatch(value["tools"]["mathlib_commit"]) is not None, "invalid mathlib commit")
    require(set(value["finite"]) == {"outer17", "outer41"}, "finite field keys changed")

    source_paths: set[str] = set()
    source_roles: dict[str, str] = {}
    source_digests: dict[str, str] = {}
    for index, source in enumerate(value["sources"]):
        expect_keys(source, {"path", "sha256", "role"}, f"sources[{index}]")
        require(source["path"] not in source_paths, f"duplicate source path: {source['path']}")
        source_paths.add(source["path"])
        source_roles[source["path"]] = source["role"]
        require(HEX64.fullmatch(source["sha256"]) is not None, f"invalid source digest: {source['path']}")
        source_digests[source["path"]] = source["sha256"]
    require(source_roles == EXPECTED_SOURCE_ROLES, "source path or role inventory changed")

    finite_object_ids: set[str] = set()
    require(isinstance(value["finite_objects"], list), "finite_objects must be an array")
    for index, finite_object in enumerate(value["finite_objects"]):
        expect_keys(
            finite_object,
            {
                "object_id",
                "meaning",
                "source_path",
                "source_function",
                "generator_command",
                "independent_replay_command",
                "expected_digest",
                "allowed_interpretation",
            },
            f"finite_objects[{index}]",
        )
        object_id = require_nonempty_text(
            finite_object["object_id"], f"finite_objects[{index}].object_id"
        )
        require(object_id not in finite_object_ids, f"duplicate finite object: {object_id}")
        finite_object_ids.add(object_id)
        for key in (
            "meaning",
            "source_path",
            "source_function",
            "generator_command",
            "independent_replay_command",
            "allowed_interpretation",
        ):
            require_nonempty_text(finite_object[key], f"finite_objects[{index}].{key}")
        require(
            finite_object["source_path"] in source_paths,
            f"finite object source is not manifest-listed: {object_id}",
        )
        require(
            isinstance(finite_object["expected_digest"], str)
            and HEX64.fullmatch(finite_object["expected_digest"]) is not None,
            f"invalid finite object digest: {object_id}",
        )
        require(
            finite_object["expected_digest"] == source_digests[finite_object["source_path"]],
            f"finite object digest does not bind its source: {object_id}",
        )
    require(
        finite_object_ids == EXPECTED_FINITE_OBJECT_IDS,
        "finite object inventory changed",
    )

    theorem_names: set[str] = set()
    vocabulary = set(value["status_vocabulary"])
    roles = set(value["evidence_roles"])
    for index, theorem in enumerate(value["theorems"]):
        expect_keys(
            theorem,
            {
                "name",
                "path",
                "statuses",
                "role",
                "required_fragments",
                "imports",
                "signature",
                "human_name",
                "source_object",
                "certificate_dependency",
                "paper_section",
            },
            f"theorems[{index}]",
        )
        require_nonempty_text(theorem["name"], f"theorems[{index}].name")
        require_nonempty_text(theorem["path"], f"theorems[{index}].path")
        require(theorem["path"] in source_paths, f"theorem path is not manifest-listed: {theorem['name']}")
        require(
            isinstance(theorem["imports"], list)
            and all(isinstance(item, str) and bool(item.strip()) for item in theorem["imports"])
            and len(theorem["imports"]) == len(set(theorem["imports"])),
            f"invalid theorem imports: {theorem['name']}",
        )
        for imported_module in theorem["imports"]:
            imported_path = imported_module.replace(".", "/") + ".lean"
            require(
                imported_path in source_paths,
                f"theorem import is not manifest-listed: {theorem['name']}",
            )
        for key in (
            "signature",
            "human_name",
            "source_object",
            "certificate_dependency",
            "paper_section",
        ):
            require_nonempty_text(theorem[key], f"theorems[{index}].{key}")
        require(
            isinstance(theorem["statuses"], list)
            and theorem["statuses"]
            and all(isinstance(item, str) for item in theorem["statuses"]),
            f"invalid theorem statuses: {theorem['name']}",
        )
        require(
            isinstance(theorem["required_fragments"], list)
            and theorem["required_fragments"]
            and all(isinstance(item, str) and bool(item.strip()) for item in theorem["required_fragments"]),
            f"invalid theorem signature fragments: {theorem['name']}",
        )
        require(theorem["name"] not in theorem_names, f"duplicate theorem: {theorem['name']}")
        theorem_names.add(theorem["name"])
        require(set(theorem["statuses"]) <= vocabulary, f"unknown status: {theorem['name']}")
        require(theorem["role"] in roles, f"unknown evidence role: {theorem['name']}")
        require(theorem["name"] in EXPECTED_THEOREM_STATUS_ROLES, "unknown theorem metadata row")
        expected_statuses, expected_role = EXPECTED_THEOREM_STATUS_ROLES[theorem["name"]]
        require(tuple(theorem["statuses"]) == expected_statuses, f"status drift: {theorem['name']}")
        require(theorem["role"] == expected_role, f"role drift: {theorem['name']}")
    require(
        theorem_names == set(THEOREM_AXIOM_NAMES) | {"PaperI.complete_source_full_index_corollary"},
        "theorem inventory is not exactly the Paper I inventory",
    )
    status_object_ids: set[str] = set()
    used_statuses = {status for theorem in value["theorems"] for status in theorem["statuses"]}
    used_dispositions: set[str] = set()
    for index, status_object in enumerate(value["status_objects"]):
        expect_keys(
            status_object,
            {"id", "path", "statuses", "disposition", "scope"},
            f"status_objects[{index}]",
        )
        require(status_object["id"] not in status_object_ids, "duplicate status object")
        status_object_ids.add(status_object["id"])
        require(set(status_object["statuses"]) <= vocabulary, "unknown status object vocabulary")
        require(
            status_object["disposition"] in EXPECTED_STATUS_DISPOSITIONS,
            "unknown status disposition vocabulary",
        )
        used_dispositions.add(status_object["disposition"])
        used_statuses.update(status_object["statuses"])
        require(status_object["id"] in EXPECTED_STATUS_OBJECTS, "unknown status object")
        expected_path, expected_statuses, expected_disposition, expected_scope = EXPECTED_STATUS_OBJECTS[
            status_object["id"]
        ]
        require(status_object["path"] == expected_path, "status object path drift")
        require(tuple(status_object["statuses"]) == expected_statuses, "status object status drift")
        require(status_object["disposition"] == expected_disposition, "status disposition drift")
        require(status_object["scope"] == expected_scope, "status scope drift")
    require(status_object_ids == set(EXPECTED_STATUS_OBJECTS), "status object inventory changed")
    require(used_statuses == vocabulary, "status vocabulary is not fully assigned")
    require(
        used_dispositions == EXPECTED_STATUS_DISPOSITIONS,
        "status disposition vocabulary is not fully assigned",
    )

    payload_ids: set[str] = set()
    for index, payload in enumerate(value["payloads"]):
        expect_keys(
            payload,
            {"id", "path", "schema", "digest_field", "digest"},
            f"payloads[{index}]",
        )
        require(payload["id"] not in payload_ids, f"duplicate payload id: {payload['id']}")
        payload_ids.add(payload["id"])
        require(HEX64.fullmatch(payload["digest"]) is not None, f"invalid payload digest: {payload['id']}")
    require(
        payload_ids
        == {
            "outer41-jacobi-block",
            "outer41-jacobi-certificate",
            "outer41-jacobi-telescope",
            "shifted-square-propagation",
        },
        "payload inventory changed",
    )

    command_ids: set[str] = set()
    records: dict[str, str] = {}
    for index, command in enumerate(value["commands"]):
        expect_keys(command, {"id", "argv", "record", "timeout", "oracle"}, f"commands[{index}]")
        require(command["id"] not in command_ids, f"duplicate command id: {command['id']}")
        command_ids.add(command["id"])
        records[command["id"]] = command["record"]
        require(
            isinstance(command["argv"], list)
            and command["argv"]
            and all(isinstance(item, str) and item for item in command["argv"]),
            f"invalid argv: {command['id']}",
        )
        require(
            0 < command["timeout"] <= value["budgets"]["build_seconds"],
            f"invalid timeout: {command['id']}",
        )
        require(command["id"] in EXPECTED_COMMANDS, "unknown command id")
        expected_argv, expected_record, expected_timeout, expected_oracle = EXPECTED_COMMANDS[
            command["id"]
        ]
        require(command["argv"] == expected_argv, f"command argv drift: {command['id']}")
        require(command["record"] == expected_record, f"command record drift: {command['id']}")
        require(command["timeout"] == expected_timeout, f"command timeout drift: {command['id']}")
        require(command["oracle"] == expected_oracle, f"command oracle drift: {command['id']}")
    require(records == EXPECTED_RECORDS, "command or record inventory changed")
    for finite_object in value["finite_objects"]:
        object_id = finite_object["object_id"]
        command_sets: dict[str, set[str]] = {}
        for key in ("generator_command", "independent_replay_command"):
            raw_commands = finite_object[key]
            referenced = raw_commands.split(" plus ")
            require(
                raw_commands == " plus ".join(referenced)
                and referenced
                and all(command_id in command_ids for command_id in referenced)
                and len(referenced) == len(set(referenced)),
                f"invalid finite object command lineage: {object_id}.{key}",
            )
            command_sets[key] = set(referenced)
        require(
            command_sets["generator_command"].isdisjoint(
                command_sets["independent_replay_command"]
            ),
            f"finite object generator is its own independent replay: {object_id}",
        )

    mutations = value["hostile_mutations"]
    require(len(mutations) == len(EXPECTED_HOSTILE_MUTATIONS), "hostile mutation count changed")
    for index, mutation in enumerate(mutations):
        expect_keys(mutation, {"id", "target", "oracle"}, f"hostile_mutations[{index}]")
        expected_id, expected_target, expected_oracle = EXPECTED_HOSTILE_MUTATIONS[index]
        require(mutation["id"] == expected_id, "hostile mutation ids changed")
        require(mutation["target"] == expected_target, f"hostile target drift: {expected_id}")
        require(mutation["oracle"] == expected_oracle, f"hostile oracle drift: {expected_id}")
    require(
        len({item["oracle"] for item in mutations}) == len(EXPECTED_HOSTILE_MUTATIONS),
        "hostile oracles must be unique",
    )
    return value


def polynomial_add(left: list[int], right: list[int]) -> list[int]:
    """Add coefficient vectors in increasing degree order."""

    size = max(len(left), len(right))
    return [
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(size)
    ]


def dickson_source_coefficients(prime: int) -> list[int]:
    """Reconstruct D_prime(x,-1)-2 from D_0=2, D_1=x."""

    d0 = [2]
    d1 = [0, 1]
    for _ in range(2, prime + 1):
        d0, d1 = d1, polynomial_add([0] + d1, d0)
    d1[0] -= 2
    return d1


def dickson_value(index: int, x: int) -> int:
    """Evaluate D_index(x,-1) by an implementation separate from GP."""

    if index == 0:
        return 2
    if index == 1:
        return x
    previous, current = 2, x
    for _ in range(2, index + 1):
        previous, current = current, x * current + previous
    return current


def evaluate_polynomial(coefficients: Iterable[int], x: int) -> int:
    """Evaluate an increasing-order coefficient vector by Horner's rule."""

    result = 0
    for coefficient in reversed(list(coefficients)):
        result = result * x + coefficient
    return result


def is_prime(number: int) -> bool:
    """Deterministically test the bounded manifest factors."""

    if number < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for prime in small_primes:
        if number % prime == 0:
            return number == prime
    divisor = 41
    while divisor * divisor <= number:
        if number % divisor == 0 or number % (divisor + 2) == 0:
            return False
        divisor += 6
    return True


def validate_finite_field(field: Mapping[str, Any]) -> None:
    """Check one exact fixed-field row without invoking its certificate producer."""

    expected_keys = {
        "prime",
        "source_coefficients",
        "detector_dickson_coefficients",
        "polynomial_discriminant",
        "signature",
        "theta_norm",
        "detector_norm",
        "b_norm",
        "reference_norm",
        "detector_at_four",
        "reference_factors",
        "reference_symbols",
        "dyadic_rows",
        "ramified_row",
    }
    prime = field["prime"]
    if prime == 17:
        expected_keys |= {"fixed_prs_exceptions"}
    elif prime == 41:
        expected_keys |= {
            "boundary_modulus",
            "boundary_value",
            "boundary_square_target",
            "local_exception_indices",
            "factor_thirteen_index",
            "factor_thirteen_residue",
            "factor_thirteen_value",
        }
    else:
        raise EvidenceError("unexpected fixed-field prime")
    expect_keys(field, expected_keys, f"finite.outer{prime}")
    require(
        field["polynomial_discriminant"]
        == ("2^24*17^17" if prime == 17 else "2^60*41^41"),
        f"degree-{prime}-discriminant",
    )
    require(field["source_coefficients"] == dickson_source_coefficients(prime), f"degree-{prime}-source")
    require(
        evaluate_polynomial(field["source_coefficients"], 4) == field["reference_norm"],
        f"degree-{prime}-reference-norm",
    )
    detector = field["detector_dickson_coefficients"]
    detector_at_four = detector[0] + detector[1] * 4 + sum(
        detector[index] * dickson_value(index, 4)
        for index in range(2, len(detector))
    )
    require(detector_at_four == field["detector_at_four"], "detector-at-four")
    require(detector == EXPECTED_DETECTORS[prime], "detector-coefficient-vector")
    require(field["theta_norm"] == 2, f"degree-{prime}-theta-norm")
    require(field["detector_norm"] == -1, f"degree-{prime}-detector-norm")
    require(field["b_norm"] == -2, f"degree-{prime}-b-norm")
    require(field["signature"] == [1, (prime - 1) // 2], f"degree-{prime}-signature")
    factors = field["reference_factors"]
    product = 1
    for factor in factors:
        require(is_prime(factor), f"outer{prime}-reference-factor-primality")
        product *= factor
    require(product * 2 == field["reference_norm"], f"outer{prime}-reference-factor-product")
    require(len(factors) == len(field["reference_symbols"]), "reference-symbol-count")
    rows = field["dyadic_rows"]
    require(len(rows) == 3 and all(len(row) == 6 for row in rows), "dyadic-row-shape")
    require(sum(row[0] * row[1] for row in rows) == prime, "dyadic-degree-sum")
    require(rows[0] == [1, 1, 1, 1, 1, 1], "dyadic-valuation-row")
    residual = (prime - 1) // 4
    require(
        rows[1:] == [[2, residual, 0, 0, 0, -1], [2, residual, 0, 0, 0, 1]],
        "dyadic-valuation-row",
    )
    require(field["ramified_row"] == [prime, 1, 0, 0, 0, 1], "ramified-prime-row")
    hilbert_product = 1
    for row in rows:
        hilbert_product *= row[-1]
    for symbol in field["reference_symbols"]:
        hilbert_product *= symbol
    hilbert_product *= field["ramified_row"][-1]
    require(hilbert_product == 1, "hilbert-product")
    require(
        field["reference_symbols"] == EXPECTED_REFERENCE_SYMBOLS[prime],
        "reference-symbol-vector",
    )
    if prime == 17:
        require(field["fixed_prs_exceptions"] == [3, 5, 7, 11, 13, 31, 37], "fixed-17-exceptions")
    else:
        require(field["local_exception_indices"] == [37, 25, 23, 11, 3], "fixed-41-exceptions")
        require(
            field["factor_thirteen_value"] == 13
            and field["factor_thirteen_index"] == 23
            and field["factor_thirteen_residue"] == 12,
            "factor-thirteen-local-row",
        )
        modulus = field["boundary_modulus"]
        previous, current = 1, 2
        for _ in range(1, 41):
            previous, current = current, (4 * current + previous) % modulus
        require(current == field["boundary_value"] == 21, "fixed-41-boundary-value")
        require(
            field["boundary_square_target"] == (field["boundary_value"] - 1) % modulus,
            "fixed-41-boundary-target",
        )
        require(
            all(
                (value * value) % modulus != field["boundary_square_target"]
                for value in range(modulus)
            ),
            "fixed-41-boundary-nonresidue",
        )


def validate_sources(manifest: Mapping[str, Any]) -> None:
    """Bind every listed input to its exact SHA-256 bytes."""

    maximum = manifest["budgets"]["max_input_bytes"]
    for source in manifest["sources"]:
        actual = sha256_bytes(read_bounded(source["path"], maximum))
        require(actual == source["sha256"], f"source digest mismatch: {source['path']}")


def load_json_value(path: str, maximum: int) -> tuple[bytes, dict[str, Any]]:
    """Load canonical JSON and reject duplicate keys."""

    raw = read_bounded(path, maximum)
    try:
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise EvidenceError(f"cannot decode canonical JSON: {path}") from error
    require(isinstance(value, dict), f"JSON root must be an object: {path}")
    require(raw == canonical_json_bytes(value), f"noncanonical JSON bytes: {path}")
    return raw, value


def validate_payload_value(payload: Mapping[str, Any], value: Mapping[str, Any]) -> None:
    """Validate one packet's schema and content digest."""

    require(value.get("schema") == payload["schema"], f"payload schema mismatch: {payload['id']}")
    field = payload["digest_field"]
    require(value.get(field) == payload["digest"], f"payload declared digest mismatch: {payload['id']}")
    if field == "payload_sha256":
        body = dict(value)
        body.pop(field)
        actual = sha256_bytes(canonical_json_bytes(body))
    elif field == "result_sha256":
        require("result" in value, "payload result missing")
        actual = sha256_bytes(canonical_json_bytes(value["result"]))
    else:
        raise EvidenceError(f"unsupported digest field: {field}")
    require(actual == payload["digest"], "payload-result-digest")


def validate_payloads(manifest: Mapping[str, Any]) -> None:
    """Validate all canonical finite packets independently of their producers."""

    maximum = manifest["budgets"]["max_input_bytes"]
    for payload in manifest["payloads"]:
        _, value = load_json_value(payload["path"], maximum)
        validate_payload_value(payload, value)


def normalise_space(value: str) -> str:
    """Collapse whitespace for exact signature-fragment checks."""

    return " ".join(value.split())


def normalise_signature(value: str) -> str:
    """Normalize namespace qualification and Markdown math spelling only."""

    value = value.replace("Erdos364.", "")
    value = value.replace(r"\(", "").replace(r"\)", "")
    value = value.replace(r"\mid", " divides ")
    value = re.sub(r"\s*([+^=])\s*", r" \1 ", value)
    return normalise_space(value)


def validate_theorems(
    manifest: Mapping[str, Any], overrides: Mapping[str, str] | None = None
) -> None:
    """Check maintained signatures and the prose-only derived corollary."""

    maximum = manifest["budgets"]["max_input_bytes"]
    overrides = overrides or {}
    cache: dict[str, str] = {}
    for theorem in manifest["theorems"]:
        path = theorem["path"]
        if path not in cache:
            cache[path] = overrides.get(path, read_text(path, maximum))
        normalized = normalise_space(cache[path])
        require(
            normalise_signature(theorem["signature"]) in normalise_signature(cache[path]),
            f"theorem signature mismatch: {theorem['name']}",
        )
        for fragment in theorem["required_fragments"]:
            require(
                normalise_space(fragment) in normalized,
                f"theorem signature mismatch: {theorem['name']}",
            )
        if theorem["name"] == "PaperI.complete_source_full_index_corollary":
            require("MAINTAINED_LEAN" not in theorem["statuses"], "prose corollary mislabeled as Lean")
            require(theorem["role"] == "HUMAN_DERIVED_COROLLARY", "prose corollary role changed")
    outer17_path = "Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean"
    outer17 = overrides.get(outer17_path, read_text(outer17_path, maximum))
    require("2 * A * outer17R2 A - outer17R3 A" in outer17, "fixed-17-source-digest")
    outer17_certificate = read_text(
        "problems/square-middle/sm2-lower-square/outer-seventeen-certificate.md", maximum
    )
    require("3, 5, 7, 11, 13, 31, 37" in outer17_certificate, "fixed-17-exceptions")
    outer41_path = "Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean"
    outer41 = overrides.get(outer41_path, read_text(outer41_path, maximum))
    require(
        "sm2LucasReal 2 41 % 23 = 21" in outer41
        and "∀ z : ZMod 23, z ^ 2 ≠ 20" in outer41,
        "fixed-41-boundary-source",
    )
    require(
        "(h41 : 41 ∣ 2 * generator.outerIndex + 1)" in normalise_space(outer41),
        "selected-41-signature",
    )
    require(
        "41 ∣ pellRank data.upperKernel allocation.upper_pellKernel" in normalise_space(outer41),
        "selected-41-signature",
    )


def validate_crosswalk(manifest: Mapping[str, Any], override: str | None = None) -> None:
    """Check exact theorem/prose quantifiers and selected-prime ceilings."""

    maximum = manifest["budgets"]["max_input_bytes"]
    text = override
    if text is None:
        text = read_text("papers/shifted-square-17-41/theorem-formal-crosswalk.md", maximum)
    require(text.count(r"For all \(A,y\in\mathbf N\),") == 4, "theorem-prose-crosswalk")
    require(text.count("plus a separate explicit") == 2, "theorem-prose-crosswalk")
    require("NoSm2OuterLargeBlocks" in text, "theorem-prose-crosswalk")
    require("NoSm2RankDefectBlocks" in text, "theorem-prose-crosswalk")


def command_environment() -> dict[str, str]:
    """Return the narrow deterministic environment for trusted-local checks."""

    environment = os.environ.copy()
    environment.update(
        {
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONHASHSEED": "0",
            "GIT_CONFIG_NOSYSTEM": "1",
        }
    )
    return environment


def terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    """Terminate the complete process group, escalating to SIGKILL after a grace period."""

    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    except OSError as error:
        raise EvidenceError("cannot terminate process group") from error
    time.sleep(PROCESS_TERMINATION_GRACE_SECONDS)
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError as error:
        if process.poll() is None:
            process.kill()
            raise EvidenceError("cannot kill process group") from error
    except OSError as error:
        raise EvidenceError("cannot kill process group") from error
    try:
        process.wait(timeout=PROCESS_TERMINATION_GRACE_SECONDS)
    except subprocess.TimeoutExpired as error:
        raise EvidenceError("process group did not terminate") from error


def run_bounded_process(
    argv: list[str],
    *,
    timeout: float,
    maximum: int,
    context: str,
) -> tuple[int, bytes, bytes]:
    """Capture stdout and stderr under one streaming byte and wall-clock ceiling."""

    require(timeout > 0, f"invalid process timeout: {context}")
    require(maximum >= 0, f"invalid process output budget: {context}")
    try:
        process = subprocess.Popen(
            argv,
            cwd=REPOSITORY_ROOT,
            env=command_environment(),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
    except OSError as error:
        raise EvidenceError(f"cannot execute process: {context}") from error
    require(process.stdout is not None and process.stderr is not None, "process pipes unavailable")
    selector = selectors.DefaultSelector()
    streams = {"stdout": process.stdout, "stderr": process.stderr}
    chunks: dict[str, list[bytes]] = {name: [] for name in streams}
    total = 0
    deadline = time.monotonic() + timeout
    try:
        for name, stream in streams.items():
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, name)
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise EvidenceError(f"process timeout: {context}")
            for key, _ in selector.select(min(remaining, 0.25)):
                try:
                    chunk = os.read(
                        key.fileobj.fileno(),
                        min(64 * 1024, maximum - total + 1),
                    )
                except BlockingIOError:
                    continue
                except OSError as error:
                    raise EvidenceError(f"cannot read process output: {context}") from error
                if not chunk:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                total += len(chunk)
                if total > maximum:
                    raise EvidenceError(f"combined process output exceeds budget: {context}")
                chunks[key.data].append(chunk)
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise EvidenceError(f"process timeout: {context}")
        try:
            returncode = process.wait(timeout=remaining)
        except subprocess.TimeoutExpired as error:
            raise EvidenceError(f"process timeout: {context}") from error
    except BaseException:
        terminate_process_group(process)
        raise
    finally:
        selector.close()
        for stream in streams.values():
            if not stream.closed:
                stream.close()
    return returncode, b"".join(chunks["stdout"]), b"".join(chunks["stderr"])


def run_version(argv: list[str]) -> str:
    """Run a small local version probe."""

    try:
        returncode, stdout, stderr = run_bounded_process(
            argv,
            timeout=20,
            maximum=PROBE_OUTPUT_MAX_BYTES,
            context=f"tool version probe {argv[0]}",
        )
    except EvidenceError as error:
        raise EvidenceError(f"tool version probe failed: {argv[0]}") from error
    require(returncode == 0, f"tool version probe failed: {argv[0]}")
    return (stdout + stderr).decode("utf-8", errors="replace")


def validate_toolchain(manifest: Mapping[str, Any]) -> None:
    """Require the exact local tool and dependency pins."""

    tools = manifest["tools"]
    lean = run_version(["lean", "--version"])
    require(f"version {tools['lean']}" in lean, "Lean version mismatch")
    require(f"commit {tools['lean_commit']}" in lean, "Lean commit mismatch")
    lake = run_version(["lake", "--version"])
    require(f"Lake version {tools['lake']}" in lake, "Lake version mismatch")
    gp = run_version(["gp", "--version"])
    require(f"Version {tools['pari_gp']}" in gp, "PARI/GP version mismatch")
    python_version = run_version(["python3", "--version"])
    require(f"Python {tools['python']}" in python_version, "Python version mismatch")
    current_platform = f"{platform.system()}-{platform.release()}-{platform.machine()}"
    require(current_platform == tools["platform"], "platform mismatch")
    manifest_json = json.loads(read_text("lake-manifest.json", manifest["budgets"]["max_input_bytes"]))
    mathlib = [item for item in manifest_json["packages"] if item["name"] == "mathlib"]
    require(len(mathlib) == 1, "mathlib package pin missing or duplicated")
    require(mathlib[0]["rev"] == tools["mathlib_commit"], "mathlib commit mismatch")


def git_output(argv: list[str]) -> bytes:
    """Run one bounded read-only Git identity query."""

    try:
        returncode, stdout, _ = run_bounded_process(
            ["git", *argv],
            timeout=20,
            maximum=PROBE_OUTPUT_MAX_BYTES,
            context=f"Git identity query {argv[0]}",
        )
    except EvidenceError as error:
        raise EvidenceError(f"Git identity query failed: {argv[0]}") from error
    require(returncode == 0, f"Git identity query failed: {argv[0]}")
    return stdout


def validate_repository_identity(manifest: Mapping[str, Any]) -> None:
    """Freeze the complete source tree while allowing only Issue #122 paths."""

    source_commit = manifest["source_commit"]
    tree = git_output(["show", "-s", "--format=%T", source_commit]).decode("ascii").strip()
    require(tree == manifest["source_tree"], "source Git tree mismatch")
    git_output(["merge-base", "--is-ancestor", source_commit, "HEAD"])
    allowed_problem = "problems/square-middle/sm2-lower-square/problem.md"
    evidence_prefix = "papers/shifted-square-17-41/evidence/"

    changed = git_output(["diff", "--name-only", source_commit, "--"]).decode("utf-8").splitlines()
    for path in changed:
        require(
            path == allowed_problem or path.startswith(evidence_prefix),
            f"tracked path outside evidence freeze: {path}",
        )

    status = git_output(["status", "--porcelain=v1", "--untracked-files=all", "-z"])
    for raw_entry in status.split(b"\0"):
        if not raw_entry:
            continue
        entry = raw_entry.decode("utf-8")
        require(len(entry) >= 4, "malformed Git status entry")
        require(entry[:2] not in {"R ", " R", "C ", " C"}, "rename or copy outside freeze")
        path = entry[3:]
        require(
            path == allowed_problem or path.startswith(evidence_prefix),
            f"worktree path outside evidence freeze: {path}",
        )


def normalize_output(raw: bytes) -> str:
    """Normalize line endings and checkout-specific absolute roots."""

    text = raw.decode("utf-8", errors="replace").replace("\r\n", "\n").replace("\r", "\n")
    roots = {str(REPOSITORY_ROOT): "<REPOSITORY_ROOT>"}
    package_cache = REPOSITORY_ROOT / ".lake" / "packages"
    if package_cache.exists():
        dependency_root = package_cache.resolve().parents[1]
        if dependency_root != REPOSITORY_ROOT:
            roots[str(dependency_root)] = "<DEPENDENCY_CACHE_ROOT>"
    for source, replacement in roots.items():
        text = text.replace(source, replacement)
    return text


def validate_axiom_output(output: str, manifest: Mapping[str, Any]) -> None:
    """Require one exact parsed axiom row for each theorem and support."""

    pattern = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.DOTALL)
    rows = pattern.findall(output)
    require(len(rows) == len(ALL_AXIOM_NAMES), "axiom record count mismatch")
    parsed: dict[str, list[str]] = {}
    for name, body in rows:
        require(name not in parsed, f"duplicate axiom record: {name}")
        parsed[name] = [item.strip() for item in body.replace("\n", " ").split(",") if item.strip()]
    require(set(parsed) == set(ALL_AXIOM_NAMES), "axiom declaration inventory mismatch")
    for name in ALL_AXIOM_NAMES:
        require(parsed[name] == manifest["allowed_axioms"], f"axiom set mismatch: {name}")


def validate_command_result(
    command: Mapping[str, Any],
    returncode: int,
    stdout: str,
    stderr: str,
    manifest: Mapping[str, Any],
) -> None:
    """Apply the semantic success oracle for one bounded command."""

    require(returncode == 0, f"command failed: {command['id']}")
    combined = stdout + "\n" + stderr
    require("\x00" not in combined, f"NUL output rejected: {command['id']}")
    oracle = command["oracle"]
    if oracle in {"lean-success", "lake-success"}:
        require(
            re.search(r"(^|\n).*error:", combined, flags=re.IGNORECASE) is None,
            f"error diagnostic in successful command: {command['id']}",
        )
    elif oracle == "axiom-exact":
        validate_axiom_output(combined, manifest)
    else:
        require(combined.count(oracle) == 1, f"success marker mismatch: {command['id']}")


def execute_command(
    command: Mapping[str, Any],
    manifest: Mapping[str, Any],
    deadline: float | None = None,
) -> dict[str, Any]:
    """Execute one bounded local command and return a canonical record object."""

    timeout = float(command["timeout"])
    if deadline is not None:
        remaining = deadline - time.monotonic()
        require(remaining > 0, "aggregate command budget exhausted")
        timeout = min(timeout, remaining)
    maximum = manifest["budgets"]["max_record_bytes"]
    returncode, stdout_raw, stderr_raw = run_bounded_process(
        command["argv"],
        timeout=timeout,
        maximum=maximum,
        context=f"command {command['id']}",
    )
    stdout = normalize_output(stdout_raw)
    stderr = normalize_output(stderr_raw)
    normalized_bytes = len(stdout.encode("utf-8")) + len(stderr.encode("utf-8"))
    require(normalized_bytes <= maximum, f"normalized output exceeds budget: {command['id']}")
    validate_command_result(command, returncode, stdout, stderr, manifest)
    record = {
        "argv": command["argv"],
        "command_id": command["id"],
        "exit_code": returncode,
        "oracle": command["oracle"],
        "schema": RECORD_SCHEMA,
        "source_commit": manifest["source_commit"],
        "stderr": stderr,
        "stderr_sha256": sha256_bytes(stderr.encode("utf-8")),
        "stdout": stdout,
        "stdout_sha256": sha256_bytes(stdout.encode("utf-8")),
    }
    require(len(pretty_json_bytes(record)) <= maximum, f"command record exceeds budget: {command['id']}")
    return record


def write_text(relative: str, text: str) -> None:
    """Write one approved evidence output path."""

    path = EVIDENCE_ROOT / relative
    require(path.resolve().is_relative_to(EVIDENCE_ROOT), f"output path escape: {relative}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def write_record(relative: str, record: Mapping[str, Any]) -> None:
    """Write a deterministic pretty JSON command record."""

    write_text(relative, pretty_json_bytes(record).decode("ascii"))


def validate_record(command: Mapping[str, Any], manifest: Mapping[str, Any]) -> None:
    """Validate one frozen command record without re-executing it."""

    relative = f"papers/shifted-square-17-41/evidence/{command['record']}"
    raw = read_bounded(relative, manifest["budgets"]["max_record_bytes"])
    try:
        record = json.loads(raw.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise EvidenceError(f"invalid command record: {command['id']}") from error
    require(
        raw == pretty_json_bytes(record),
        f"noncanonical command record: {command['id']}",
    )
    expect_keys(
        record,
        {
            "argv",
            "command_id",
            "exit_code",
            "oracle",
            "schema",
            "source_commit",
            "stderr",
            "stderr_sha256",
            "stdout",
            "stdout_sha256",
        },
        f"record {command['id']}",
    )
    require(record["schema"] == RECORD_SCHEMA, f"record schema mismatch: {command['id']}")
    require(record["command_id"] == command["id"], f"record id mismatch: {command['id']}")
    require(record["argv"] == command["argv"], f"record argv mismatch: {command['id']}")
    require(record["oracle"] == command["oracle"], f"record oracle mismatch: {command['id']}")
    require(record["source_commit"] == manifest["source_commit"], f"record source commit mismatch: {command['id']}")
    require(
        sha256_bytes(record["stdout"].encode("utf-8")) == record["stdout_sha256"],
        f"record stdout digest mismatch: {command['id']}",
    )
    require(
        sha256_bytes(record["stderr"].encode("utf-8")) == record["stderr_sha256"],
        f"record stderr digest mismatch: {command['id']}",
    )
    validate_command_result(command, record["exit_code"], record["stdout"], record["stderr"], manifest)


def expected_evidence_paths(manifest: Mapping[str, Any]) -> set[str]:
    """Return the exact evidence allowlist, excluding the hash index."""

    return EVIDENCE_BASE_FILES | ASSURANCE_RECORDS | set(EXPECTED_RECORDS.values())


def current_evidence_paths() -> set[str]:
    """Enumerate regular evidence files while rejecting symlinks and junk."""

    paths: set[str] = set()
    for path in EVIDENCE_ROOT.rglob("*"):
        relative = path.relative_to(EVIDENCE_ROOT).as_posix()
        require(not path.is_symlink(), f"symlink in evidence tree: {relative}")
        if path.is_dir():
            require(path.name != "__pycache__", "Python cache in evidence tree")
            continue
        require(path.is_file(), f"non-regular evidence object: {relative}")
        require(path.name != ".DS_Store", "Finder metadata in evidence tree")
        if relative != "hashes/SHA256SUMS":
            paths.add(relative)
    return paths


def scan_public_text(raw: bytes, relative: str, *, kind: str) -> None:
    """Reject binary, private-location, URI, and secret-like bytes."""

    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"non-UTF-8 {kind}: {relative}") from error
    for pattern in PRIVATE_PATTERNS:
        require(pattern.search(text) is None, f"private path or URI in {kind}: {relative}")
    for pattern in SECRET_PATTERNS:
        require(pattern.search(text) is None, f"secret-like text in {kind}: {relative}")


def privacy_and_integrity_report(manifest: Mapping[str, Any]) -> str:
    """Run bounded rights, privacy, token and path checks."""

    expected = expected_evidence_paths(manifest)
    actual = current_evidence_paths()
    self_record = "assurance/integrity-output.txt"
    require(
        not ((expected - {self_record}) - actual),
        f"missing evidence files: {sorted((expected - {self_record}) - actual)}",
    )
    require(not (actual - expected), f"unapproved evidence files: {sorted(actual - expected)}")
    allowed_suffixes = {".md", ".toml", ".py", ".sh", ".lean", ".gp", ".txt"}
    maximum_record = manifest["budgets"]["max_record_bytes"]
    maximum_input = manifest["budgets"]["max_input_bytes"]
    total = 0
    for relative in sorted(actual):
        if relative == self_record:
            continue
        path = EVIDENCE_ROOT / relative
        require(path.suffix in allowed_suffixes, f"binary or unapproved evidence type: {relative}")
        raw = read_path_bounded(path, maximum_record, f"evidence/{relative}")
        total += len(raw)
        scan_public_text(raw, relative, kind="evidence")
    require(total <= maximum_record, "evidence tree exceeds 10 MiB")

    source_bytes = 0
    external_bytes = 0
    for source in manifest["sources"]:
        raw = read_bounded(source["path"], maximum_input)
        source_bytes += len(raw)
        scan_public_text(raw, source["path"], kind="manifest source")
        if source["role"] == "external-bytes":
            external_bytes += len(raw)
    require(external_bytes == 0, "external source bytes are not permitted")
    token_paths = [
        "Erdos364/DicksonLucas/ShiftedSquarePropagation.lean",
        "Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean",
        "Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean",
        "papers/shifted-square-17-41/source-theorem.md",
        "papers/shifted-square-17-41/theorem-formal-crosswalk.md",
    ]
    token_pattern = re.compile(r"\b(?:sorry|admit|todo|fixme|changeme)\b", re.IGNORECASE)
    for relative in token_paths:
        require(
            token_pattern.search(read_text(relative, maximum_input)) is None,
            f"unfinished token in maintained input: {relative}",
        )
    rights = normalise_space(
        read_text("papers/shifted-square-17-41/evidence/PUBLIC_RIGHTS_PRIVACY.md", maximum_input)
    )
    for fragment in [
        "No public release is authorized by this bundle.",
        "No third-party bytes are copied into the evidence tree.",
        "A clean-history allowlisted export is required.",
        "License selection remains outside Issue #122.",
        "BLOCKED_PUBLIC_EXPORT_INPUT",
        "no proposed public-import commit",
    ]:
        require(fragment in rights, "rights and privacy declaration incomplete")
    ceiling = normalise_space(
        read_text("papers/shifted-square-17-41/evidence/CLAIM_CEILING.md", maximum_input)
    )
    require("maintained internal terminal count remains 1/4" in ceiling, "terminal ceiling missing")
    require("not a percentage of Erdős 364 completion" in ceiling, "terminal count interpretation missing")
    return (
        "PAPER1_INTEGRITY_OK "
        f"files={len(expected)} bytes_excluding_self_record={total} "
        f"source_files={len(manifest['sources'])} source_bytes_scanned={source_bytes} "
        "private_paths=0 secrets=0 "
        f"external_bytes={external_bytes} "
        "terminal=maintained-internal-1-of-4\n"
    )


def expect_rejection(mutation_id: str, oracle: str, callback: Callable[[], None]) -> str:
    """Require one hostile mutation to fail for its named reason."""

    try:
        callback()
    except EvidenceError as error:
        require(oracle in str(error), f"{mutation_id} rejected by wrong oracle: {error}")
        return f"{mutation_id} REJECTED oracle={oracle}\n"
    raise EvidenceError(f"{mutation_id} was accepted")


def resource_control_report() -> str:
    """Self-test streaming output, process-group timeout, and bounded file reads."""

    overflow_command = [
        sys.executable,
        "-B",
        "-c",
        "import sys;sys.stdout.buffer.write(b'o'*768);sys.stderr.buffer.write(b'e'*768)",
    ]
    try:
        run_bounded_process(
            overflow_command,
            timeout=1.0,
            maximum=1024,
            context="resource combined-output probe",
        )
    except EvidenceError as error:
        require(
            "combined process output exceeds budget" in str(error),
            f"resource output probe rejected by wrong oracle: {error}",
        )
    else:
        raise EvidenceError("resource combined-output probe was accepted")

    with tempfile.TemporaryDirectory(prefix="erdos364-paper1-resource-") as temporary:
        temporary_root = Path(temporary)
        ready_path = temporary_root / "descendant-ready.txt"
        survived_path = temporary_root / "descendant-survived.txt"
        child_code = (
            "import os,signal,sys,time;from pathlib import Path;"
            "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
            "Path(sys.argv[1]).write_text(str(os.getpid()),encoding='ascii');"
            "time.sleep(.75);Path(sys.argv[2]).write_text('survived',encoding='ascii');"
            "time.sleep(30)"
        )
        parent_code = (
            "import signal,subprocess,sys,time;"
            "signal.signal(signal.SIGTERM,signal.SIG_IGN);"
            "subprocess.Popen([sys.executable,'-B','-c',sys.argv[1],sys.argv[2],sys.argv[3]]);"
            "time.sleep(30)"
        )
        try:
            run_bounded_process(
                [
                    sys.executable,
                    "-B",
                    "-c",
                    parent_code,
                    child_code,
                    str(ready_path),
                    str(survived_path),
                ],
                timeout=0.4,
                maximum=1024,
                context="resource process-group probe",
            )
        except EvidenceError as error:
            require(
                "process timeout" in str(error),
                f"resource timeout probe rejected by wrong oracle: {error}",
            )
        else:
            raise EvidenceError("resource process-group timeout probe was accepted")
        require(ready_path.is_file(), "resource descendant did not start")
        descendant_pid_raw = read_path_bounded(ready_path, 32, "resource descendant pid")
        require(descendant_pid_raw.isdigit(), "resource descendant pid is invalid")
        descendant_pid = int(descendant_pid_raw)
        disappearance_deadline = time.monotonic() + 2.0
        while True:
            try:
                os.kill(descendant_pid, 0)
            except ProcessLookupError:
                break
            except OSError as error:
                raise EvidenceError("cannot probe resource descendant") from error
            if survived_path.exists() or time.monotonic() >= disappearance_deadline:
                try:
                    os.kill(descendant_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                raise EvidenceError("resource process-group descendant survived timeout")
            time.sleep(0.05)
        require(not survived_path.exists(), "resource descendant wrote after process-group kill")

        oversized_path = temporary_root / "oversized.bin"
        oversized_path.write_bytes(b"x" * 17)
        try:
            read_path_bounded(oversized_path, 16, "resource oversized input")
        except EvidenceError as error:
            require(
                "input exceeds byte budget" in str(error),
                f"resource bounded-read probe rejected by wrong oracle: {error}",
            )
        else:
            raise EvidenceError("resource bounded-read probe was accepted")
    return (
        "PAPER1_RESOURCE_CONTROL_OK combined_output=REJECTED "
        "process_group=KILLED bounded_read=REJECTED\n"
    )


def hostile_report(manifest: Mapping[str, Any]) -> str:
    """Execute all twelve in-memory hostile mutations without editing sources."""

    fields = manifest["finite"]
    lines: list[str] = []
    mutated = copy.deepcopy(fields["outer17"])
    mutated["source_coefficients"][13] += 1
    lines.append(expect_rejection("M01", "degree-17-source", lambda: validate_finite_field(mutated)))
    mutated = copy.deepcopy(fields["outer41"])
    mutated["source_coefficients"][9] += 1
    lines.append(expect_rejection("M02", "degree-41-source", lambda: validate_finite_field(mutated)))
    mutated = copy.deepcopy(fields["outer41"])
    mutated["detector_dickson_coefficients"][0] += 1
    lines.append(expect_rejection("M03", "detector-at-four", lambda: validate_finite_field(mutated)))
    mutated = copy.deepcopy(fields["outer41"])
    mutated["reference_factors"][1] = 1381
    lines.append(
        expect_rejection(
            "M04",
            "outer41-reference-factor-product",
            lambda: validate_finite_field(mutated),
        )
    )
    mutated = copy.deepcopy(fields["outer41"])
    mutated["dyadic_rows"][1][0] = 1
    lines.append(expect_rejection("M05", "dyadic-degree-sum", lambda: validate_finite_field(mutated)))
    mutated = copy.deepcopy(fields["outer17"])
    mutated["dyadic_rows"][0][2] = 0
    lines.append(expect_rejection("M06", "dyadic-valuation-row", lambda: validate_finite_field(mutated)))
    mutated = copy.deepcopy(fields["outer41"])
    mutated["reference_symbols"][1] = 1
    lines.append(expect_rejection("M07", "hilbert-product", lambda: validate_finite_field(mutated)))
    outer17_path = "Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean"
    outer17 = read_text(outer17_path, manifest["budgets"]["max_input_bytes"])
    outer17 = outer17.replace(
        "2 * A * outer17R2 A - outer17R3 A",
        "2 * A * outer17R2 A + outer17R3 A",
        1,
    )
    lines.append(
        expect_rejection(
            "M08",
            "fixed-17-source-digest",
            lambda: validate_theorems(manifest, {outer17_path: outer17}),
        )
    )
    mutated = copy.deepcopy(fields["outer41"])
    mutated["factor_thirteen_value"] = 1
    lines.append(expect_rejection("M09", "factor-thirteen-local-row", lambda: validate_finite_field(mutated)))
    outer41_path = "Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean"
    outer41 = read_text(outer41_path, manifest["budgets"]["max_input_bytes"])
    outer41 = outer41.replace(
        "(h41 : 41 ∣ 2 * generator.outerIndex + 1)",
        "(hnearby : generator.OuterLargePacket)",
    )
    lines.append(
        expect_rejection(
            "M10",
            "selected-41-signature",
            lambda: require(
                "(h41 : 41 ∣ 2 * generator.outerIndex + 1)"
                in normalise_space(outer41),
                "selected-41-signature",
            ),
        )
    )
    crosswalk = read_text(
        "papers/shifted-square-17-41/theorem-formal-crosswalk.md",
        manifest["budgets"]["max_input_bytes"],
    )
    crosswalk = crosswalk.replace(
        r"For all \(A,y\in\mathbf N\),",
        r"For every \(A\), there exists \(y\in\mathbf N\),",
        1,
    )
    lines.append(
        expect_rejection(
            "M11", "theorem-prose-crosswalk", lambda: validate_crosswalk(manifest, crosswalk)
        )
    )
    payload = next(item for item in manifest["payloads"] if item["id"] == "shifted-square-propagation")
    _, value = load_json_value(payload["path"], manifest["budgets"]["max_input_bytes"])
    mutated_value = copy.deepcopy(value)
    mutated_value["result_sha256"] = "0" + mutated_value["result_sha256"][1:]
    if mutated_value["result_sha256"] == value["result_sha256"]:
        mutated_value["result_sha256"] = "1" + mutated_value["result_sha256"][1:]
    mutated_payload = copy.deepcopy(payload)
    mutated_payload["digest"] = mutated_value["result_sha256"]
    lines.append(
        expect_rejection(
            "M12",
            "payload-result-digest",
            lambda: validate_payload_value(mutated_payload, mutated_value),
        )
    )
    require(len(lines) == 12, "hostile mutation execution count changed")
    return (
        "".join(lines)
        + resource_control_report()
        + "PAPER1_HOSTILE_OK mutations=12 accepted=0\n"
    )


def write_hash_index(manifest: Mapping[str, Any]) -> None:
    """Freeze every approved evidence byte except the self-referential index."""

    actual = current_evidence_paths()
    require(actual == expected_evidence_paths(manifest), "cannot freeze incomplete evidence tree")
    lines = []
    for relative in sorted(actual):
        raw = read_path_bounded(
            EVIDENCE_ROOT / relative,
            manifest["budgets"]["max_record_bytes"],
            f"evidence/{relative}",
        )
        digest = sha256_bytes(raw)
        lines.append(f"{digest}  {relative}\n")
    write_text("hashes/SHA256SUMS", "".join(lines))


def verify_hash_index(manifest: Mapping[str, Any]) -> None:
    """Validate the sorted, complete evidence hash index."""

    require(HASH_PATH.is_file() and not HASH_PATH.is_symlink(), "missing evidence hash index")
    raw_bytes = read_path_bounded(
        HASH_PATH,
        manifest["budgets"]["max_record_bytes"],
        "evidence/hashes/SHA256SUMS",
    )
    try:
        raw = raw_bytes.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError("non-UTF-8 hash index") from error
    require(raw.endswith("\n"), "hash index must end with newline")
    entries: dict[str, str] = {}
    lines = raw.splitlines()
    require(lines == sorted(lines, key=lambda line: line[66:]), "hash index is not path-sorted")
    for line in lines:
        require(re.fullmatch(r"[0-9a-f]{64}  [^\n]+", line) is not None, "invalid hash row")
        digest, relative = line.split("  ", 1)
        require(relative not in entries, f"duplicate hash path: {relative}")
        entries[relative] = digest
    require(set(entries) == expected_evidence_paths(manifest), "hash index path inventory mismatch")
    for relative, expected in entries.items():
        evidence_raw = read_path_bounded(
            EVIDENCE_ROOT / relative,
            manifest["budgets"]["max_record_bytes"],
            f"evidence/{relative}",
        )
        actual = sha256_bytes(evidence_raw)
        require(actual == expected, f"evidence hash mismatch: {relative}")


def validate_static(manifest: Mapping[str, Any], *, require_hashes: bool) -> None:
    """Run all non-command validations."""

    validate_toolchain(manifest)
    validate_repository_identity(manifest)
    validate_sources(manifest)
    validate_finite_field(manifest["finite"]["outer17"])
    validate_finite_field(manifest["finite"]["outer41"])
    validate_payloads(manifest)
    validate_theorems(manifest)
    validate_crosswalk(manifest)
    if require_hashes:
        verify_hash_index(manifest)
        for command in manifest["commands"]:
            validate_record(command, manifest)
        hostile = read_text(
            "papers/shifted-square-17-41/evidence/assurance/hostile-output.txt",
            manifest["budgets"]["max_record_bytes"],
        )
        require(hostile == hostile_report(manifest), "hostile assurance record mismatch")
        integrity = read_text(
            "papers/shifted-square-17-41/evidence/assurance/integrity-output.txt",
            manifest["budgets"]["max_record_bytes"],
        )
        require(integrity == privacy_and_integrity_report(manifest), "integrity record mismatch")


def record_all(manifest: Mapping[str, Any]) -> None:
    """Execute, capture, and freeze every bounded command."""

    validate_toolchain(manifest)
    validate_repository_identity(manifest)
    validate_sources(manifest)
    validate_finite_field(manifest["finite"]["outer17"])
    validate_finite_field(manifest["finite"]["outer41"])
    validate_payloads(manifest)
    validate_theorems(manifest)
    validate_crosswalk(manifest)
    deadline = time.monotonic() + manifest["budgets"]["total_seconds"]
    for command in manifest["commands"]:
        record = execute_command(command, manifest, deadline)
        write_record(command["record"], record)
        print(f"{command['id']}: OK")
    write_text("assurance/hostile-output.txt", hostile_report(manifest))
    write_text("assurance/integrity-output.txt", privacy_and_integrity_report(manifest))
    write_hash_index(manifest)
    verify_hash_index(manifest)


def rerun_all(manifest: Mapping[str, Any]) -> None:
    """Verify frozen bytes, then rerun all semantic command oracles."""

    validate_static(manifest, require_hashes=True)
    deadline = time.monotonic() + manifest["budgets"]["total_seconds"]
    for command in manifest["commands"]:
        execute_command(command, manifest, deadline)
        print(f"{command['id']}: OK")


def freeze_existing_records(manifest: Mapping[str, Any]) -> None:
    """Freeze already captured records after all commands have succeeded."""

    validate_static(manifest, require_hashes=False)
    for command in manifest["commands"]:
        validate_record(command, manifest)
    write_text("assurance/hostile-output.txt", hostile_report(manifest))
    write_text("assurance/integrity-output.txt", privacy_and_integrity_report(manifest))
    write_hash_index(manifest)
    validate_static(manifest, require_hashes=True)


def parse_args() -> argparse.Namespace:
    """Parse the deliberately narrow evidence interface."""

    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="action", required=True)
    for action in ("record", "run"):
        subparser = subparsers.add_parser(action)
        subparser.add_argument("--full", action="store_true", required=True)
    subparsers.add_parser("verify")
    subparsers.add_parser("hostile")
    subparsers.add_parser("integrity")
    subparsers.add_parser("freeze")
    return parser.parse_args()


def main() -> int:
    """Dispatch the requested fail-closed evidence operation."""

    arguments = parse_args()
    try:
        manifest = load_manifest()
        if arguments.action == "record":
            record_all(manifest)
            print("PAPER1_EVIDENCE_RECORDED_OK")
        elif arguments.action == "run":
            rerun_all(manifest)
            print("PAPER1_EVIDENCE_REPLAY_OK")
        elif arguments.action == "verify":
            validate_static(manifest, require_hashes=True)
            print("PAPER1_EVIDENCE_VERIFY_OK")
        elif arguments.action == "hostile":
            print(hostile_report(manifest), end="")
        elif arguments.action == "integrity":
            print(privacy_and_integrity_report(manifest), end="")
        elif arguments.action == "freeze":
            freeze_existing_records(manifest)
            print("PAPER1_EVIDENCE_HASH_FREEZE_OK")
        else:
            raise EvidenceError("unsupported action")
    except EvidenceError as error:
        print(f"PAPER1_EVIDENCE_FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
