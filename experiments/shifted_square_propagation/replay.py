#!/usr/bin/env python3
"""Replay the bounded arithmetic behind shifted-square propagation.

This trusted-local diagnostic uses only exact Python integers.  It checks a
finite grid of recurrence identities and residue phases; it is not a proof of
the infinite-index theorem and does not change mathematical status.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

SCHEMA = "SHIFTED-SQUARE-PROPAGATION-REPLAY-V2"
MARKER = "SHIFTED_SQUARE_PROPAGATION_OK"
EXPECTED_PATH = Path(__file__).with_name("expected.json")
MAX_EXPECTED_BYTES = 8 * 1024

JsonObject = dict[str, Any]


class ReplayError(RuntimeError):
    """Raised when an exact replay invariant fails."""


def require(condition: bool, message: str) -> None:
    """Fail closed when a replay invariant does not hold."""

    if not condition:
        raise ReplayError(message)


def canonical_json_bytes(value: object) -> bytes:
    """Return the one permitted byte representation of a JSON value."""

    return (
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    )


def sha256_rows(rows: Iterable[tuple[object, ...]]) -> str:
    """Digest a deterministic row stream without retaining its large values."""

    digest = hashlib.sha256()
    for row in rows:
        digest.update(canonical_json_bytes(row))
    return digest.hexdigest()


def lucas_real(a: int, n: int) -> int:
    """Return F_n(a), where F_0=1, F_1=a, F_(j+2)=2*a*F_(j+1)+F_j."""

    require(type(a) is int and a >= 0, "a must be a natural number")
    require(type(n) is int and n >= 0, "n must be a natural number")
    if n == 0:
        return 1
    previous, current = 1, a
    for _ in range(1, n):
        previous, current = current, 2 * a * current + previous
    return current


def lucas_v(p: int, n: int) -> int:
    """Return V_n(p,-1), with V_0=2 and V_1=p."""

    require(type(p) is int and p >= 0, "p must be a natural number")
    require(type(n) is int and n >= 0, "n must be a natural number")
    if n == 0:
        return 2
    previous, current = 2, p
    for _ in range(1, n):
        previous, current = current, p * current + previous
    return current


def lucas_u(p: int, n: int) -> int:
    """Return U_n(p,-1), with U_0=0 and U_1=1."""

    require(type(p) is int and p >= 0, "p must be a natural number")
    require(type(n) is int and n >= 0, "n must be a natural number")
    if n == 0:
        return 0
    previous, current = 0, 1
    for _ in range(1, n):
        previous, current = current, p * current + previous
    return current


def v2(value: int) -> int:
    """Return the exact two-adic exponent, using the Lean convention v2(0)=0."""

    require(type(value) is int and value >= 0, "valuation input must be a natural number")
    exponent = 0
    while value and value % 2 == 0:
        value //= 2
        exponent += 1
    return exponent


def composition_rows() -> Iterable[tuple[int, ...]]:
    """Yield the approved composition grid with both exact coordinates."""

    for a in range(17):
        for m in range(9):
            for n in range(1, 16, 2):
                left = lucas_real(a, m * n)
                right = lucas_real(lucas_real(a, n), m)
                require(left == right, f"composition failed at a={a}, m={m}, n={n}")
                yield a, m, n, left, right


def mod_four_rows() -> Iterable[tuple[int, ...]]:
    """Yield the approved odd-index mod-four phase grid."""

    for a in range(2, 64, 4):
        for n in range(1, 42, 2):
            residue = lucas_real(a, n) % 4
            require(residue == 2, f"mod-four phase failed at a={a}, n={n}")
            yield a, n, residue


def mod_eight_rows() -> Iterable[tuple[int, ...]]:
    """Yield the approved fixed-index mod-eight phase grid."""

    for a in range(6, 64, 8):
        for n in (17, 41):
            residue = lucas_real(a, n) % 8
            require(residue == 6, f"mod-eight phase failed at a={a}, n={n}")
            yield a, n, residue


def even_valuation_rows() -> Iterable[tuple[object, ...]]:
    """Yield exact representative rows for the positive-even valuation theorem."""

    indices = (2, 4, 6, 8, 10, 12, 16, 24)
    for a in (2, 6, 10):
        p = 2 * a
        require(p % 8 == 4, f"P phase failed at a={a}")
        for n in indices:
            f = lucas_real(a, n)
            direct_v = lucas_v(p, n)
            require(direct_v == 2 * f, f"V=2F failed at a={a}, n={n}")
            v_minus_two = direct_v - 2
            f_minus_one = f - 1
            expected = 2 * v2(n) + 1
            observed = v2(f_minus_one)
            require(observed == expected, f"even valuation failed at a={a}, n={n}")
            require(v2(v_minus_two) == expected + 1, f"V valuation failed at a={a}, n={n}")
            yield (
                a,
                p,
                n,
                v2(n),
                str(v_minus_two),
                v2(v_minus_two),
                str(f_minus_one),
                observed,
                expected,
            )


def local_two_rows() -> Iterable[tuple[object, ...]]:
    """Yield the complete four-phase mod-eight classification table."""

    expected_tables = {
        2: (1, 2, 1, 6),
        6: (1, 6, 1, 2),
    }
    expected_codes = {
        (2, 1): "ODD_2ADIC_ADMISSIBLE",
        (2, 3): "ODD_UNIT_CLASS_REJECTION",
        (6, 1): "ODD_UNIT_CLASS_REJECTION",
        (6, 3): "ODD_2ADIC_ADMISSIBLE",
    }
    for a_mod_eight, table in expected_tables.items():
        for n_mod_four, residue in enumerate(table):
            observed = lucas_real(a_mod_eight, n_mod_four) % 8
            require(
                observed == residue,
                f"local table failed at a={a_mod_eight}, n={n_mod_four}",
            )
            if n_mod_four % 2 == 0:
                code = "EVEN_ODD_VALUATION_REJECTION"
            else:
                code = expected_codes[(a_mod_eight, n_mod_four)]
            yield a_mod_eight, n_mod_four, observed, (observed - 1) % 8, code


def build_packet() -> JsonObject:
    """Compute the complete bounded replay packet."""

    composition = list(composition_rows())
    mod_four = list(mod_four_rows())
    mod_eight = list(mod_eight_rows())
    even_valuation = list(even_valuation_rows())
    local_two = list(local_two_rows())
    hostile_left = lucas_real(1, 2 * 2)
    hostile_right = lucas_real(lucas_real(1, 2), 2)
    require(hostile_left == 17, "hostile control left coordinate changed")
    require(hostile_right == 19, "hostile control right coordinate changed")
    require(hostile_left != hostile_right, "hostile even-inner control did not fail")

    formula_left_bad = lucas_v(4, 2) - 2
    formula_right_bad = (4**2 + 4) * lucas_u(4, 1) ** 2
    formula_left_good = lucas_v(4, 4) - 2
    formula_right_good = (4**2 + 4) * lucas_u(4, 2) ** 2
    require(formula_left_bad == 16, "guarded formula left control changed")
    require(formula_right_bad == 20, "guarded formula false-right control changed")
    require(formula_left_bad != formula_right_bad, "guarded formula hostile control did not fail")
    require(formula_left_good == formula_right_good == 320, "guarded formula valid control failed")

    witnesses = {
        "cross_phase_a2_n3": {"f": str(lucas_real(2, 3)), "f_minus_one_mod_8": 5},
        "cross_phase_a6_n5": {"f": str(lucas_real(6, 5)), "f_minus_one_mod_8": 5},
        "surviving_a2_n5": {
            "f": str(lucas_real(2, 5)),
            "f_minus_one": str(lucas_real(2, 5) - 1),
            "f_minus_one_mod_8": 1,
            "integer_square_bracket": [26, 27],
        },
    }
    require(witnesses["cross_phase_a2_n3"]["f"] == "38", "a=2,n=3 witness changed")
    require(witnesses["cross_phase_a6_n5"]["f"] == "128766", "a=6,n=5 witness changed")
    require(witnesses["surviving_a2_n5"]["f"] == "682", "a=2,n=5 witness changed")
    require(lucas_real(2, 3) - 1 == 37, "a=2,n=3 shifted witness changed")
    require(lucas_real(6, 5) - 1 == 128765, "a=6,n=5 shifted witness changed")
    require(26**2 < lucas_real(2, 5) - 1 < 27**2, "surviving witness bracket changed")

    result: JsonObject = {
        "arithmetic": {
            "backend": "python-int",
            "exact_arbitrary_precision": True,
            "randomness": False,
        },
        "composition": {
            "a_bounds_inclusive": [0, 16],
            "all_equal": True,
            "cases": len(composition),
            "m_bounds_inclusive": [0, 8],
            "odd_n_bounds_inclusive": [1, 15],
            "rows_sha256": sha256_rows(composition),
        },
        "mod_four": {
            "a_bounds_inclusive": [0, 63],
            "a_residue": 2,
            "all_residues_equal_two": True,
            "cases": len(mod_four),
            "modulus": 4,
            "odd_n_bounds_inclusive": [1, 41],
            "rows_sha256": sha256_rows(mod_four),
        },
        "mod_eight": {
            "a_bounds_inclusive": [0, 63],
            "a_residue": 6,
            "all_residues_equal_six": True,
            "cases": len(mod_eight),
            "indices": [17, 41],
            "modulus": 8,
            "rows_sha256": sha256_rows(mod_eight),
        },
        "even_valuation": {
            "all_rows_match": True,
            "indices": [2, 4, 6, 8, 10, 12, 16, 24],
            "p_mod_16_phases": [
                {"a": 2, "p": 4, "p_mod_16": 4},
                {"a": 6, "p": 12, "p_mod_16": 12},
                {"a": 10, "p": 20, "p_mod_16": 4},
            ],
            "row_schema": [
                "a",
                "p",
                "n",
                "v2_n",
                "v_n_minus_two",
                "v2_v_n_minus_two",
                "f_n_minus_one",
                "observed_v2_f_n_minus_one",
                "expected_v2_f_n_minus_one",
            ],
            "rows": [list(row) for row in even_valuation],
            "rows_sha256": sha256_rows(even_valuation),
            "theorem_formula": "v2(F_n(A)-1)=2*v2(n)+1 for A=2 mod 4 and positive even n",
        },
        "local_two": {
            "classification_rows": [
                {
                    "a_mod_8": a_mod_eight,
                    "code": code,
                    "f_n_mod_8": residue,
                    "n_mod_4": n_mod_four,
                    "shifted_mod_8": shifted,
                }
                for a_mod_eight, n_mod_four, residue, shifted, code in local_two
            ],
            "complete_tables": {
                "a_mod_8_2": [1, 2, 1, 6],
                "a_mod_8_6": [1, 6, 1, 2],
            },
            "cross_phase_square_class": 5,
            "surviving_unit_square_class": 1,
        },
        "hostile_controls": {
            "guarded_u_formula": {
                "false_case": {
                    "m": 1,
                    "n": 2,
                    "p": 4,
                    "right": formula_right_bad,
                    "v_n_minus_two": formula_left_bad,
                },
                "identity_only_when_m_even": True,
                "valid_case": {
                    "m": 2,
                    "n": 4,
                    "p": 4,
                    "right": formula_right_good,
                    "v_n_minus_two": formula_left_good,
                },
            },
            "n_zero": {
                "a": 2,
                "f_n_minus_one": str(lucas_real(2, 0) - 1),
                "is_divisible_by_17": True,
                "is_divisible_by_41": True,
                "n": 0,
                "v2_convention": v2(lucas_real(2, 0) - 1),
            },
            "phase_boundary_n2": [
                {
                    "a": a,
                    "a_mod_4": a % 4,
                    "v2_f_n_minus_one": v2(lucas_real(a, 2) - 1),
                }
                for a in (0, 1, 3, 4)
            ],
            "wrong_phase_n2": {
                "a": 0,
                "a_mod_4": 0,
                "observed_v2": v2(lucas_real(0, 2) - 1),
            },
        },
        "hostile_even_inner": {
            "a": 1,
            "composition_fails": True,
            "direct_f_4": hostile_left,
            "inner_n": 2,
            "outer_m": 2,
            "nested_f_2_f_2": hostile_right,
        },
        "nonclaims": {
            "bounded_replay_is_proof": False,
            "canonical_status_changed": False,
            "even_inner_composition": False,
            "terminal_count": "1/4",
            "uniform_prime_index_theorem": False,
            "odd_2adic_admissible_implies_global_square": False,
            "source_terminal_scope_enlarged": False,
        },
        "witnesses": witnesses,
    }
    require(len(composition) == 1_224, "composition case count changed")
    require(len(mod_four) == 336, "mod-four case count changed")
    require(len(mod_eight) == 16, "mod-eight case count changed")
    require(len(even_valuation) == 24, "even valuation case count changed")
    require(len(local_two) == 8, "local-two classification count changed")
    packet: JsonObject = {
        "marker": MARKER,
        "result": result,
        "result_sha256": hashlib.sha256(canonical_json_bytes(result)).hexdigest(),
        "schema": SCHEMA,
    }
    require(len(canonical_json_bytes(packet)) <= MAX_EXPECTED_BYTES, "packet exceeds 8 KiB")
    return packet


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> JsonObject:
    """Reject duplicate keys while decoding the maintained fixture."""

    result: JsonObject = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def load_expected_bytes(path: Path) -> bytes:
    """Load the bounded canonical bytes of the maintained expected packet."""

    try:
        resolved_path = path.resolve(strict=True)
        maintained_path = EXPECTED_PATH.resolve(strict=True)
        require(
            resolved_path == maintained_path,
            "expected path must resolve to the maintained adjacent fixture",
        )
        with resolved_path.open("rb") as handle:
            raw = handle.read(MAX_EXPECTED_BYTES + 1)
    except OSError as error:
        raise ReplayError(f"cannot read {path}: {error}") from error
    require(len(raw) <= MAX_EXPECTED_BYTES, "expected packet exceeds 8 KiB")
    try:
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReplayError(f"cannot decode {path}: {error}") from error
    require(isinstance(value, dict), "expected packet must be a JSON object")
    require(raw == canonical_json_bytes(value), "expected packet is not canonical JSON")
    return raw


def parse_args() -> argparse.Namespace:
    """Parse the narrow trusted-local replay interface."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--expected",
        type=Path,
        default=EXPECTED_PATH,
        help="canonical expected packet to compare (default: adjacent expected.json)",
    )
    parser.add_argument(
        "--emit-packet",
        action="store_true",
        help="emit the computed canonical packet without reading expected.json",
    )
    return parser.parse_args()


def main() -> int:
    """Run the replay and return a shell-friendly status."""

    arguments = parse_args()
    try:
        packet = build_packet()
        if arguments.emit_packet:
            sys.stdout.buffer.write(canonical_json_bytes(packet))
            return 0
        expected_bytes = load_expected_bytes(arguments.expected)
        require(
            canonical_json_bytes(packet) == expected_bytes,
            "computed packet bytes differ from expected packet",
        )
    except ReplayError as error:
        print(f"SHIFTED_SQUARE_PROPAGATION_FAIL: {error}", file=sys.stderr)
        return 1

    summary = {
        "composition_cases": packet["result"]["composition"]["cases"],
        "even_valuation_cases": len(packet["result"]["even_valuation"]["rows"]),
        "local_two_cases": len(packet["result"]["local_two"]["classification_rows"]),
        "mod_eight_cases": packet["result"]["mod_eight"]["cases"],
        "mod_four_cases": packet["result"]["mod_four"]["cases"],
        "result_sha256": packet["result_sha256"],
        "schema": packet["schema"],
    }
    print(json.dumps(summary, ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    print(MARKER)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
