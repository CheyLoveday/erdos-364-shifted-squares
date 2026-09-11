#!/usr/bin/env python3
"""Fail-closed SS41 two-level Jacobi certificate.

The replay reconstructs the fixed-p=41 polynomial pair from the banked
Dickson unit, generates two primitive pseudo-remainder chains, and emits the
two endpoint matrices audited for a possible Lean proof.  It proves the
global determinant-minus-16 reduction exactly, then records that the proposed
determinant-245 finisher introduces new 3- and 11-support.  Finite plug-back
checks are controls only; this is a readiness/obstruction certificate, not an
SS41 proof or a packet closure.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import tempfile
from typing import Iterable


SCHEMA = "sm2.outer41-jacobi-certificate.v1"
SOURCE = Path("experiments/sm2_four_translate/interpolation/outer41_verify.gp")
SOURCE_SHA256 = "59ac1ef75d1d5e953aec81943a28bdb6b0656721de7947506704ac498c7bb560"
DEFAULT_CERTIFICATE = Path(__file__).with_suffix(".json")
UNIT_DICKSON = (
    -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
    3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
    -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5,
)
UNIT_DICKSON_17 = (-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1)
PLUG_BACK_BOUND = 10_000
Poly = tuple[int, ...]
FracPoly = tuple[Fraction, ...]


class CertificateError(RuntimeError):
    """A fail-closed construction or replay error."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


def trim(values: Iterable[int]) -> Poly:
    out = list(values)
    require(out and all(type(value) is int for value in out), "integer polynomial")
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def add(left: Poly, right: Poly) -> Poly:
    size = max(len(left), len(right))
    return trim(
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(size)
    )


def neg(poly: Poly) -> Poly:
    return trim(-value for value in poly)


def sub(left: Poly, right: Poly) -> Poly:
    return add(left, neg(right))


def scale(poly: Poly, scalar: int) -> Poly:
    require(type(scalar) is int, "integer scalar")
    return trim(scalar * value for value in poly)


def shift(poly: Poly, amount: int) -> Poly:
    require(type(amount) is int and amount >= 0, "monomial shift")
    return poly if poly == (0,) else (0,) * amount + poly


def mul(left: Poly, right: Poly) -> Poly:
    if left == (0,) or right == (0,):
        return (0,)
    out = [0] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            out[left_index + right_index] += left_value * right_value
    return trim(out)


def evaluate(poly: Poly, value: int) -> int:
    result = 0
    for coefficient in reversed(poly):
        result = result * value + coefficient
    return result


def compose_affine(poly: Poly, slope: int, intercept: int) -> Poly:
    result: Poly = (0,)
    affine = (intercept, slope)
    for coefficient in reversed(poly):
        result = add(mul(result, affine), (coefficient,))
    return result


def content(poly: Poly) -> int:
    result = 0
    for coefficient in poly:
        result = math.gcd(result, abs(coefficient))
    return result


def exact_div(poly: Poly, divisor: int) -> Poly:
    require(divisor != 0 and all(value % divisor == 0 for value in poly),
            "exact polynomial division")
    return trim(value // divisor for value in poly)


def primitive_positive(poly: Poly) -> Poly:
    require(poly != (0,), "nonzero primitive part")
    result = exact_div(poly, content(poly))
    return neg(result) if result[-1] < 0 else result


def pseudo_division(dividend: Poly, divisor: Poly) -> tuple[Poly, Poly]:
    require(divisor != (0,) and len(dividend) >= len(divisor), "pseudo-division")
    leading = divisor[-1]
    quotient: Poly = (0,)
    remainder = dividend
    steps_left = len(dividend) - len(divisor) + 1
    while remainder != (0,) and len(remainder) >= len(divisor):
        exponent = len(remainder) - len(divisor)
        coefficient = remainder[-1]
        quotient = add(scale(quotient, leading), shift((coefficient,), exponent))
        remainder = sub(
            scale(remainder, leading),
            scale(shift(divisor, exponent), coefficient),
        )
        steps_left -= 1
    require(steps_left >= 0, "pseudo-division step count")
    if steps_left:
        multiplier = leading ** steps_left
        quotient = scale(quotient, multiplier)
        remainder = scale(remainder, multiplier)
    return quotient, remainder


def primitive_prs(first: Poly, second: Poly) -> tuple[Poly, ...]:
    rows = [first, second]
    while True:
        _, remainder = pseudo_division(rows[-2], rows[-1])
        if remainder == (0,):
            break
        rows.append(primitive_positive(remainder))
    return tuple(rows)


def dickson_rows(limit: int) -> tuple[Poly, ...]:
    rows: list[Poly] = [(2,), (0, 1)]
    for _ in range(2, limit + 1):
        rows.append(add(shift(rows[-1], 1), rows[-2]))
    return tuple(rows)


def lucas_real(index: int) -> Poly:
    previous: Poly = (1,)
    current: Poly = (0, 1)
    for _ in range(2, index + 1):
        previous, current = current, add(mul((0, 2), current), previous)
    return current


def build_source_pair() -> tuple[Poly, Poly]:
    dickson = dickson_rows(41)
    unit: Poly = (UNIT_DICKSON[0],)
    for coefficient, row in zip(UNIT_DICKSON[1:], dickson[1:41], strict=True):
        unit = add(unit, scale(row, coefficient))
    half_norm = sub(lucas_real(41), (1,))
    positive_unit = neg(compose_affine(unit, 2, 0))
    require((len(half_norm) - 1, len(positive_unit) - 1) == (41, 40),
            "source degrees")
    return half_norm, positive_unit


def normalized_phase_rows() -> tuple[Poly, ...]:
    rows = primitive_prs(*build_source_pair())
    require(tuple(len(row) - 1 for row in rows) ==
            tuple(range(41, 1, -1)) + (0,), "source PRS degrees")
    normalized = []
    for index, row in enumerate(rows):
        phase_row = compose_affine(row, 8, 10)
        if index in (5, 21):
            phase_row = exact_div(phase_row, 2)
        require(phase_row[0] > 0 and all(value >= 0 for value in phase_row),
                f"source row positivity {index}")
        require(phase_row[0] % 2 == 1 and
                all(value % 2 == 0 for value in phase_row[1:]),
                f"source row oddness {index}")
        normalized.append(phase_row)
    return tuple(normalized)


def adjacent_relations(raw_rows: tuple[Poly, ...], divisors: tuple[int, ...],
                       slope: int, intercept: int) -> tuple[dict, ...]:
    relations = []
    for index in range(len(raw_rows) - 2):
        quotient, remainder = pseudo_division(raw_rows[index], raw_rows[index + 1])
        sign = 1 if remainder[-1] > 0 else -1
        left = raw_rows[index + 1][-1] ** 2 * divisors[index]
        right = sign * content(remainder) * divisors[index + 2]
        quotient = scale(compose_affine(quotient, slope, intercept),
                         divisors[index + 1])
        common = math.gcd(abs(left), abs(right))
        for coefficient in quotient:
            common = math.gcd(common, abs(coefficient))
        left //= common
        right //= common
        quotient = exact_div(quotient, common)
        relations.append({"left": left, "quotient": quotient, "right": right})
    return tuple(relations)


def ftrim(values: Iterable[Fraction]) -> FracPoly:
    out = list(values)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def fadd(left: FracPoly, right: FracPoly) -> FracPoly:
    size = max(len(left), len(right))
    return ftrim(
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(size)
    )


def fscale(poly: FracPoly, scalar: Fraction) -> FracPoly:
    return ftrim(scalar * value for value in poly)


def fmul(left: FracPoly, right: FracPoly) -> FracPoly:
    out = [Fraction(0)] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            out[left_index + right_index] += left_value * right_value
    return ftrim(out)


def endpoint_vectors(relations: tuple[dict, ...]) -> tuple[tuple[FracPoly, FracPoly], ...]:
    vectors: list[tuple[FracPoly, FracPoly]] = [
        ((Fraction(1),), (Fraction(0),)),
        ((Fraction(0),), (Fraction(1),)),
    ]
    for relation in relations:
        quotient = tuple(Fraction(value) for value in relation["quotient"])
        reciprocal = Fraction(1, relation["right"])
        next_left = fscale(fadd(
            fscale(vectors[-2][0], relation["left"]),
            fscale(fmul(quotient, vectors[-1][0]), -1)), reciprocal)
        next_right = fscale(fadd(
            fscale(vectors[-2][1], relation["left"]),
            fscale(fmul(quotient, vectors[-1][1]), -1)), reciprocal)
        vectors.append((next_left, next_right))
    return tuple(vectors)


def integral_row(vector: tuple[FracPoly, FracPoly]) -> tuple[int, Poly, Poly]:
    denominator = 1
    for poly in vector:
        for value in poly:
            denominator = math.lcm(denominator, value.denominator)
    integer_polys = [tuple(int(value * denominator) for value in poly)
                     for poly in vector]
    common = denominator
    for poly in integer_polys:
        for value in poly:
            common = math.gcd(common, abs(value))
    return (denominator // common,
            trim(value // common for value in integer_polys[0]),
            trim(value // common for value in integer_polys[1]))


def determinant(first: tuple[Poly, Poly], second: tuple[Poly, Poly]) -> Poly:
    return sub(mul(first[0], second[1]), mul(first[1], second[0]))


def verify_endpoint(rows: tuple[Poly, ...], relations: tuple[dict, ...],
                    first_index: int, second_index: int) -> dict:
    vectors = endpoint_vectors(relations)
    first_scale, a, b = integral_row(vectors[first_index])
    second_scale, c, d = integral_row(vectors[second_index])
    require(scale(rows[first_index], first_scale) ==
            add(mul(a, rows[0]), mul(b, rows[1])), "endpoint first identity")
    require(scale(rows[second_index], second_scale) ==
            add(mul(c, rows[0]), mul(d, rows[1])), "endpoint second identity")
    det = determinant((a, b), (c, d))
    require(len(det) == 1, "constant endpoint determinant")
    return {"indices": (first_index, second_index),
            "scales": (first_scale, second_scale),
            "matrix": ((a, b), (c, d)), "determinant": det[0]}


def bareiss_determinant(matrix: list[list[int]]) -> int:
    size = len(matrix)
    data = [row[:] for row in matrix]
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        pivot_row = next((row for row in range(pivot_index, size)
                          if data[row][pivot_index] != 0), None)
        require(pivot_row is not None, "Bareiss pivot")
        if pivot_row != pivot_index:
            data[pivot_index], data[pivot_row] = data[pivot_row], data[pivot_index]
            sign = -sign
        pivot = data[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for column in range(pivot_index + 1, size):
                numerator = (data[row][column] * pivot
                             - data[row][pivot_index] * data[pivot_index][column])
                require(numerator % previous == 0, "Bareiss exact division")
                data[row][column] = numerator // previous
            data[row][pivot_index] = 0
        previous = pivot
    return sign * data[-1][-1]


def resultant(first: Poly, second: Poly) -> int:
    m = len(first) - 1
    n = len(second) - 1
    size = m + n
    matrix = [[0] * size for _ in range(size)]
    first_desc = list(reversed(first))
    second_desc = list(reversed(second))
    for row in range(n):
        matrix[row][row:row + m + 1] = first_desc
    for row in range(m):
        matrix[n + row][row:row + n + 1] = second_desc
    return bareiss_determinant(matrix)


def jacobi(numerator: int, denominator: int) -> int:
    require(denominator > 0 and denominator % 2 == 1, "Jacobi denominator")
    numerator %= denominator
    result = 1
    while numerator:
        while numerator % 2 == 0:
            numerator //= 2
            if denominator % 8 in (3, 5):
                result = -result
        numerator, denominator = denominator, numerator
        if numerator % 4 == denominator % 4 == 3:
            result = -result
        numerator %= denominator
    return result if denominator == 1 else 0


def roots_mod(poly: Poly, modulus: int) -> list[int]:
    return [value for value in range(modulus) if evaluate(poly, value) % modulus == 0]


def common_roots_mod(first: Poly, second: Poly, modulus: int) -> list[int]:
    return [value for value in range(modulus)
            if evaluate(first, value) % modulus == 0
            and evaluate(second, value) % modulus == 0]


def p17_control() -> dict:
    dickson = dickson_rows(17)
    unit: Poly = (UNIT_DICKSON_17[0],)
    for coefficient, row in zip(UNIT_DICKSON_17[1:], dickson[1:15], strict=True):
        unit = add(unit, scale(row, coefficient))
    half_norm = sub(lucas_real(17), (1,))
    detector = compose_affine(unit, 2, 0)
    control_resultant = resultant(half_norm, detector)
    require(abs(control_resultant) == 2 ** 224, "p17 scaled resultant")
    reference_half_norm = evaluate(half_norm, 2)
    reference_detector = evaluate(detector, 2)
    require(reference_half_norm % 8 == 1 and
            jacobi(reference_detector, reference_half_norm) == -1,
            "p17 reference character")
    for parameter in range(128):
        value = 8 * parameter + 2
        require(jacobi(evaluate(detector, value), evaluate(half_norm, value)) == -1,
                "p17 bounded character control")
    return {
        "dickson_coefficients": UNIT_DICKSON_17,
        "scaled_resultant_abs": abs(control_resultant),
        "scaled_resultant_factorization": ((2, 224),),
        "reference_A": 2,
        "reference_half_norm": reference_half_norm,
        "reference_detector": reference_detector,
        "reference_jacobi": -1,
        "bounded_phase_checks": 128,
        "claim": "exact_source_and_reference_control; bounded_phase_is_diagnostic",
    }


def encode(value: object) -> object:
    if type(value) is int:
        return str(value)
    if isinstance(value, tuple) or isinstance(value, list):
        return [encode(item) for item in value]
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    return value


def canonical_bytes(payload: dict) -> bytes:
    return (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()


def construct_payload() -> dict:
    require(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256,
            "source verifier hash")
    source_raw = primitive_prs(*build_source_pair())
    source_divisors = tuple(2 if index in (5, 21) else 1
                            for index in range(len(source_raw)))
    source_rows = normalized_phase_rows()
    source_relations = adjacent_relations(source_raw, source_divisors, 8, 10)
    source_endpoint = verify_endpoint(source_rows, source_relations, 39, 40)
    require(source_endpoint["scales"] == (1, 1), "source endpoint scales")
    require(source_endpoint["determinant"] == -16, "source endpoint determinant")
    ((source_a, source_b), (source_c, source_d)) = source_endpoint["matrix"]
    alpha = exact_div(source_a, 2)
    beta = neg(source_b)
    gamma = exact_div(source_c, 2)
    delta = neg(source_d)
    require(beta != (0,) and delta != (0,), "source endpoint orientation")
    for name, poly in (("alpha", alpha), ("beta", beta),
                       ("gamma", gamma), ("delta", delta)):
        require(poly[0] > 0 and all(value >= 0 for value in poly),
                f"{name} positivity")
        require(poly[0] % 8 == 7 and all(value % 8 == 0 for value in poly[1:]),
                f"{name} phase")
    require(sub(mul(beta, gamma), mul(alpha, delta)) == (-8,),
            "source reduced determinant")
    boundary_q0 = evaluate(source_rows[0], -1)
    boundary_q1 = evaluate(source_rows[1], -1)
    require((boundary_q0, boundary_q1) == (
        25377553679502347277411601,
        43956715453803235217163523,
    ), "p41 A=2 boundary values")
    require((boundary_q0 % 8, boundary_q1 % 8,
             jacobi(boundary_q1, boundary_q0)) == (1, 3, -1),
            "p41 A=2 boundary character")

    coefficient_raw = primitive_prs(gamma, alpha)
    require(len(coefficient_raw) == 39, "coefficient PRS length")
    require(coefficient_raw[-2] == (17, 14) and coefficient_raw[-1] == (1,),
            "coefficient terminal rows")
    coefficient_divisors = (1,) * len(coefficient_raw)
    coefficient_relations = adjacent_relations(
        coefficient_raw, coefficient_divisors, 1, 0)
    coefficient_endpoint = verify_endpoint(
        coefficient_raw, coefficient_relations, 37, 38)
    require(coefficient_endpoint["scales"] == (800, 5),
            "coefficient endpoint scales")
    require(coefficient_endpoint["determinant"] == 245,
            "coefficient endpoint determinant")
    ((terminal_a, terminal_b_signed),
     (terminal_c_signed, terminal_d_twice)) = coefficient_endpoint["matrix"]
    terminal_b = neg(terminal_b_signed)
    terminal_c = neg(terminal_c_signed)
    terminal_d = exact_div(terminal_d_twice, 2)
    terminal_l = coefficient_raw[-2]
    require(scale(terminal_l, 800) ==
            sub(mul(terminal_a, gamma), mul(terminal_b, alpha)),
            "oriented coefficient first identity")
    require((5,) == sub(scale(mul(terminal_d, alpha), 2),
                        mul(terminal_c, gamma)),
            "oriented coefficient second identity")
    require(sub(scale(mul(terminal_a, terminal_d), 2),
                mul(terminal_b, terminal_c)) == (245,),
            "oriented coefficient determinant")
    expected_phases = {
        "X": (7, 7), "Y": (7, 7), "L": (1, 7),
        "A": (7, 7), "B": (7, 7), "C": (3, 7), "D": (3, 5),
    }
    terminal_polys = {
        "X": gamma, "Y": alpha, "L": terminal_l,
        "A": terminal_a, "B": terminal_b,
        "C": terminal_c, "D": terminal_d,
    }
    for name, poly in terminal_polys.items():
        require(poly[0] > 0 and all(value >= 0 for value in poly),
                f"terminal {name} positivity")
    phases = {name: (evaluate(poly, 0) % 8, evaluate(poly, 1) % 8)
              for name, poly in terminal_polys.items()}
    require(phases == expected_phases, "terminal parity phases")
    roots_five = {name: roots_mod(poly, 5)
                  for name, poly in terminal_polys.items()}
    roots_seven = {name: roots_mod(poly, 7)
                   for name, poly in terminal_polys.items()}
    require(roots_five == {
        "X": [4], "Y": [0, 2], "L": [2], "A": [0, 2],
        "B": [4], "C": [0, 2, 4], "D": [4],
    }, "terminal roots mod five")
    require(roots_seven == {
        "X": [1], "Y": [], "L": [], "A": [5],
        "B": [], "C": [5], "D": [],
    }, "terminal roots mod seven")
    common_ac = {
        "mod_5": common_roots_mod(terminal_a, terminal_c, 5),
        "mod_25": common_roots_mod(terminal_a, terminal_c, 25),
        "mod_7": common_roots_mod(terminal_a, terminal_c, 7),
        "mod_49": common_roots_mod(terminal_a, terminal_c, 49),
        "mod_343": common_roots_mod(terminal_a, terminal_c, 343),
    }
    require(common_ac == {
        "mod_5": [0, 2], "mod_25": [], "mod_7": [5],
        "mod_49": [26], "mod_343": [],
    }, "terminal A,C lifts")
    exceptional_five = {
        name: evaluate(poly, 4) % 25 for name, poly in terminal_polys.items()
    }
    require(exceptional_five == {
        "X": 20, "Y": 1, "L": 23, "A": 24,
        "B": 5, "C": 5, "D": 15,
    }, "terminal exceptional five class")
    coefficient_resultant = resultant(alpha, gamma)
    require(abs(coefficient_resultant) == 2 ** 5735 * 5 ** 76,
            "coefficient resultant")
    require(roots_mod(alpha, 5) == [0, 2] and roots_mod(gamma, 5) == [4],
            "coefficient disjoint mod-five roots")
    terminal_resultant = resultant(terminal_a, terminal_b)
    require(abs(terminal_resultant) == 2 ** 5075 * 3 ** 72 * 11 ** 144,
            "terminal coefficient obstruction resultant")
    control_17 = p17_control()

    digest = hashlib.sha256()
    main_failures = 0
    coefficient_failures = 0
    for parameter in range(PLUG_BACK_BOUND):
        values = [evaluate(row, parameter) for row in source_rows]
        alpha_value = evaluate(alpha, parameter)
        gamma_value = evaluate(gamma, parameter)
        require(math.gcd(values[0], values[1]) == 1, "source value coprimality")
        require(math.gcd(alpha_value, gamma_value) == 1,
                "coefficient value coprimality")
        source_symbol = jacobi(values[1], values[0])
        coefficient_symbol = jacobi(alpha_value, gamma_value)
        main_failures += int(source_symbol != -coefficient_symbol)
        coefficient_failures += int(coefficient_symbol != 1)
        digest.update(f"{parameter}:{source_symbol}:{coefficient_symbol}\n".encode())
    require(main_failures == 0, "global transfer plug-back")
    require(coefficient_failures == 0, "coefficient target plug-back")

    payload = {
        "schema": SCHEMA,
        "claim_ceiling": "two_level_exact_certificate_not_lean_or_packet_closure",
        "upstream": {"path": str(SOURCE), "sha256": SOURCE_SHA256},
        "p17_control": encode(control_17),
        "normalization": {"A": "8*j+10", "domain": "j>=0",
                          "boundary_A": "2", "divided_rows": ["5", "21"]},
        "source_chain": {
            "row_count": len(source_rows),
            "degrees": [len(row) - 1 for row in source_rows],
            "rows_sha256": hashlib.sha256(canonical_bytes(
                {"rows": encode(source_rows)})).hexdigest(),
            "endpoint": encode(source_endpoint),
            "alpha": encode(alpha), "beta": encode(beta),
            "gamma": encode(gamma), "delta": encode(delta),
            "transfer": "J(Q1,Q0)=-J(alpha,gamma)",
            "boundary_A_2": {
                "Q0": str(boundary_q0), "Q1": str(boundary_q1),
                "Q0_mod_8": "1", "Q1_mod_8": "3", "jacobi": "-1",
            },
        },
        "coefficient_chain": {
            "row_count": len(coefficient_raw),
            "degrees": [len(row) - 1 for row in coefficient_raw],
            "rows_sha256": hashlib.sha256(canonical_bytes(
                {"rows": encode(coefficient_raw)})).hexdigest(),
            "terminal_rows": encode(coefficient_raw[-2:]),
            "endpoint": encode(coefficient_endpoint),
            "resultant_abs": str(abs(coefficient_resultant)),
            "resultant_factorization": [["2", "5735"], ["5", "76"]],
            "alpha_roots_mod_5": ["0", "2"],
            "gamma_roots_mod_5": ["4"],
            "target": "J(alpha(j),gamma(j))=1",
            "terminal_orientation": {
                "identities": ["800*L=A*X-B*Y", "5=2*D*Y-C*X"],
                "determinant": "2*A*D-B*C=245",
                "polynomials": encode(terminal_polys),
                "phases_even_odd_mod_8": encode(phases),
                "roots_mod_5": encode(roots_five),
                "roots_mod_7": encode(roots_seven),
                "common_A_C_lifts": encode(common_ac),
                "exceptional_j_4_mod_25": encode(exceptional_five),
            },
            "terminal_obstruction": {
                "resultant_A_B_abs": str(abs(terminal_resultant)),
                "resultant_A_B_factorization":
                    [["2", "5075"], ["3", "72"], ["11", "144"]],
                "conclusion":
                    "the determinant-245 transfer does not close with 5/7 support",
            },
        },
        "proof_dag": [
            {"id": "L1", "kind": "PrimitivePRS", "status": "exact"},
            {"id": "L2", "kind": "GlobalBezoutDetMinus16", "status": "exact"},
            {"id": "L3", "kind": "DyadicJacobiTransfer", "status": "human_exact"},
            {"id": "L4", "kind": "CoefficientCoprimality", "status": "exact"},
            {"id": "L5", "kind": "CoefficientTerminalDet245", "status": "exact"},
            {"id": "L6", "kind": "FactorSafeFiveSevenTransfer",
             "status": "refuted_by_new_3_11_support"},
            {"id": "L7", "kind": "ShiftedSquareContradiction",
             "status": "blocked_pending_3_11_orientation_or_new_identity"},
        ],
        "downstream_change": {
            "retired": "determinant-245 five/seven-only closure",
            "survives": "global determinant-minus-16 transfer",
            "new_hinge": "control J(A(j),B(j)) with exact 3/11 orientation or cancel it",
            "lean_readiness": "not_ready_for_full_SS41",
        },
        "plug_back": {"bound": str(PLUG_BACK_BOUND),
                      "sha256": digest.hexdigest(),
                      "claim": "diagnostic_only"},
    }
    payload = encode(payload)
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(type(key) is str and key not in result, "unique JSON key")
        result[key] = value
    return result


def reject_number(value: str) -> object:
    raise CertificateError(f"unencoded JSON number: {value}")


def strict_load(path: Path) -> dict:
    raw = path.read_bytes()
    require(len(raw) <= 2_000_000, "certificate size")
    payload = json.loads(raw, object_pairs_hook=unique_object,
                         parse_int=reject_number, parse_float=reject_number,
                         parse_constant=reject_number)
    require(type(payload) is dict and payload.get("schema") == SCHEMA,
            "certificate schema")
    return payload


def verify_certificate(path: Path, expected: dict) -> dict:
    stored = strict_load(path)
    require(path.read_bytes() == canonical_bytes(expected),
            "byte-identical regeneration")
    return stored


def atomic_write(path: Path, data: bytes) -> None:
    target = path.resolve()
    target.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{target.name}.", dir=target.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, target)
    finally:
        if temporary.exists():
            temporary.unlink()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--self-test", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    expected = construct_payload()
    if args.write:
        atomic_write(args.certificate, canonical_bytes(expected))
    stored = verify_certificate(args.certificate, expected)
    if args.self_test:
        corrupted = json.loads(json.dumps(stored))
        corrupted["source_chain"]["alpha"][0] = str(
            int(corrupted["source_chain"]["alpha"][0]) + 1)
        require(canonical_bytes(corrupted) != canonical_bytes(expected),
                "corrupt coefficient control")
        corrupt_alpha = tuple(map(int, corrupted["source_chain"]["alpha"]))
        beta = tuple(map(int, stored["source_chain"]["beta"]))
        gamma = tuple(map(int, stored["source_chain"]["gamma"]))
        delta = tuple(map(int, stored["source_chain"]["delta"]))
        require(sub(mul(beta, gamma), mul(corrupt_alpha, delta)) != (-8,),
                "corrupt coefficient must break reduced determinant")
        wrong_phase_q0 = compose_affine(build_source_pair()[0], 8, 9)
        require(wrong_phase_q0[0] % 2 == 0,
                "wrong affine phase must fail odd-source invariant")
        with tempfile.TemporaryDirectory(prefix="outer41-noncanonical-") as directory:
            pretty_path = Path(directory) / "pretty.json"
            pretty = (json.dumps(expected, sort_keys=True, indent=2) + "\n").encode()
            atomic_write(pretty_path, pretty)
            try:
                verify_certificate(pretty_path, expected)
            except CertificateError as error:
                require(str(error) == "byte-identical regeneration",
                        "noncanonical JSON rejection reason")
            else:
                raise CertificateError("noncanonical JSON accepted")
    print("OUTER41_JACOBI_CERTIFICATE_OK", "source_rows=41",
          "coefficient_rows=39", "stop=terminal-3-11-support")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertificateError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"OUTER41_JACOBI_CERTIFICATE_FAIL: {error}")
        raise SystemExit(1) from error
