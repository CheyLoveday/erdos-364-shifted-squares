#!/usr/bin/env python3
"""Exact replay for the first specialization-safe SS41 Jacobi block.

The replay reconstructs the p=41 Dickson/Lucas polynomials, derives the
first seven primitive pseudo-remainders, proves the grouped block matrix,
and certifies every determinant-prime specialization.  The paired human
handoff proves the Jacobi transfer rule.  This script does not claim a Lean
proof or a complete 41-row Jacobi chain.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import tempfile
from pathlib import Path
from typing import Iterable


SCHEMA = "sm2.outer41-jacobi-block.v1"
DEFAULT_CERTIFICATE = Path(__file__).with_suffix(".json")
SOURCE_VERIFIER = Path("experiments/sm2_four_translate/interpolation/outer41_verify.gp")
SOURCE_VERIFIER_SHA256 = "59ac1ef75d1d5e953aec81943a28bdb6b0656721de7947506704ac498c7bb560"
UNIT_DICKSON = (
    -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
    3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
    -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5,
)
S = 32_459
DETERMINANT_PRIMES = (7, 4_637)
DIRECT_CHECK_COUNT = S

# Coefficients are stored in increasing degree order.
Poly = tuple[int, ...]


class CertificateError(RuntimeError):
    """A fail-closed construction or replay error."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


def trim(values: Iterable[int]) -> Poly:
    out = list(values)
    require(all(type(value) is int for value in out), "non-integer coefficient")
    if not out:
        return (0,)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def degree(poly: Poly) -> int:
    return len(poly) - 1


def is_zero(poly: Poly) -> bool:
    return poly == (0,)


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
    require(type(scalar) is int, "non-integer scalar")
    return trim(scalar * value for value in poly)


def shift(poly: Poly, amount: int) -> Poly:
    require(type(amount) is int and amount >= 0, "invalid monomial shift")
    if is_zero(poly):
        return poly
    return (0,) * amount + poly


def mul(left: Poly, right: Poly) -> Poly:
    if is_zero(left) or is_zero(right):
        return (0,)
    out = [0] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            out[left_index + right_index] += left_value * right_value
    return trim(out)


def evaluate(poly: Poly, value: int) -> int:
    require(type(value) is int, "non-integer evaluation")
    result = 0
    for coefficient in reversed(poly):
        result = result * value + coefficient
    return result


def compose_affine(poly: Poly, slope: int, intercept: int) -> Poly:
    require(type(slope) is int and type(intercept) is int, "invalid affine map")
    affine = (intercept, slope)
    result: Poly = (0,)
    for coefficient in reversed(poly):
        result = add(mul(result, affine), (coefficient,))
    return result


def content(poly: Poly) -> int:
    result = 0
    for coefficient in poly:
        result = math.gcd(result, abs(coefficient))
    return result


def exact_scalar_div(poly: Poly, divisor: int) -> Poly:
    require(type(divisor) is int and divisor != 0, "invalid scalar divisor")
    require(all(value % divisor == 0 for value in poly), "inexact scalar division")
    return trim(value // divisor for value in poly)


def primitive_positive(poly: Poly) -> Poly:
    require(not is_zero(poly), "zero primitive part")
    divisor = content(poly)
    require(divisor > 0, "zero content")
    result = exact_scalar_div(poly, divisor)
    return neg(result) if result[-1] < 0 else result


def pseudo_remainder(dividend: Poly, divisor: Poly) -> Poly:
    require(not is_zero(divisor), "pseudo-remainder by zero")
    require(degree(dividend) >= degree(divisor), "pseudo-remainder degree")
    leading = divisor[-1]
    steps_left = degree(dividend) - degree(divisor) + 1
    remainder = dividend
    while not is_zero(remainder) and degree(remainder) >= degree(divisor):
        exponent = degree(remainder) - degree(divisor)
        coefficient = remainder[-1]
        remainder = sub(
            scale(remainder, leading),
            scale(shift(divisor, exponent), coefficient),
        )
        steps_left -= 1
    require(steps_left >= 0, "pseudo-remainder step underflow")
    return scale(remainder, leading ** steps_left)


def dickson_rows(limit: int) -> tuple[Poly, ...]:
    require(type(limit) is int and limit >= 1, "invalid Dickson limit")
    rows: list[Poly] = [(2,), (0, 1)]
    for _ in range(2, limit + 1):
        rows.append(add(shift(rows[-1], 1), rows[-2]))
    return tuple(rows)


def lucas_real(index: int) -> Poly:
    require(type(index) is int and index >= 1, "invalid Lucas index")
    previous: Poly = (1,)
    current: Poly = (0, 1)
    for _ in range(2, index + 1):
        previous, current = current, add(mul((0, 2), current), previous)
    return current


def build_inputs() -> tuple[Poly, Poly]:
    dickson = dickson_rows(41)
    unit_t: Poly = (UNIT_DICKSON[0],)
    for coefficient, row in zip(UNIT_DICKSON[1:], dickson[1:41], strict=True):
        unit_t = add(unit_t, scale(row, coefficient))
    half_norm = sub(lucas_real(41), (1,))
    positive_unit = neg(compose_affine(unit_t, 2, 0))
    require(degree(half_norm) == 41, "half-norm degree")
    require(degree(positive_unit) == 40, "unit degree")
    require(evaluate(half_norm, 2) == 25_377_553_679_502_347_277_411_601,
            "half-norm boundary")
    require(evaluate(positive_unit, 2) == 43_956_715_453_803_235_217_163_523,
            "unit boundary")
    return half_norm, positive_unit


def first_rows() -> tuple[Poly, ...]:
    first, second = build_inputs()
    rows: list[Poly] = [first, second]
    while len(rows) < 7:
        remainder = pseudo_remainder(rows[-2], rows[-1])
        require(not is_zero(remainder), "premature zero remainder")
        rows.append(primitive_positive(remainder))
    require(tuple(degree(row) for row in rows) == (41, 40, 39, 38, 37, 36, 35),
            "first-row degrees")
    return tuple(rows)


def phase_rows() -> tuple[Poly, ...]:
    """Return Q_i(j), where A=8*j+10 and Q_5=S_5/2."""

    rows = []
    for index, row in enumerate(first_rows()):
        specialized = compose_affine(row, 8, 10)
        if index == 5:
            specialized = exact_scalar_div(specialized, 2)
        require(specialized[0] > 0 and all(value >= 0 for value in specialized),
                f"Q{index} positivity")
        if index != 5:
            require(all(value % 8 == 0 for value in specialized[1:]),
                    f"Q{index} fixed mod-eight class")
        require(specialized[0] % 2 == 1, f"Q{index} parity")
        rows.append(specialized)
    fixed_indices = (0, 1, 2, 3, 4, 6)
    expected_fixed_mod_eight = (1, 3, 3, 7, 5, 7)
    require(tuple(rows[index][0] % 8 for index in fixed_indices)
            == expected_fixed_mod_eight, "fixed phase row residues")
    q5_even = compose_affine(rows[5], 2, 0)
    q5_odd = compose_affine(rows[5], 2, 1)
    require(q5_even[0] % 8 == 1
            and all(value % 8 == 0 for value in q5_even[1:]),
            "Q5 even-phase residue")
    require(q5_odd[0] % 8 == 5
            and all(value % 8 == 0 for value in q5_odd[1:]),
            "Q5 odd-phase residue")
    return tuple(rows)


def row_residue_payload(index: int, row: Poly) -> dict:
    if index == 5:
        return {
            "mod_8": "phase-dependent",
            "phase_mod_8": {"j_even": "1", "j_odd": "5"},
        }
    return {"mod_8": encode_int(row[0] % 8)}


def linear(constant: int, slope: int) -> Poly:
    return (constant, slope)


def verify_adjacent_identities(rows: tuple[Poly, ...]) -> tuple[dict, ...]:
    q0, q1, q2, q3, q4, q5, q6 = rows
    identities = (
        (10, q0, linear(21, 16), q1, 1, q2),
        (49, q1, scale(linear(340, 280), 1), q2, 1, q3),
        (43_923, q2, scale(linear(8_341, 6_776), 8), q3, 245, q4),
        (2_486_929, q3, scale(linear(1_882_609, 1_526_536), 3), q4,
         117_128, q5),
        (1_053_586_681, q4, scale(linear(1_037_603_369, 819_005_488), 8), q5,
         7_460_787, q6),
    )
    encoded = []
    for index, (left_scale, left, quotient, middle, right_scale, right) in enumerate(identities):
        require(scale(left, left_scale) == add(mul(quotient, middle), scale(right, right_scale)),
                f"adjacent identity {index}")
        encoded.append({
            "index": index,
            "left_scale": left_scale,
            "left_row": index,
            "quotient": quotient,
            "middle_row": index + 1,
            "right_scale": right_scale,
            "right_row": index + 2,
        })
    return tuple(encoded)


def block_coefficients() -> tuple[Poly, Poly, Poly, Poly]:
    # These are the exact telescoped coefficients after shifting from
    # A=8*r+2 to A=8*j+10, i.e. r=j+1.
    r: Poly = (1, 1)

    def polynomial(coefficients: tuple[int, ...]) -> Poly:
        result: Poly = (0,)
        power: Poly = (1,)
        for coefficient in coefficients:
            result = add(result, scale(power, coefficient))
            power = mul(power, r)
        return result

    n3 = polynomial((1_234_893, 15_376_256, 65_740_800, 96_890_880))
    n4 = polynomial((712_955, 10_451_080, 59_168_000, 153_630_720, 155_025_408))
    c = scale(polynomial((2_404_585, 37_847_145, 228_615_264, 628_471_040,
                          664_760_320)), 32)
    d = neg(polynomial((44_423_683, 797_293_664, 5_867_790_592,
                        22_132_903_936, 42_813_882_368, 34_035_728_384)))
    return n3, n4, c, d


def verify_block_matrix(rows: tuple[Poly, ...]) -> dict:
    q0, q1, _, _, _, q5, q6 = rows
    n3, n4, c, d = block_coefficients()
    require(scale(q5, 4) == add(mul(neg(n3), q0), mul(n4, q1)),
            "block first row")
    require(q6 == add(mul(c, q0), mul(d, q1)), "block second row")
    determinant = sub(mul(neg(n3), d), mul(n4, c))
    require(determinant == (-(S * S),), "block determinant")
    require(scale(q0, S * S) == add(mul(scale(d, -4), q5), mul(n4, q6)),
            "block inverse Q0")
    require(scale(q1, S * S) == add(mul(scale(c, 4), q5), mul(n3, q6)),
            "block inverse Q1")
    return {"n3": n3, "n4": n4, "c": c, "d": d,
            "determinant": -(S * S)}


def bareiss_determinant(matrix: list[list[int]]) -> int:
    size = len(matrix)
    require(size > 0 and all(len(row) == size for row in matrix), "square matrix")
    data = [row[:] for row in matrix]
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        pivot_row = next((row for row in range(pivot_index, size)
                          if data[row][pivot_index] != 0), None)
        require(pivot_row is not None, "singular Bareiss pivot")
        if pivot_row != pivot_index:
            data[pivot_index], data[pivot_row] = data[pivot_row], data[pivot_index]
            sign = -sign
        pivot = data[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for column in range(pivot_index + 1, size):
                numerator = (data[row][column] * pivot
                             - data[row][pivot_index] * data[pivot_index][column])
                require(numerator % previous == 0, "inexact Bareiss division")
                data[row][column] = numerator // previous
            data[row][pivot_index] = 0
        previous = pivot
    return sign * data[-1][-1]


def sylvester_resultant(first: Poly, second: Poly) -> int:
    m = degree(first)
    n = degree(second)
    size = m + n
    matrix = [[0] * size for _ in range(size)]
    first_desc = list(reversed(first))
    second_desc = list(reversed(second))
    for row in range(n):
        matrix[row][row:row + m + 1] = first_desc
    for row in range(m):
        matrix[n + row][row:row + n + 1] = second_desc
    return bareiss_determinant(matrix)


def roots_mod(poly: Poly, prime: int) -> list[int]:
    return [value for value in range(prime) if evaluate(poly, value) % prime == 0]


def coefficient_spin_certificate(a: Poly, b: Poly) -> dict:
    spin_c: Poly = (25_782_221, 41_783_040, 16_955_904)
    spin_l: Poly = (1_882_609, 1_526_536)
    require(scale(b, 10) == add(mul(linear(21, 16), a), spin_c),
            "coefficient spin identity 0")
    require(scale(a, 49) == add(
        mul(scale(linear(17, 14), 20), spin_c), scale(spin_l, 9)),
        "coefficient spin identity 1")
    require(scale(spin_c, 14_641) == add(
        mul(scale(linear(8_341, 6_776), 24), spin_l), (609_297_605,)),
        "coefficient spin identity 2")
    resultant_ac = sylvester_resultant(a, spin_c)
    resultant_cl = sylvester_resultant(spin_c, spin_l)
    require(resultant_ac == 2 ** 24 * 3 ** 6 * 5 * 19 ** 6 * 83 ** 6,
            "coefficient resultant a,C")
    require(resultant_cl == 2 ** 6 * 5 * 7 ** 2 * 19 ** 4 * 83 ** 4,
            "coefficient resultant C,L")
    common_ac = {
        str(prime): sorted(set(roots_mod(a, prime)) & set(roots_mod(spin_c, prime)))
        for prime in (3, 5, 19, 83)
    }
    require(common_ac == {"3": [], "5": [1], "19": [], "83": []},
            "coefficient common roots a,C")
    lifts_25 = [(value, evaluate(a, value) % 25, evaluate(spin_c, value) % 25)
                for value in range(1, 25, 5)]
    require(all(not (left == 0 and right == 0)
                for _, left, right in lifts_25), "coefficient common lift mod 25")
    common_cl = {
        str(prime): sorted(set(roots_mod(spin_c, prime)) & set(roots_mod(spin_l, prime)))
        for prime in (5, 7, 19, 83)
    }
    require(common_cl == {"5": [1], "7": [5], "19": [], "83": []},
            "coefficient common roots C,L")
    lifts_49 = [(value, evaluate(spin_c, value) % 49,
                 evaluate(spin_l, value) % 49) for value in range(5, 49, 7)]
    require([value for value, left, right in lifts_49 if left == right == 0] == [47],
            "coefficient common lifts mod 49")
    lifts_343 = [(value, evaluate(spin_c, value) % 343,
                  evaluate(spin_l, value) % 343) for value in range(47, 343, 49)]
    require(all(not (left == 0 and right == 0)
                for _, left, right in lifts_343), "coefficient common lift mod 343")
    quotient_rows_7 = [
        (value, evaluate(a, value) % 7,
         (evaluate(spin_c, value) // 7) % 7,
         (evaluate(spin_l, value) // 7) % 7)
        for value in (5, 12, 19, 26, 33, 40)
    ]
    require(quotient_rows_7 == [
        (5, 6, 5, 4), (12, 6, 3, 1), (19, 6, 1, 5),
        (26, 6, 6, 2), (33, 6, 4, 6), (40, 6, 2, 3),
    ], "coefficient quotient table mod 7")
    reduction_digest = hashlib.sha256()
    h_counts = {1: 0, 5: 0}
    k_counts = {1: 0, 7: 0, 49: 0}
    for parameter in range(DIRECT_CHECK_COUNT):
        a_value = evaluate(a, parameter)
        b_value = evaluate(b, parameter)
        c_value = evaluate(spin_c, parameter)
        l_value = evaluate(spin_l, parameter)
        h = math.gcd(a_value, c_value)
        require(h in h_counts and l_value % h == 0, "coefficient h classification")
        a1, c1, l1 = a_value // h, c_value // h, l_value // h
        k = math.gcd(c1, l1)
        require(k in k_counts, "coefficient k classification")
        require((h == 5) == (parameter % 5 == 1), "coefficient h residue class")
        require((k == 49) == (parameter % 49 == 47), "coefficient k=49 class")
        require((k in (7, 49)) == (parameter % 7 == 5),
                "coefficient k support class")
        c2, l2 = c1 // k, l1 // k
        reduction = (
            jacobi(h, b_value)
            * jacobi(k, a1)
            * jacobi(49 // k, c2)
            * jacobi(-1, k)
            * jacobi(5 // h, l2)
            * jacobi(49 // k, l2)
            * jacobi(10 // h, a1)
        )
        coefficient_symbol = jacobi(a_value, b_value)
        require(coefficient_symbol == reduction == -1,
                f"coefficient reduction at j={parameter}")
        require(jacobi(-a_value, b_value) == 1,
                f"coefficient spin at j={parameter}")
        h_counts[h] += 1
        k_counts[k] += 1
        reduction_digest.update(f"{parameter}:{h}:{k}:{reduction}\n".encode())
    require(h_counts == {1: 25_967, 5: 6_492}, "coefficient h counts")
    require(k_counts == {1: 27_822, 7: 3_975, 49: 662},
            "coefficient k counts")
    return {
        "C": spin_c,
        "L": spin_l,
        "constant": 609_297_605,
        "constant_factorization": [["5", "1"], ["7", "2"],
                                   ["19", "2"], ["83", "2"]],
        "resultant_a_C": resultant_ac,
        "resultant_C_L": resultant_cl,
        "common_roots_a_C": common_ac,
        "lifts_mod_25": lifts_25,
        "common_roots_C_L": common_cl,
        "lifts_mod_49": lifts_49,
        "lifts_mod_343": lifts_343,
        "quotient_rows_mod_7": quotient_rows_7,
        "direct_reduction_count": DIRECT_CHECK_COUNT,
        "h_counts": h_counts,
        "k_counts": k_counts,
        "direct_reduction_sha256": reduction_digest.hexdigest(),
        "theorem": "J(-a(j),b(j))=1 for every j>=0",
    }


def jacobi(numerator: int, denominator: int) -> int:
    require(type(numerator) is int and type(denominator) is int,
            "Jacobi inputs must be integers")
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


def gcd_certificate(
    rows: tuple[Poly, ...],
    coefficients: tuple[Poly, Poly, Poly, Poly],
    source_resultant: int,
) -> dict:
    q0, q1, _, _, _, q5, q6 = rows
    a, b, c, d = coefficients
    require(source_resultant == 2 ** 1600, "source resultant")
    # Q0 and Q1 are odd, so the power-of-two resultant makes their values
    # coprime at every specialization.
    common_mod_7 = [value for value in range(7)
                    if evaluate(q5, value) % 7 == 0 and evaluate(q6, value) % 7 == 0]
    require(common_mod_7 == [0], "mod-7 common-root class")
    lifts_mod_49 = []
    for value in range(0, 49, 7):
        left = evaluate(q5, value) % 49
        right = evaluate(q6, value) % 49
        require(left % 7 == 0 and right % 7 == 0, "mod-7 lift")
        require(not (left == 0 and right == 0), "unexpected common mod-49 lift")
        lifts_mod_49.append((value, left, right))
    require(all((left, right) == (42, 7) for _, left, right in lifts_mod_49),
            "endpoint quotient residues mod 7")
    names = [f"Q{index}" for index in range(7)] + ["a", "b", "c", "d"]
    polys = list(rows) + [a, b, c, d]
    support_roots = {
        str(prime): {name: roots_mod(poly, prime) for name, poly in zip(names, polys, strict=True)}
        for prime in DETERMINANT_PRIMES
    }
    require(support_roots["7"] == {
        "Q0": [3], "Q1": [5], "Q2": [4], "Q3": [4],
        "Q4": [1, 2], "Q5": [0], "Q6": [0],
        "a": [1], "b": [], "c": [1], "d": [],
    }, "complete mod-7 root table")
    require(support_roots["4637"] == {
        "Q0": [723], "Q1": [3603], "Q2": [3039, 3502],
        "Q3": [1462, 4491], "Q4": [173, 1721, 4621],
        "Q5": [], "Q6": [], "a": [], "b": [1983, 2128],
        "c": [], "d": [1983, 2128],
    }, "complete mod-4637 root table")
    roots_4637_q5 = support_roots["4637"]["Q5"]
    roots_4637_q6 = support_roots["4637"]["Q6"]
    require(not (set(roots_4637_q5) & set(roots_4637_q6)), "common mod-4637 root")
    require(roots_4637_q5 == [] and roots_4637_q6 == [], "unexpected mod-4637 root")
    # Bounded adversarial verification covers every determinant residue and
    # many higher lifts.  The human proof uses the determinant/resultant and
    # the complete residue certificates above, not this finite range.
    digest = hashlib.sha256()
    raw_failures = 0
    missing_correction_failures = 0
    exceptional_count = 0
    for parameter in range(DIRECT_CHECK_COUNT):
        q0_value = evaluate(q0, parameter)
        q1_value = evaluate(q1, parameter)
        q5_value = evaluate(q5, parameter)
        q6_value = evaluate(q6, parameter)
        endpoint_gcd = math.gcd(q5_value, q6_value)
        expected_gcd = 7 if parameter % 7 == 0 else 1
        require(endpoint_gcd == expected_gcd, f"endpoint gcd at j={parameter}")
        exceptional_count += int(endpoint_gcd == 7)
        initial_symbol = jacobi(q1_value, q0_value)
        reduced_symbol = jacobi(q6_value // endpoint_gcd, q5_value // endpoint_gcd)
        correction = jacobi(-1, endpoint_gcd)
        require(initial_symbol == correction * reduced_symbol,
                f"factor-safe symbol at j={parameter}")
        raw_symbol = (reduced_symbol if endpoint_gcd == 1
                      else jacobi(q6_value, q5_value))
        raw_failures += int(initial_symbol != raw_symbol)
        missing_correction_failures += int(initial_symbol != reduced_symbol)
        coefficient_symbol = jacobi(-evaluate(a, parameter), evaluate(b, parameter))
        require(coefficient_symbol == 1, f"coefficient spin at j={parameter}")
        digest.update(
            f"{parameter}:{endpoint_gcd}:{initial_symbol}:"
            f"{reduced_symbol}:{coefficient_symbol}\n".encode()
        )
    require(exceptional_count == 4_637, "support-period exceptional count")
    require(raw_failures == 4_637, "raw-transfer negative control")
    require(missing_correction_failures == 4_637,
            "missing-correction negative control")
    return {
        "common_mod_7": common_mod_7,
        "lifts_mod_49": lifts_mod_49,
        "roots_4637_q5": roots_4637_q5,
        "roots_4637_q6": roots_4637_q6,
        "support_root_tables": support_roots,
        "direct_check_count": DIRECT_CHECK_COUNT,
        "exceptional_count": exceptional_count,
        "raw_transfer_failure_count": raw_failures,
        "missing_correction_failure_count": missing_correction_failures,
        "direct_check_sha256": digest.hexdigest(),
    }


def encode_int(value: int) -> str:
    require(type(value) is int, "durable integer type")
    return str(value)


def encode_poly(poly: Poly) -> list[str]:
    return [encode_int(value) for value in poly]


def encode_value(value: object) -> object:
    if type(value) is int:
        return encode_int(value)
    if isinstance(value, tuple):
        return [encode_value(item) for item in value]
    if isinstance(value, list):
        return [encode_value(item) for item in value]
    if isinstance(value, dict):
        require(all(type(key) in (str, int) for key in value), "durable dictionary key")
        keys = [str(key) for key in value]
        require(len(keys) == len(set(keys)), "colliding durable dictionary key")
        return {str(key): encode_value(item) for key, item in value.items()}
    return value


def canonical_bytes(payload: dict) -> bytes:
    return (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(type(key) is str and key not in result, "duplicate or non-string JSON key")
        result[key] = value
    return result


def reject_json_number(value: str) -> object:
    raise CertificateError(f"unencoded JSON number: {value}")


def construct_payload() -> dict:
    source_bytes = SOURCE_VERIFIER.read_bytes()
    require(hashlib.sha256(source_bytes).hexdigest() == SOURCE_VERIFIER_SHA256,
            "upstream verifier hash")
    require(b"cert_assert(polresultant(g, u) == -1" in source_bytes,
            "upstream resultant assertion")
    build_inputs()
    # The locked verifier proves Res_x(g,u)=-1.  Under x=2A this gains
    # 2^(41*40); since g(2A)=2*Q0 and -u(2A)=Q1, removing the factor 2
    # from the degree-40 first argument gives Res_A(Q0,Q1)=2^1600.
    source_resultant = 2 ** 1600
    rows = phase_rows()
    identities = verify_adjacent_identities(rows)
    coefficients = block_coefficients()
    matrix = verify_block_matrix(rows)
    spin_data = coefficient_spin_certificate(coefficients[0], coefficients[1])
    gcd_data = gcd_certificate(rows, coefficients, source_resultant)
    boundary_values = [evaluate(row, -1) for row in rows]  # A=2 corresponds to j=-1.
    require(boundary_values[0] == 25_377_553_679_502_347_277_411_601,
            "A=2 boundary half norm")
    require(boundary_values[1] == 43_956_715_453_803_235_217_163_523,
            "A=2 boundary unit")
    require(jacobi(boundary_values[1], boundary_values[0]) == -1,
            "A=2 boundary Jacobi")
    payload = {
        "schema": SCHEMA,
        "claim_ceiling": "exact_block_certificate_not_lean_or_full_chain",
        "upstream": {
            "path": str(SOURCE_VERIFIER),
            "sha256": SOURCE_VERIFIER_SHA256,
            "resultant_g_u": "-1",
            "resultant_scaling": "2^(41*40)/2^40",
            "resultant_positive_unit_half_norm": encode_int(source_resultant),
        },
        "normalization": {
            "A": "8*j+10",
            "domain": "j>=0",
            "Q5_divisor": "2",
            "boundary_A": "2",
            "boundary_j": "-1",
        },
        "rows": [
            {
                "index": encode_int(index),
                "degree": encode_int(degree(row)),
                **row_residue_payload(index, row),
                "coefficients": encode_poly(row),
            }
            for index, row in enumerate(rows)
        ],
        "adjacent_identities": [encode_value(item) for item in identities],
        "block_matrix": {key: encode_poly(value) if isinstance(value, tuple)
                         else encode_int(value) for key, value in matrix.items()},
        "coefficient_spin": encode_value(spin_data),
        "determinant": {
            "s": encode_int(S),
            "factorization": [["7", "1"], ["4637", "1"]],
            "matrix_determinant": encode_int(-(S * S)),
        },
        "gcd_certificate": encode_value(gcd_data),
        "factor_safe_identity": {
            "statement": "J(Q1,Q0)=chi4(g)*J(Q6/g,Q5/g)",
            "chi4_g": "J(-1,g)",
            "g": "7 iff j mod 7 = 0; otherwise 1",
            "phase_10": "A=16*t+10; exceptional iff t mod 7=0",
            "phase_18": "A=16*t+18; exceptional iff t mod 7=3",
        },
        "boundary": {
            "A": "2",
            "Q0": encode_int(boundary_values[0]),
            "Q1": encode_int(boundary_values[1]),
            "jacobi_Q1_Q0": "-1",
        },
    }
    payload["payload_sha256"] = hashlib.sha256(canonical_bytes(payload)).hexdigest()
    return payload


def strict_load(path: Path) -> dict:
    raw = path.read_bytes()
    require(len(raw) <= 250_000, "certificate exceeds 250 KiB")
    payload = json.loads(
        raw,
        object_pairs_hook=unique_object,
        parse_int=reject_json_number,
        parse_float=reject_json_number,
        parse_constant=reject_json_number,
    )
    require(type(payload) is dict, "certificate root")
    required = {
        "schema", "claim_ceiling", "upstream", "normalization", "rows",
        "adjacent_identities", "block_matrix", "coefficient_spin", "determinant",
        "gcd_certificate", "factor_safe_identity", "boundary", "payload_sha256",
    }
    require(set(payload) == required, "certificate fields")
    require(payload["schema"] == SCHEMA, "certificate schema")
    return payload


def require_regeneration(stored: dict, expected: dict) -> None:
    require(canonical_bytes(stored) == canonical_bytes(expected), "certificate regeneration")


def replay(path: Path) -> dict:
    stored = strict_load(path)
    expected = construct_payload()
    require_regeneration(stored, expected)
    return stored


def atomic_write(path: Path, data: bytes) -> None:
    target = path.resolve()
    target.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{target.name}.", dir=target.parent)
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
    if args.write:
        payload = construct_payload()
        data = canonical_bytes(payload)
        require(len(data) <= 250_000, "generated certificate exceeds 250 KiB")
        atomic_write(args.certificate, data)
        require_regeneration(strict_load(args.certificate), payload)
    else:
        payload = replay(args.certificate)
    if args.self_test:
        corrupted = json.loads(json.dumps(payload))
        old = int(corrupted["rows"][5]["coefficients"][0])
        corrupted["rows"][5]["coefficients"][0] = str(old + 1)
        temporary = args.certificate.with_name(f".{args.certificate.name}.corrupt-control")
        try:
            atomic_write(temporary, canonical_bytes(corrupted))
            try:
                require_regeneration(strict_load(temporary), payload)
            except CertificateError:
                pass
            else:
                raise CertificateError("corrupt-row control was accepted")
        finally:
            if temporary.exists():
                temporary.unlink()
    print(
        "OUTER41_JACOBI_BLOCK_OK",
        "rows=7",
        f"checks={DIRECT_CHECK_COUNT}",
        "g=7-iff-j-mod7-zero",
        "claim=block-certificate-not-lean",
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (CertificateError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"OUTER41_JACOBI_BLOCK_FAIL: {error}")
        raise SystemExit(1) from error
