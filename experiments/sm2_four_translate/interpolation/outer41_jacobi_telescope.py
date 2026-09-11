#!/usr/bin/env python3
"""Exact replay for the fixed-41 specialization-safe local certificate.

The replay reconstructs the coefficient pseudo-remainder chain from the
banked fixed-41 source, proves all 18 dual endpoint-matrix identities, checks
every endpoint-constant-support prime by exact polynomial gcd over the
relevant finite field, and certifies all exceptional local residue branches.

The 10,000 specialization checks and 171 span ratios are hostile controls.
They do not prove a directed-link transfer, the universal Jacobi-symbol
telescope, or SS41.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import tempfile
from collections import Counter
from collections.abc import Iterable
from pathlib import Path

import outer41_jacobi_certificate as base

SCHEMA = "sm2.outer41-jacobi-telescope.v2"
UPSTREAM = Path("experiments/sm2_four_translate/interpolation/outer41_jacobi_certificate.py")
UPSTREAM_SHA256 = "41853cf8d0296e6b4ebc0caab5d3a938246ade4944475d6d47b8282e78a68a1c"
DEFAULT_CERTIFICATE = Path(__file__).with_suffix(".json")
CONTROL_BOUND = 10_000
MAX_CERTIFICATE_BYTES = 2_000_000
INDICES = tuple(range(37, 0, -2))
Poly = tuple[int, ...]


EXPECTED_DETERMINANTS: dict[int, tuple[int, tuple[tuple[int, int], ...]]] = {
    37: (1, ((3, 1), (19, 2), (83, 2))),
    35: (1, ((2, 5), (53, 2), (251, 2))),
    33: (1, ((2, 1), (187_337, 2))),
    31: (1, ((2, 3), (13, 2), (237_161, 2))),
    29: (-1, ((2, 2), (41, 2), (277, 2), (15_889, 2))),
    27: (1, ((2, 9), (139, 2), (2_917_199, 2))),
    25: (-1, ((2, 3), (3, 3), (13, 1), (59, 2), (6_530_779, 2))),
    23: (-1, ((2, 3), (3, 2), (306_749, 2), (419_743, 2))),
    21: (1, ((2, 4), (3, 2), (14_149, 2), (35_117, 2))),
    19: (-1, ((2, 3), (37, 2), (23_141_737, 2))),
    17: (1, ((2, 2), (3, 2), (5, 4), (13, 2), (17, 2), (23, 2), (223, 2))),
    15: (1, ((2, 6), (3, 4), (7_675_009, 2))),
    13: (-1, ((2, 2), (7, 2), (263, 2), (54_583, 2))),
    11: (-1, ((2, 5), (3, 3), (204_793, 2))),
    9: (-1, ((2, 2), (3, 8), (109, 2), (179, 2))),
    7: (-1, ((2, 5), (5, 2), (17, 2), (1_621, 2))),
    5: (-1, ((2, 4), (7_841, 2))),
    3: (-1, ((3, 3), (13, 2))),
}


EXPECTED_SUPPORT: dict[int, tuple[tuple[int, int], ...]] = {
    37: ((3, 1), (11, 4)),
    35: ((7, 2), (4_637, 2)),
    33: ((3, 2), (41_801, 2)),
    31: ((5, 2), (19_483, 2)),
    29: ((3, 4), (117_517, 2)),
    27: ((3, 2), (7, 2), (47, 2), (9_491, 2)),
    25: ((3, 5), (73, 2), (18_889_231, 2)),
    23: ((13, 1), (10_639, 2), (290_737, 2)),
    21: ((229, 2), (220_030_169, 2)),
    19: ((13, 2), (17_519_263, 2)),
    17: ((2_731_930_457, 2),),
    15: ((31, 2), (211, 2), (11_633, 2)),
    13: ((1_487, 2), (6_481, 2)),
    11: ((3, 5), (53, 2), (2_791, 2)),
    9: ((3_200_983, 2),),
    7: ((7, 2), (358_727, 2)),
    5: ((3, 4), (31, 2), (811, 2)),
    3: ((3, 7), (11, 2)),
}


class TelescopeError(RuntimeError):
    """A fail-closed reconstruction or verification error."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise TelescopeError(message)


def factor_value(factors: tuple[tuple[int, int], ...], sign: int = 1) -> int:
    require(sign in (-1, 1), "factorization sign")
    result = sign
    for prime, exponent in factors:
        require(type(prime) is int and type(exponent) is int, "integer factorization")
        require(prime >= 2 and exponent >= 1, "positive factorization")
        result *= prime**exponent
    return result


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True


def odd_part(value: int) -> int:
    require(value > 0, "positive support constant")
    while value % 2 == 0:
        value //= 2
    return value


def positive_oriented(poly: Poly, sign: int) -> Poly:
    oriented = base.scale(poly, sign)
    require(
        oriented[0] > 0 and all(coefficient >= 0 for coefficient in oriented),
        "positive oriented polynomial",
    )
    return oriented


def modular_trim(poly: Iterable[int], prime: int) -> list[int]:
    result = [coefficient % prime for coefficient in poly]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def modular_add(left: Iterable[int], right: Iterable[int], prime: int) -> Poly:
    left_values = list(left)
    right_values = list(right)
    size = max(len(left_values), len(right_values))
    result = [0] * size
    for index in range(size):
        result[index] = (
            (left_values[index] if index < len(left_values) else 0)
            + (right_values[index] if index < len(right_values) else 0)
        ) % prime
    return tuple(modular_trim(result, prime))


def modular_sub(left: Iterable[int], right: Iterable[int], prime: int) -> Poly:
    return modular_add(left, (-value for value in right), prime)


def modular_mul(left: Iterable[int], right: Iterable[int], prime: int) -> Poly:
    left_values = list(left)
    right_values = list(right)
    result = [0] * (len(left_values) + len(right_values) - 1)
    for left_index, left_value in enumerate(left_values):
        for right_index, right_value in enumerate(right_values):
            result[left_index + right_index] = (
                result[left_index + right_index] + left_value * right_value
            ) % prime
    return tuple(modular_trim(result, prime))


def modular_divmod(
    dividend: Iterable[int], divisor: Iterable[int], prime: int
) -> tuple[Poly, Poly]:
    remainder = modular_trim(dividend, prime)
    denominator = modular_trim(divisor, prime)
    require(denominator != [0], "nonzero modular divisor")
    quotient = [0] * max(1, len(remainder) - len(denominator) + 1)
    inverse = pow(denominator[-1], -1, prime)
    while remainder != [0] and len(remainder) >= len(denominator):
        coefficient = remainder[-1] * inverse % prime
        shift = len(remainder) - len(denominator)
        quotient[shift] = coefficient
        for index, value in enumerate(denominator):
            remainder[index + shift] = (remainder[index + shift] - coefficient * value) % prime
        remainder = modular_trim(remainder, prime)
    return tuple(modular_trim(quotient, prime)), tuple(remainder)


def modular_divrem(dividend: Iterable[int], divisor: Iterable[int], prime: int) -> list[int]:
    return list(modular_divmod(dividend, divisor, prime)[1])


def modular_xgcd(first: Poly, second: Poly, prime: int) -> tuple[Poly, Poly, Poly]:
    require(is_prime(prime), "prime modular field")
    old_remainder = tuple(modular_trim(first, prime))
    remainder = tuple(modular_trim(second, prime))
    old_first_coefficient, first_coefficient = (1,), (0,)
    old_second_coefficient, second_coefficient = (0,), (1,)
    while remainder != (0,):
        quotient, new_remainder = modular_divmod(old_remainder, remainder, prime)
        old_remainder, remainder = remainder, new_remainder
        old_first_coefficient, first_coefficient = (
            first_coefficient,
            modular_sub(
                old_first_coefficient,
                modular_mul(quotient, first_coefficient, prime),
                prime,
            ),
        )
        old_second_coefficient, second_coefficient = (
            second_coefficient,
            modular_sub(
                old_second_coefficient,
                modular_mul(quotient, second_coefficient, prime),
                prime,
            ),
        )
    inverse = pow(old_remainder[-1], -1, prime)
    gcd = tuple(value * inverse % prime for value in old_remainder)
    first_bezout = tuple(value * inverse % prime for value in old_first_coefficient)
    second_bezout = tuple(value * inverse % prime for value in old_second_coefficient)
    require(
        modular_add(
            modular_mul(first_bezout, first, prime),
            modular_mul(second_bezout, second, prime),
            prime,
        )
        == gcd,
        "modular Bezout identity",
    )
    return gcd, first_bezout, second_bezout


def modular_gcd(first: Poly, second: Poly, prime: int) -> Poly:
    return modular_xgcd(first, second, prime)[0]


def substitute_linear(poly: Poly, scale: int, shift: int) -> Poly:
    require(scale > 0 and shift >= 0, "nonnegative affine substitution")
    result = [0] * len(poly)
    for degree, coefficient in enumerate(poly):
        for output_degree in range(degree + 1):
            result[output_degree] += (
                coefficient
                * math.comb(degree, output_degree)
                * shift ** (degree - output_degree)
                * scale**output_degree
            )
    return tuple(result)


def exact_coefficient_division(poly: Poly, divisor: int) -> Poly:
    require(divisor > 0, "positive coefficient divisor")
    require(all(coefficient % divisor == 0 for coefficient in poly), "exact coefficient division")
    return tuple(coefficient // divisor for coefficient in poly)


def source_coefficient_pair() -> tuple[Poly, Poly]:
    source_raw = base.primitive_prs(*base.build_source_pair())
    source_divisors = tuple(2 if index in (5, 21) else 1 for index in range(len(source_raw)))
    source_rows = base.normalized_phase_rows()
    source_relations = base.adjacent_relations(source_raw, source_divisors, 8, 10)
    source_endpoint = base.verify_endpoint(source_rows, source_relations, 39, 40)
    ((source_a, _), (source_c, _)) = source_endpoint["matrix"]
    return base.exact_div(source_a, 2), base.exact_div(source_c, 2)


def coefficient_chain() -> tuple[
    tuple[Poly, ...], tuple[dict, ...], tuple[tuple[object, object], ...]
]:
    alpha, gamma = source_coefficient_pair()
    rows = base.primitive_prs(gamma, alpha)
    require(len(rows) == 39 and rows[-2:] == ((17, 14), (1,)), "coefficient chain shape")
    relations = base.adjacent_relations(rows, (1,) * len(rows), 1, 0)
    vectors = base.endpoint_vectors(relations)
    require(len(vectors) == len(rows), "coefficient vector count")
    return rows, relations, vectors


def integral_vectors(
    rows: tuple[Poly, ...], vectors: tuple[tuple[object, object], ...]
) -> tuple[tuple[int, Poly, Poly], ...]:
    result = []
    for index, vector in enumerate(vectors):
        scale, left, right = base.integral_row(vector)
        require(
            base.scale(rows[index], scale)
            == base.add(base.mul(left, rows[0]), base.mul(right, rows[1])),
            f"coefficient vector identity {index}",
        )
        result.append((scale, left, right))
    return tuple(result)


def oriented_pairs(vectors: tuple[tuple[int, Poly, Poly], ...]) -> dict[int, tuple[Poly, Poly]]:
    result: dict[int, tuple[Poly, Poly]] = {1: ((0,), (1,))}
    for index in INDICES[:-1]:
        _, left, right = vectors[index]
        require(
            left[-1] != 0 and right[-1] != 0 and left[-1] * right[-1] < 0,
            f"opposite endpoint signs {index}",
        )
        sign = 1 if left[-1] > 0 else -1
        p_poly = positive_oriented(left, sign)
        q_poly = positive_oriented(right, -sign)
        require(len(q_poly) == len(p_poly) + 1, f"oriented consecutive degrees {index}")
        require(p_poly[0] % 2 == 1 and q_poly[0] % 2 == 1, f"oriented odd constants {index}")
        require(
            all(coefficient % 2 == 0 for coefficient in p_poly[1:])
            and all(coefficient % 2 == 0 for coefficient in q_poly[1:]),
            f"oriented even nonconstants {index}",
        )
        result[index] = (p_poly, q_poly)
    require(set(result) == set(INDICES), "oriented index set")
    return result


def build_links(
    rows: tuple[Poly, ...],
    vectors: tuple[tuple[int, Poly, Poly], ...],
    pairs: dict[int, tuple[Poly, Poly]],
) -> tuple[list[dict], list[dict]]:
    links = []
    modular_checks = []
    for index in INDICES[:-1]:
        p_poly, q_poly = pairs[index]
        nested_rows = base.primitive_prs(q_poly, p_poly)
        require(
            [len(row) - 1 for row in nested_rows] == list(range(index - 1, -1, -1)),
            f"nested degree descent {index}",
        )
        require(
            nested_rows[-1] == (1,) and len(nested_rows[-2]) == 2, f"nested terminal rows {index}"
        )
        nested_relations = base.adjacent_relations(nested_rows, (1,) * len(nested_rows), 1, 0)
        endpoint = base.verify_endpoint(
            nested_rows,
            nested_relations,
            len(nested_rows) - 2,
            len(nested_rows) - 1,
        )
        expected_matrix = (
            (vectors[index - 2][1], vectors[index - 2][2]),
            (vectors[index - 1][1], vectors[index - 1][2]),
        )
        require(endpoint["matrix"] == expected_matrix, f"dual endpoint matrix {index}")
        sign, determinant_factors = EXPECTED_DETERMINANTS[index]
        expected_determinant = factor_value(determinant_factors, sign)
        require(endpoint["determinant"] == expected_determinant, f"nested determinant {index}")
        support_factors = EXPECTED_SUPPORT[index]
        support_constant = endpoint["scales"][1]
        require(
            odd_part(support_constant) == factor_value(support_factors),
            f"support constant factorization {index}",
        )
        for prime, _ in determinant_factors + support_factors:
            require(is_prime(prime), f"certified prime {prime}")
        checks = []
        for prime, _ in support_factors:
            polynomial_gcd, bezout_left, bezout_right = modular_xgcd(p_poly, q_poly, prime)
            expected_gcd = (1, 1) if (index, prime) == (23, 13) else (1,)
            require(polynomial_gcd == expected_gcd, f"modular polynomial gcd {index} {prime}")
            check = {
                "index": index,
                "prime": prime,
                "gcd": polynomial_gcd,
                "bezout_left": bezout_left,
                "bezout_right": bezout_right,
            }
            checks.append(check)
            modular_checks.append(check)
        links.append(
            {
                "index": index,
                "input_degrees": (len(q_poly) - 1, len(p_poly) - 1),
                "nested_row_count": len(nested_rows),
                "nested_rows_sha256": hashlib.sha256(
                    base.canonical_bytes({"rows": base.encode(nested_rows)})
                ).hexdigest(),
                "terminal_rows": nested_rows[-2:],
                "endpoint": endpoint,
                "determinant_factorization": {
                    "sign": sign,
                    "factors": determinant_factors,
                },
                "support_constant": support_constant,
                "support_factorization_odd_part": support_factors,
                "modular_gcds": checks,
            }
        )
    require(len(links) == 18 and len(modular_checks) == 41, "link and modular-check totals")
    return links, modular_checks


def p_adic_valuation(value: int, prime: int, ceiling: int) -> int:
    require(value >= 0 and is_prime(prime) and ceiling > 0, "bounded valuation inputs")
    exponent = 0
    while exponent < ceiling and value % prime == 0:
        exponent += 1
        value //= prime
    return exponent


def evaluate_pair(pair: tuple[Poly, Poly], parameter: int) -> tuple[int, int]:
    require(parameter >= 0, "nonnegative specialization")
    return tuple(base.evaluate(poly, parameter) for poly in pair)


def internal_reduction(index: int, parameter: int) -> int:
    return 13 if index == 23 and parameter % 13 == 12 else 1


def reduced_pair_values(
    pairs: dict[int, tuple[Poly, Poly]], index: int, parameter: int
) -> tuple[int, int]:
    divisor = internal_reduction(index, parameter)
    first, second = evaluate_pair(pairs[index], parameter)
    require(first % divisor == 0 and second % divisor == 0, "exact internal reduction")
    return first // divisor, second // divisor


def polynomial_sha256(poly: Poly) -> str:
    return hashlib.sha256(base.canonical_bytes({"coefficients": base.encode(poly)})).hexdigest()


def exact_factorization_record(value: int, sign: int, factors: tuple[tuple[int, int], ...]) -> dict:
    require(value == factor_value(factors, sign), "exact recorded factorization")
    return {"sign": sign, "factors": factors}


def remove_factor(
    factors: tuple[tuple[int, int], ...], prime: int, exponent: int
) -> tuple[tuple[int, int], ...]:
    require(exponent > 0, "positive removed exponent")
    result = []
    found = False
    for factor_prime, factor_exponent in factors:
        if factor_prime == prime:
            require(factor_exponent >= exponent, "available removed factor")
            found = True
            if factor_exponent > exponent:
                result.append((factor_prime, factor_exponent - exponent))
        else:
            result.append((factor_prime, factor_exponent))
    require(found, "removed prime occurs")
    return tuple(result)


def verify_residue_coverage(records: list[dict], modulus: int, label: str) -> None:
    require(modulus > 0, f"{label} positive modulus")
    residues = [record["residue"] for record in records]
    require(residues == list(range(modulus)), f"{label} total ordered coverage")
    require(len(set(residues)) == modulus, f"{label} disjoint coverage")


def build_primary_partition(
    pairs: dict[int, tuple[Poly, Poly]],
    index: int,
    modulus: int,
    precision_modulus: int,
) -> dict:
    require(index in (37, 25, 11), "exceptional 3-primary link")
    require(precision_modulus == 3 * modulus, "one-level 3-primary refinement")
    source = pairs[index]
    target = pairs[index - 2]
    ceiling = 0
    power = precision_modulus
    while power > 1:
        require(power % 3 == 0, "3-power precision")
        ceiling += 1
        power //= 3
    records = []
    for residue in range(modulus):
        refinements = []
        common_exponents = set()
        for parameter in range(residue, precision_modulus, modulus):
            source_q = base.evaluate(source[1], parameter) % precision_modulus
            target_q = base.evaluate(target[1], parameter) % precision_modulus
            common_exponent = min(
                p_adic_valuation(source_q, 3, ceiling),
                p_adic_valuation(target_q, 3, ceiling),
            )
            require(common_exponent < ceiling, f"exact 3-primary depth {index} {parameter}")
            common_exponents.add(common_exponent)
            refinements.append(
                {
                    "residue": parameter,
                    "source_q": source_q,
                    "target_q": target_q,
                }
            )
        require(len(common_exponents) == 1, f"3-primary branch determined modulo {modulus}")
        common_exponent = common_exponents.pop()
        parameter = residue
        source_p = base.evaluate(source[0], parameter)
        target_p = base.evaluate(target[0], parameter)
        common_power = 3**common_exponent
        correction_symbol = base.jacobi(source_p, common_power) * base.jacobi(
            target_p, common_power
        )
        require(correction_symbol in (-1, 1), f"nonzero 3-primary correction {index} {residue}")
        records.append(
            {
                "residue": residue,
                "common_exponent": common_exponent,
                "common_power": common_power,
                "correction_symbol": correction_symbol,
                "refinements": refinements,
            }
        )
    verify_residue_coverage(records, modulus, f"i{index} 3-primary")
    return {
        "index": index,
        "prime": 3,
        "modulus": modulus,
        "precision_modulus": precision_modulus,
        "records": records,
        "claim": "exact_common_3_primary_factor_and_local_correction",
    }


def build_root_partition(alpha: Poly, gamma: Poly, pairs: dict[int, tuple[Poly, Poly]]) -> dict:
    p37, q37 = pairs[37]
    records = []
    for residue in range(25):
        alpha_value = base.evaluate(alpha, residue)
        gamma_value = base.evaluate(gamma, residue)
        p_value = base.evaluate(p37, residue)
        q_value = base.evaluate(q37, residue)
        gamma_residue = gamma_value % 25
        q_residue = q_value % 25
        common_exponent = min(
            p_adic_valuation(gamma_residue, 5, 2),
            p_adic_valuation(q_residue, 5, 2),
        )
        require(common_exponent < 2, f"root common factor not 25 {residue}")
        require((common_exponent == 1) == (residue % 5 == 4), f"root 5-primary class {residue}")
        common_power = 5**common_exponent
        correction_symbol = base.jacobi(alpha_value, common_power) * base.jacobi(
            p_value, common_power
        )
        require(correction_symbol == 1, f"root correction {residue}")
        records.append(
            {
                "residue": residue,
                "isolated_residue_four": residue == 4,
                "alpha": alpha_value % 25,
                "gamma": gamma_residue,
                "target_p": p_value % 25,
                "target_q": q_residue,
                "common_exponent": common_exponent,
                "common_power": common_power,
                "correction_symbol": correction_symbol,
            }
        )
    verify_residue_coverage(records, 25, "root modulo 25")
    require(
        sum(record["isolated_residue_four"] for record in records) == 1,
        "unique isolated root residue four",
    )
    return {
        "modulus": 25,
        "determinant": 245,
        "determinant_factorization": ((5, 1), (7, 2)),
        "support_constant": 5,
        "cross_scale": 800,
        "cross_linear": (17, 14),
        "records": records,
        "claim": "exact_pre_telescope_local_partition_not_transfer",
    }


def build_factor_thirteen_partition(pairs: dict[int, tuple[Poly, Poly]]) -> dict:
    p23, q23 = pairs[23]
    substituted_p = substitute_linear(p23, 13, 12)
    substituted_q = substitute_linear(q23, 13, 12)
    quotient_p = exact_coefficient_division(substituted_p, 13)
    quotient_q = exact_coefficient_division(substituted_q, 13)
    quotient_bezout = []
    for prime in (13, 10639, 290737):
        quotient_gcd, bezout_left, bezout_right = modular_xgcd(quotient_p, quotient_q, prime)
        require(
            quotient_gcd == (1,),
            f"factor-thirteen quotient coprimality modulo {prime}",
        )
        quotient_bezout.append(
            {
                "prime": prime,
                "gcd": quotient_gcd,
                "left": bezout_left,
                "right": bezout_right,
            }
        )
    records = []
    for residue in range(13):
        p_residue = base.evaluate(p23, residue) % 13
        q_residue = base.evaluate(q23, residue) % 13
        on_factor_class = residue == 12
        require(
            (p_residue == 0 and q_residue == 0) == on_factor_class,
            f"factor-thirteen root class {residue}",
        )
        symbol = 1 if on_factor_class else base.jacobi(residue + 1, 13)
        require(symbol in (-1, 1), f"off-class factor symbol {residue}")
        records.append(
            {
                "residue": residue,
                "factor": 13 if on_factor_class else 1,
                "p": p_residue,
                "q": q_residue,
                "off_class_symbol": symbol,
            }
        )
    verify_residue_coverage(records, 13, "factor-thirteen")
    return {
        "index": 23,
        "prime": 13,
        "modulus": 13,
        "records": records,
        "quotient_substitution": {"scale": 13, "shift": 12},
        "quotient_p": quotient_p,
        "quotient_q": quotient_q,
        "quotient_bezout": quotient_bezout,
        "quotient_p_sha256": polynomial_sha256(quotient_p),
        "quotient_q_sha256": polynomial_sha256(quotient_q),
        "claim": "exact_division_on_class_and_J_j_plus_one_13_off_class",
    }


def build_local_links(
    vectors: tuple[tuple[int, Poly, Poly], ...],
    pairs: dict[int, tuple[Poly, Poly]],
    links: list[dict],
) -> list[dict]:
    link_by_index = {link["index"]: link for link in links}
    records = []
    for index in INDICES[:-1]:
        source_p, source_q = pairs[index]
        target_p, target_q = pairs[index - 2]
        link = link_by_index[index]
        endpoint = link["endpoint"]
        target_orientation = 1 if vectors[index - 2][1][-1] > 0 else -1
        cross_scale = endpoint["scales"][0]
        cross_linear = link["terminal_rows"][0]
        raw_cross = base.sub(
            base.mul(target_p, source_q),
            base.mul(target_q, source_p),
        )
        require(
            raw_cross == base.scale(cross_linear, target_orientation * cross_scale),
            f"oriented cross identity {index}",
        )
        _, endpoint_left, endpoint_right = vectors[index - 1]
        support_constant = link["support_constant"]
        require(
            base.add(
                base.mul(endpoint_left, source_q),
                base.mul(endpoint_right, source_p),
            )
            == (support_constant,),
            f"endpoint support identity {index}",
        )
        determinant = endpoint["determinant"]
        delta = target_orientation * determinant
        determinant_sign = link["determinant_factorization"]["sign"]
        determinant_factors = link["determinant_factorization"]["factors"]
        support_factors = link["support_factorization_odd_part"]
        exact_factorization_record(determinant, determinant_sign, determinant_factors)
        require(
            odd_part(support_constant) == factor_value(support_factors),
            f"endpoint support factors {index}",
        )
        reduction_cases = [
            {"condition": "all", "residue": None, "source_divisor": 1, "target_divisor": 1}
        ]
        if index == 25:
            reduction_cases = [
                {
                    "condition": "j%13!=12",
                    "residue": None,
                    "source_divisor": 1,
                    "target_divisor": 1,
                },
                {"condition": "j%13=12", "residue": 12, "source_divisor": 1, "target_divisor": 13},
            ]
        elif index == 23:
            reduction_cases = [
                {
                    "condition": "j%13!=12",
                    "residue": None,
                    "source_divisor": 1,
                    "target_divisor": 1,
                },
                {"condition": "j%13=12", "residue": 12, "source_divisor": 13, "target_divisor": 1},
            ]
        checked_cases = []
        for case in reduction_cases:
            source_divisor = case["source_divisor"]
            target_divisor = case["target_divisor"]
            adjusted_support = support_constant // source_divisor
            adjusted_delta = delta // target_divisor
            require(
                adjusted_support * source_divisor == support_constant,
                f"adjusted support exact {index}",
            )
            require(adjusted_delta * target_divisor == delta, f"adjusted determinant exact {index}")
            if case["residue"] is None:
                reduced_cross = raw_cross
            else:
                substituted_cross = substitute_linear(raw_cross, 13, case["residue"])
                reduced_cross = exact_coefficient_division(
                    substituted_cross, source_divisor * target_divisor
                )
            case_record = dict(case)
            case_record.update(
                {
                    "adjusted_support": adjusted_support,
                    "adjusted_delta": adjusted_delta,
                    "adjusted_gcd": math.gcd(abs(adjusted_support), abs(adjusted_delta)),
                    "reduced_cross": reduced_cross,
                    "reduced_cross_sha256": polynomial_sha256(reduced_cross),
                }
            )
            checked_cases.append(case_record)
        records.append(
            {
                "index": index,
                "target_index": index - 2,
                "target_orientation": target_orientation,
                "cross_scale": cross_scale,
                "cross_linear": cross_linear,
                "support_constant": support_constant,
                "support_factorization_odd_part": support_factors,
                "determinant": determinant,
                "oriented_delta": delta,
                "determinant_factorization": {
                    "sign": determinant_sign,
                    "factors": determinant_factors,
                },
                "reduction_cases": checked_cases,
                "kernel_data": {
                    "h": "gcd(reduced_Q_i,reduced_Q_target)",
                    "Q0": "reduced_Q_i/h",
                    "q0": "reduced_Q_target/h",
                    "r": "(reduced_P_target*reduced_Q_i-reduced_Q_target*reduced_P_i)/h",
                },
                "claim": "exact_local_data_not_directed_link_transfer",
            }
        )
    require(len(records) == 18, "local link count")
    return records


def build_local_certificate(
    vectors: tuple[tuple[int, Poly, Poly], ...],
    pairs: dict[int, tuple[Poly, Poly]],
    links: list[dict],
) -> dict:
    alpha, gamma = source_coefficient_pair()
    p37, q37 = pairs[37]
    root_cross = base.sub(base.mul(p37, gamma), base.mul(q37, alpha))
    require(root_cross == base.scale((17, 14), 800), "pre-telescope cross identity")
    _, root_left, root_right = vectors[38]
    require(
        base.add(base.mul(root_left, gamma), base.mul(root_right, alpha)) == (5,),
        "pre-telescope support identity",
    )
    require(
        base.add(base.mul(p37, root_right), base.mul(q37, root_left)) == (245,),
        "pre-telescope determinant identity",
    )
    primary_partitions = {
        37: build_primary_partition(pairs, 37, 3, 9),
        25: build_primary_partition(pairs, 25, 27, 81),
        11: build_primary_partition(pairs, 11, 27, 81),
    }
    factor_thirteen = build_factor_thirteen_partition(pairs)
    direct_p3, direct_q3 = pairs[3]
    require(pairs[1] == ((0,), (1,)), "direct terminal target")
    direct_records = []
    for residue in range(27):
        p_value = base.evaluate(direct_p3, residue)
        q_value = base.evaluate(direct_q3, residue)
        direct_records.append(
            {
                "residue": residue,
                "p_mod_27": p_value % 27,
                "q_mod_27": q_value % 27,
                "symbol": base.jacobi(p_value, q_value),
            }
        )
    verify_residue_coverage(direct_records, 27, "direct i3 endpoint")
    require(
        {record["symbol"] for record in direct_records} == {-1}, "direct i3 endpoint symbol control"
    )
    local_links = build_local_links(vectors, pairs, links)
    exceptional_indices = {37, 25, 23, 11, 3}
    neutral_links = []
    for link in local_links:
        index = link["index"]
        support_factors = link["support_factorization_odd_part"]
        determinant_factors = link["determinant_factorization"]["factors"]
        odd_support = {prime for prime, exponent in support_factors if exponent % 2 == 1}
        odd_determinant = {
            prime for prime, exponent in determinant_factors if prime != 2 and exponent % 2 == 1
        }
        permitted = {
            37: ({3}, {3}),
            25: ({3}, {3, 13}),
            23: ({13}, set()),
            11: ({3}, {3}),
            3: ({3}, {3}),
        }.get(index, (set(), set()))
        require(odd_support == permitted[0], f"support squareclass exceptions {index}")
        require(odd_determinant == permitted[1], f"determinant squareclass exceptions {index}")
        if index not in exceptional_indices:
            neutral_links.append(index)
    require(
        neutral_links == [35, 33, 31, 29, 27, 21, 19, 17, 15, 13, 9, 7, 5],
        "ordinary squareclass-neutral links",
    )
    result = {
        "claim_ceiling": "exact_local_certificate_not_link_transfer_telescope_or_SS41",
        "root": build_root_partition(alpha, gamma, pairs),
        "links": local_links,
        "primary_partitions": primary_partitions,
        "factor_thirteen": factor_thirteen,
        "direct_i3": {
            "source_index": 3,
            "target_pair": {"p": (0,), "q": (1,)},
            "source_pair": {"P": direct_p3, "Q": direct_q3},
            "modulus": 27,
            "records": direct_records,
            "generic_nonzero_p_wrapper_used": False,
        },
        "squareclass_neutral_links": neutral_links,
        "coverage": {
            "directed_links": len(local_links),
            "root_mod_25": 25,
            "i37_mod_3": 3,
            "i25_mod_27": 27,
            "i23_mod_13": 13,
            "i11_mod_27": 27,
            "all_partitions_total_and_pairwise_disjoint": True,
        },
    }
    result["sha256"] = hashlib.sha256(canonical_bytes(encode(result))).hexdigest()
    return result


def build_controls(pairs: dict[int, tuple[Poly, Poly]]) -> dict:
    span_values = {
        (left, right): set()
        for left_position, left in enumerate(INDICES)
        for right in INDICES[left_position + 1 :]
    }
    symbol_counts = {index: Counter() for index in INDICES}
    digest = hashlib.sha256()
    for parameter in range(CONTROL_BOUND):
        symbols = {}
        for index in INDICES:
            p_poly, q_poly = pairs[index]
            p_value = base.evaluate(p_poly, parameter)
            q_value = base.evaluate(q_poly, parameter)
            common = math.gcd(p_value, q_value)
            expected_common = 13 if index == 23 and parameter % 13 == 12 else 1
            require(common == expected_common, f"bounded gcd control {index} {parameter}")
            symbol = base.jacobi(p_value // common, q_value // common)
            require(symbol in (-1, 1), "reduced control symbol")
            symbols[index] = symbol
            symbol_counts[index][symbol] += 1
        if parameter % 13 == 12:
            require(symbols[23] == 1, "exceptional factor-thirteen symbol")
        else:
            require(
                symbols[23] == base.jacobi(parameter + 1, 13),
                "nonexceptional factor-thirteen symbol",
            )
        for span in span_values:
            span_values[span].add(symbols[span[0]] * symbols[span[1]])
        digest.update(
            (
                f"{parameter}:" + ",".join(f"{index}={symbols[index]}" for index in INDICES) + "\n"
            ).encode()
        )
    constant_spans = [span for span, values in span_values.items() if len(values) == 1]
    variable_spans = [span for span, values in span_values.items() if len(values) > 1]
    expected_variable = [span for span in span_values if (span[0] == 23) != (span[1] == 23)]
    require(len(span_values) == 171, "span total")
    require(
        len(constant_spans) == 153 and len(variable_spans) == 18,
        "constant and variable span totals",
    )
    require(variable_spans == expected_variable, "unique variable endpoint")
    require(span_values[(25, 21)] == {-1}, "factor-thirteen two-block ratio")
    require(span_values[(37, 1)] == {1}, "full telescope ratio")
    return {
        "bound": CONTROL_BOUND,
        "symbol_counts": {
            index: dict(sorted(counts.items())) for index, counts in symbol_counts.items()
        },
        "span_count": len(span_values),
        "constant_span_count": len(constant_spans),
        "variable_spans": variable_spans,
        "factor_thirteen_span": {"indices": (25, 21), "ratio": -1},
        "full_span": {"indices": (37, 1), "ratio": 1},
        "sha256": digest.hexdigest(),
        "claim": "diagnostic_only",
    }


def encode(value: object) -> object:
    if type(value) is int:
        return str(value)
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    return value


def canonical_bytes(payload: dict) -> bytes:
    return (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()


def construct_payload() -> dict:
    require(UPSTREAM.exists(), "upstream replay path")
    require(
        hashlib.sha256(UPSTREAM.read_bytes()).hexdigest() == UPSTREAM_SHA256, "upstream replay hash"
    )
    require(base.SOURCE.exists(), "banked GP source path")
    require(
        hashlib.sha256(base.SOURCE.read_bytes()).hexdigest() == base.SOURCE_SHA256,
        "banked GP source hash",
    )
    rows, _, raw_vectors = coefficient_chain()
    vectors = integral_vectors(rows, raw_vectors)
    pairs = oriented_pairs(vectors)
    links, modular_checks = build_links(rows, vectors, pairs)
    local_certificate = build_local_certificate(vectors, pairs, links)
    controls = build_controls(pairs)
    structural_payload = {
        "pairs": {index: pairs[index] for index in INDICES},
        "links": links,
        "modular_checks": modular_checks,
        "local_certificate": local_certificate,
    }
    payload = {
        "schema": SCHEMA,
        "marker": "OUTER41_JACOBI_LOCAL_OK",
        "claim_ceiling": "exact_local_certificate_not_link_transfer_telescope_or_SS41",
        "upstream": {
            "path": str(UPSTREAM),
            "sha256": UPSTREAM_SHA256,
            "source_path": str(base.SOURCE),
            "source_sha256": base.SOURCE_SHA256,
        },
        "coefficient_chain": {
            "row_count": len(rows),
            "rows_sha256": hashlib.sha256(
                base.canonical_bytes({"rows": base.encode(rows)})
            ).hexdigest(),
            "indices": INDICES,
            "oriented_pairs": {index: pairs[index] for index in INDICES},
        },
        "dual_telescope": {
            "link_count": len(links),
            "links": links,
            "modular_gcd_check_count": len(modular_checks),
            "modular_gcd_checks": modular_checks,
            "unique_specialization_gcd": {
                "index": 23,
                "prime": 13,
                "condition": "j%13=12",
                "value_on_condition": 13,
                "value_otherwise": 1,
            },
            "structural_sha256": hashlib.sha256(
                canonical_bytes(encode(structural_payload))
            ).hexdigest(),
            "terminal_pair": {"P1": (0,), "Q1": (1,)},
            "universal_status": "pending_concrete_specialization_safe_link_theorems",
        },
        "local_certificate": local_certificate,
        "bounded_controls": controls,
        "proof_dag": [
            {"id": "L1", "kind": "OrientedEndpointVectors", "status": "exact"},
            {"id": "L2", "kind": "DualPRSReversal18", "status": "exact"},
            {
                "id": "L3a",
                "kind": "GenericFactorSafeJacobiKernel",
                "status": "formalized_external_Lean",
                "theorem": "ss41_crossJacobiTransfer",
            },
            {
                "id": "L3b",
                "kind": "GenericEndpointFactorCorrection",
                "status": "formalized_external_Lean",
                "theorem": "ss41_endpointFactorCorrection",
            },
            {"id": "L3c", "kind": "ConcreteLinkCoprimalityOrientation", "status": "exact_replayed"},
            {"id": "L4", "kind": "GcdSupport", "status": "exact"},
            {"id": "L5", "kind": "UniqueFactor13", "status": "exact_replayed"},
            {"id": "L6", "kind": "OrdinaryLinkTransfers", "status": "open"},
            {"id": "L7", "kind": "Factor13TwoBlock", "status": "open"},
            {"id": "L8", "kind": "UniversalTelescope", "status": "open"},
        ],
        "nonclaims": [
            "the local certificate does not assert a directed-link equality",
            "bounded controls do not prove the universal Jacobi-symbol telescope",
            "the certificate does not prove SS41",
            "no packet adapter or terminal closure follows",
            "maintained terminal status remains 1/4",
        ],
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
    raise TelescopeError(f"unencoded JSON number: {value}")


def strict_load(path: Path) -> dict:
    with path.open("rb") as handle:
        raw = handle.read(MAX_CERTIFICATE_BYTES + 1)
    require(len(raw) <= MAX_CERTIFICATE_BYTES, "certificate size")
    payload = json.loads(
        raw,
        object_pairs_hook=unique_object,
        parse_int=reject_number,
        parse_float=reject_number,
        parse_constant=reject_number,
    )
    require(type(payload) is dict and payload.get("schema") == SCHEMA, "certificate schema")
    return payload


def verify_certificate(path: Path, expected: dict) -> dict:
    stored = strict_load(path)
    require(path.read_bytes() == canonical_bytes(expected), "byte-identical regeneration")
    return stored


def require_mutation_rejected(path: Path, mutated: dict, expected: dict, label: str) -> None:
    atomic_write(path, canonical_bytes(mutated))
    try:
        verify_certificate(path, expected)
    except TelescopeError as error:
        require(str(error) == "byte-identical regeneration", f"{label} rejection reason")
    else:
        raise TelescopeError(f"{label} accepted")


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
    expected = construct_payload()
    if args.write:
        atomic_write(args.certificate, canonical_bytes(expected))
    stored = verify_certificate(args.certificate, expected)
    if args.self_test:
        rows, _, raw_vectors = coefficient_chain()
        vectors = integral_vectors(rows, raw_vectors)
        pairs = oriented_pairs(vectors)
        p37, q37 = pairs[37]
        nested_rows = base.primitive_prs(q37, p37)
        nested_relations = base.adjacent_relations(nested_rows, (1,) * len(nested_rows), 1, 0)
        endpoint = base.verify_endpoint(
            nested_rows,
            nested_relations,
            len(nested_rows) - 2,
            len(nested_rows) - 1,
        )
        corrupted_matrix = [[list(poly) for poly in row] for row in endpoint["matrix"]]
        corrupted_matrix[0][0][0] += 1
        first_index = endpoint["indices"][0]
        first_scale = endpoint["scales"][0]
        corrupted_first = (tuple(corrupted_matrix[0][0]), tuple(corrupted_matrix[0][1]))
        require(
            base.scale(nested_rows[first_index], first_scale)
            != base.add(
                base.mul(corrupted_first[0], nested_rows[0]),
                base.mul(corrupted_first[1], nested_rows[1]),
            ),
            "corrupt endpoint identity rejected",
        )
        p23 = tuple(map(int, stored["coefficient_chain"]["oriented_pairs"]["23"][0]))
        q23 = tuple(map(int, stored["coefficient_chain"]["oriented_pairs"]["23"][1]))
        parameter = 12
        p_value = base.evaluate(p23, parameter)
        q_value = base.evaluate(q23, parameter)
        require(math.gcd(p_value, q_value) == 13, "factor-thirteen hostile control")
        require(base.jacobi(p_value, q_value) == 0, "raw exceptional symbol must vanish")
        require(base.jacobi(p_value // 13, q_value // 13) == 1, "divided exceptional symbol")
        require(
            modular_gcd(p23, q23, 13) != (1,), "corrupt factor-thirteen gcd expectation rejected"
        )
        first_link = stored["dual_telescope"]["links"][0]
        support_constant = int(first_link["support_constant"])
        support_factors = tuple(
            (int(prime), int(exponent))
            for prime, exponent in first_link["support_factorization_odd_part"]
        )
        *unchanged_factors, final_factor = support_factors
        corrupted_factors = (*unchanged_factors, (final_factor[0], final_factor[1] + 1))
        require(
            odd_part(support_constant) != factor_value(corrupted_factors),
            "corrupt support factorization rejected",
        )
        with tempfile.TemporaryDirectory(prefix="outer41-telescope-") as directory:
            mutation_path = Path(directory) / "mutation.json"
            mutations = []
            corrupted_root = json.loads(json.dumps(expected))
            corrupted_root["local_certificate"]["root"]["records"][4]["residue"] = "5"
            mutations.append(("corrupted root residue", corrupted_root))
            corrupted_quotient = json.loads(json.dumps(expected))
            quotient = corrupted_quotient["local_certificate"]["factor_thirteen"]["quotient_p"]
            quotient[0] = str(int(quotient[0]) + 1)
            mutations.append(("altered quotient identity", corrupted_quotient))
            missing_branch = json.loads(json.dumps(expected))
            missing_branch["local_certificate"]["primary_partitions"]["25"]["records"].pop()
            mutations.append(("missing residue branch", missing_branch))
            duplicate_branch = json.loads(json.dumps(expected))
            duplicate_records = duplicate_branch["local_certificate"]["primary_partitions"]["11"][
                "records"
            ]
            duplicate_records[-1] = duplicate_records[-2]
            mutations.append(("duplicated residue branch", duplicate_branch))
            corrupted_support = json.loads(json.dumps(expected))
            corrupted_support["local_certificate"]["links"][0]["support_constant"] = str(
                int(corrupted_support["local_certificate"]["links"][0]["support_constant"]) + 2
            )
            mutations.append(("corrupted support factor", corrupted_support))
            corrupted_determinant = json.loads(json.dumps(expected))
            corrupted_determinant["local_certificate"]["links"][0]["determinant"] = str(
                int(corrupted_determinant["local_certificate"]["links"][0]["determinant"]) + 1
            )
            mutations.append(("corrupted determinant", corrupted_determinant))
            flipped_orientation = json.loads(json.dumps(expected))
            orientation = flipped_orientation["local_certificate"]["links"][0]["target_orientation"]
            flipped_orientation["local_certificate"]["links"][0]["target_orientation"] = str(
                -int(orientation)
            )
            mutations.append(("flipped orientation", flipped_orientation))
            suppressed_division = json.loads(json.dumps(expected))
            suppressed_division["local_certificate"]["factor_thirteen"]["records"][12]["factor"] = (
                "1"
            )
            mutations.append(("suppressed factor-thirteen division", suppressed_division))
            corrupted_vector = json.loads(json.dumps(expected))
            vector_value = corrupted_vector["coefficient_chain"]["oriented_pairs"]["37"][0][0]
            corrupted_vector["coefficient_chain"]["oriented_pairs"]["37"][0][0] = str(
                int(vector_value) + 1
            )
            mutations.append(("corrupted coefficient vector", corrupted_vector))
            for label, mutation in mutations:
                require_mutation_rejected(mutation_path, mutation, expected, label)
            pretty_path = Path(directory) / "pretty.json"
            pretty = (json.dumps(expected, sort_keys=True, indent=2) + "\n").encode()
            atomic_write(pretty_path, pretty)
            try:
                verify_certificate(pretty_path, expected)
            except TelescopeError as error:
                require(
                    str(error) == "byte-identical regeneration",
                    "noncanonical JSON rejection reason",
                )
            else:
                raise TelescopeError("noncanonical JSON accepted")
            oversized_path = Path(directory) / "oversized.json"
            atomic_write(
                oversized_path,
                b" " * (MAX_CERTIFICATE_BYTES + 1),
            )
            try:
                strict_load(oversized_path)
            except TelescopeError as error:
                require(str(error) == "certificate size", "oversized certificate rejection reason")
            else:
                raise TelescopeError("oversized certificate accepted")
    print(
        "OUTER41_JACOBI_LOCAL_OK",
        "links=18",
        "modular_gcds=41",
        "branches=95",
        "spans=171",
        "claim=local-certificate-not-SS41",
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        TelescopeError,
        base.CertificateError,
        OSError,
        ValueError,
        json.JSONDecodeError,
    ) as error:
        print(f"OUTER41_JACOBI_TELESCOPE_FAIL: {error}")
        raise SystemExit(1) from error
