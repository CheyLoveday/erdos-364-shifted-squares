#!/usr/bin/env python3
"""Independent finite-object replay for the Paper I evidence bundle.

This verifier deliberately does not import any certificate producer.  It
parses the maintained JSON objects as hostile input, reconstructs their
integer and polynomial arithmetic with a separate implementation, and emits
one marker only after every check succeeds.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import math
import os
from pathlib import Path
import re
import stat
import sys
from typing import Iterable, NoReturn


MARKER = "PAPER1_INDEPENDENT_FINITE_OK"
REPOSITORY = Path(__file__).resolve().parents[4]
INTERPOLATION = REPOSITORY / "experiments/sm2_four_translate/interpolation"
BLOCK_PATH = INTERPOLATION / "outer41_jacobi_block.json"
CERTIFICATE_PATH = INTERPOLATION / "outer41_jacobi_certificate.json"
TELESCOPE_PATH = INTERPOLATION / "outer41_jacobi_telescope.json"
PROPAGATION_PATH = REPOSITORY / "experiments/shifted_square_propagation/expected.json"
SOURCE_41_PATH = INTERPOLATION / "outer41_verify.gp"
SOURCE_41_SHA256 = "59ac1ef75d1d5e953aec81943a28bdb6b0656721de7947506704ac498c7bb560"
TELESCOPE_PRODUCER_PATH = INTERPOLATION / "outer41_jacobi_certificate.py"
TELESCOPE_PRODUCER_SHA256 = "41853cf8d0296e6b4ebc0caab5d3a938246ade4944475d6d47b8282e78a68a1c"

UNIT_41 = (
    -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
    3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
    -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5,
)
UNIT_17 = (-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1)
PAIR_INDICES = tuple(range(37, 0, -2))
INTEGER_TEXT = re.compile(r"(?:0|-?[1-9][0-9]*)\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")

Poly = tuple[int, ...]
FracPoly = tuple[Fraction, ...]


class AuditError(RuntimeError):
    """A fail-closed independent-replay failure."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def canonical_bytes(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def reject_number(token: str) -> NoReturn:
    raise AuditError(f"unencoded JSON number: {token}")


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        require(type(key) is str and key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_bounded(path: Path, *, max_bytes: int) -> bytes:
    """Read a bounded regular repository file without following symlinks."""

    require(type(max_bytes) is int and max_bytes >= 0, "invalid file byte ceiling")
    try:
        relative = path.relative_to(REPOSITORY)
    except ValueError as error:
        raise AuditError(f"path outside repository: {path}") from error
    current = REPOSITORY
    require(current.is_dir() and not current.is_symlink(), "invalid repository root")
    for part in relative.parts:
        current /= part
        require(not current.is_symlink(), f"symlink input forbidden: {relative}")
    flags = os.O_RDONLY
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise AuditError(f"cannot open input: {relative}") from error
    try:
        metadata = os.fstat(descriptor)
        require(stat.S_ISREG(metadata.st_mode), f"non-regular input: {relative}")
        require(metadata.st_size <= max_bytes, f"oversized input: {relative}")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(64 * 1024, max_bytes - total + 1))
            if not chunk:
                break
            total += len(chunk)
            require(total <= max_bytes, f"oversized input: {relative}")
            chunks.append(chunk)
        return b"".join(chunks)
    except OSError as error:
        raise AuditError(f"cannot read input: {relative}") from error
    finally:
        os.close(descriptor)


def load_json(path: Path, *, max_bytes: int, strings_only_numbers: bool) -> dict[str, object]:
    raw = read_bounded(path, max_bytes=max_bytes)
    options: dict[str, object] = {"object_pairs_hook": unique_object}
    if strings_only_numbers:
        options.update(parse_int=reject_number, parse_float=reject_number, parse_constant=reject_number)
    try:
        value = json.loads(raw.decode("utf-8"), **options)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditError(f"invalid JSON: {path.name}: {error}") from error
    require(type(value) is dict, f"non-object JSON root: {path.name}")
    require(raw == canonical_bytes(value), f"noncanonical JSON bytes: {path.name}")
    return value


def keys(value: object, expected: set[str], label: str) -> dict[str, object]:
    require(type(value) is dict, f"{label}: expected object")
    result = value
    require(set(result) == expected, f"{label}: field set changed")
    return result


def as_list(value: object, label: str, length: int | None = None) -> list[object]:
    require(type(value) is list, f"{label}: expected list")
    result = value
    if length is not None:
        require(len(result) == length, f"{label}: length changed")
    return result


def integer(value: object, label: str) -> int:
    require(type(value) is str and INTEGER_TEXT.fullmatch(value) is not None, f"{label}: noncanonical integer")
    return int(value)


def integer_list(value: object, label: str) -> tuple[int, ...]:
    return tuple(integer(item, f"{label}[{index}]") for index, item in enumerate(as_list(value, label)))


def polynomial(value: object, label: str) -> Poly:
    result = integer_list(value, label)
    require(result and (len(result) == 1 or result[-1] != 0), f"{label}: untrimmed polynomial")
    return result


def encode(value: object) -> object:
    if type(value) is int:
        return str(value)
    if isinstance(value, Fraction):
        require(value.denominator == 1, "nonintegral durable value")
        return str(value.numerator)
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    if isinstance(value, dict):
        rendered = {str(key): encode(item) for key, item in value.items()}
        require(len(rendered) == len(value), "colliding rendered dictionary key")
        return rendered
    return value


def verify_payload_digest(payload: dict[str, object], label: str) -> None:
    observed = payload.get("payload_sha256")
    require(type(observed) is str and HEX64.fullmatch(observed) is not None, f"{label}: invalid payload digest")
    body = dict(payload)
    del body["payload_sha256"]
    require(sha256_bytes(canonical_bytes(body)) == observed, f"{label}: payload digest mismatch")


def same(actual: object, expected: object, label: str) -> None:
    require(actual == expected, f"{label}: value changed")


def trim(values: Iterable[int]) -> Poly:
    result = list(values)
    require(result and all(type(item) is int for item in result), "invalid polynomial coefficients")
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def p_add(left: Poly, right: Poly) -> Poly:
    width = max(len(left), len(right))
    return trim(
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(width)
    )


def p_scale(poly: Poly, scalar: int) -> Poly:
    return trim(scalar * coefficient for coefficient in poly)


def p_neg(poly: Poly) -> Poly:
    return p_scale(poly, -1)


def p_sub(left: Poly, right: Poly) -> Poly:
    return p_add(left, p_neg(right))


def p_shift(poly: Poly, amount: int) -> Poly:
    require(amount >= 0, "negative polynomial shift")
    return poly if poly == (0,) else (0,) * amount + poly


def p_mul(left: Poly, right: Poly) -> Poly:
    if left == (0,) or right == (0,):
        return (0,)
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return trim(result)


def p_eval(poly: Poly, argument: int) -> int:
    result = 0
    for coefficient in reversed(poly):
        result = result * argument + coefficient
    return result


def p_affine(poly: Poly, slope: int, intercept: int) -> Poly:
    result: Poly = (0,)
    affine = (intercept, slope)
    for coefficient in reversed(poly):
        result = p_add(p_mul(result, affine), (coefficient,))
    return result


def p_content(poly: Poly) -> int:
    result = 0
    for coefficient in poly:
        result = math.gcd(result, abs(coefficient))
    return result


def p_exact_div(poly: Poly, divisor: int) -> Poly:
    require(divisor != 0 and all(coefficient % divisor == 0 for coefficient in poly), "inexact coefficient division")
    return trim(coefficient // divisor for coefficient in poly)


def p_primitive(poly: Poly) -> Poly:
    require(poly != (0,), "zero primitive polynomial")
    result = p_exact_div(poly, p_content(poly))
    return p_neg(result) if result[-1] < 0 else result


def pseudo_divide(dividend: Poly, divisor: Poly) -> tuple[Poly, Poly]:
    require(divisor != (0,) and len(dividend) >= len(divisor), "invalid pseudo-division")
    leading = divisor[-1]
    quotient: Poly = (0,)
    remainder = dividend
    unused_steps = len(dividend) - len(divisor) + 1
    while remainder != (0,) and len(remainder) >= len(divisor):
        offset = len(remainder) - len(divisor)
        top = remainder[-1]
        quotient = p_add(p_scale(quotient, leading), p_shift((top,), offset))
        remainder = p_sub(p_scale(remainder, leading), p_scale(p_shift(divisor, offset), top))
        unused_steps -= 1
    require(unused_steps >= 0, "pseudo-division step underflow")
    multiplier = leading**unused_steps
    return p_scale(quotient, multiplier), p_scale(remainder, multiplier)


def primitive_chain(first: Poly, second: Poly) -> tuple[Poly, ...]:
    result = [first, second]
    while True:
        _, remainder = pseudo_divide(result[-2], result[-1])
        if remainder == (0,):
            return tuple(result)
        result.append(p_primitive(remainder))


def dickson_basis(limit: int) -> tuple[Poly, ...]:
    rows: list[Poly] = [(2,), (0, 1)]
    for _ in range(2, limit + 1):
        rows.append(p_add(p_shift(rows[-1], 1), rows[-2]))
    return tuple(rows)


def recurrence_polynomial(index: int) -> Poly:
    previous: Poly = (1,)
    current: Poly = (0, 1)
    for _ in range(2, index + 1):
        previous, current = current, p_add(p_mul((0, 2), current), previous)
    return current


def source_pair(index: int, detector_coefficients: tuple[int, ...]) -> tuple[Poly, Poly]:
    dickson = dickson_basis(index)
    detector: Poly = (detector_coefficients[0],)
    for coefficient, basis in zip(detector_coefficients[1:], dickson[1 : len(detector_coefficients)], strict=True):
        detector = p_add(detector, p_scale(basis, coefficient))
    if index == 41:
        wrong_d0 = p_scale(dickson[0], detector_coefficients[0])
        for coefficient, basis in zip(detector_coefficients[1:], dickson[1 : len(detector_coefficients)], strict=True):
            wrong_d0 = p_add(wrong_d0, p_scale(basis, coefficient))
        require(wrong_d0 != detector, "fixed41 D0 convention")
        require(p_eval(wrong_d0, 4) == p_eval(detector, 4) - 1, "fixed41 D0 negative control")
    half_norm = p_sub(recurrence_polynomial(index), (1,))
    scaled_detector = p_affine(detector, 2, 0)
    if index == 41:
        scaled_detector = p_neg(scaled_detector)
    return half_norm, scaled_detector


def phase_41_rows(raw_rows: tuple[Poly, ...]) -> tuple[Poly, ...]:
    result = []
    for index, row in enumerate(raw_rows):
        transformed = p_affine(row, 8, 10)
        if index in (5, 21):
            transformed = p_exact_div(transformed, 2)
        require(transformed[0] > 0 and all(value >= 0 for value in transformed), f"phase row {index}: positivity")
        require(transformed[0] % 2 == 1 and all(value % 2 == 0 for value in transformed[1:]), f"phase row {index}: parity")
        result.append(transformed)
    return tuple(result)


def chain_relations(raw_rows: tuple[Poly, ...], divisors: tuple[int, ...], slope: int, intercept: int) -> tuple[dict[str, object], ...]:
    result = []
    for index in range(len(raw_rows) - 2):
        quotient, remainder = pseudo_divide(raw_rows[index], raw_rows[index + 1])
        sign = 1 if remainder[-1] > 0 else -1
        left = raw_rows[index + 1][-1] ** 2 * divisors[index]
        right = sign * p_content(remainder) * divisors[index + 2]
        quotient = p_scale(p_affine(quotient, slope, intercept), divisors[index + 1])
        common = math.gcd(abs(left), abs(right))
        for coefficient in quotient:
            common = math.gcd(common, abs(coefficient))
        result.append({
            "left": left // common,
            "quotient": p_exact_div(quotient, common),
            "right": right // common,
        })
    return tuple(result)


def f_trim(values: Iterable[Fraction]) -> FracPoly:
    result = list(values)
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def f_add(left: FracPoly, right: FracPoly) -> FracPoly:
    width = max(len(left), len(right))
    return f_trim(
        (left[index] if index < len(left) else Fraction())
        + (right[index] if index < len(right) else Fraction())
        for index in range(width)
    )


def f_scale(poly: FracPoly, scalar: Fraction) -> FracPoly:
    return f_trim(scalar * value for value in poly)


def f_mul(left: FracPoly, right: FracPoly) -> FracPoly:
    result = [Fraction()] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return f_trim(result)


def coefficient_vectors(relations: tuple[dict[str, object], ...]) -> tuple[tuple[FracPoly, FracPoly], ...]:
    result: list[tuple[FracPoly, FracPoly]] = [
        ((Fraction(1),), (Fraction(),)),
        ((Fraction(),), (Fraction(1),)),
    ]
    for relation in relations:
        quotient = tuple(Fraction(value) for value in relation["quotient"])
        denominator = Fraction(1, int(relation["right"]))
        result.append((
            f_scale(f_add(f_scale(result[-2][0], int(relation["left"])), f_scale(f_mul(quotient, result[-1][0]), -1)), denominator),
            f_scale(f_add(f_scale(result[-2][1], int(relation["left"])), f_scale(f_mul(quotient, result[-1][1]), -1)), denominator),
        ))
    return tuple(result)


def integral_vector(vector: tuple[FracPoly, FracPoly]) -> tuple[int, Poly, Poly]:
    denominator = 1
    for poly in vector:
        for value in poly:
            denominator = math.lcm(denominator, value.denominator)
    polys = [tuple(int(value * denominator) for value in poly) for poly in vector]
    common = denominator
    for poly in polys:
        for value in poly:
            common = math.gcd(common, abs(value))
    return denominator // common, trim(value // common for value in polys[0]), trim(value // common for value in polys[1])


def endpoint(rows: tuple[Poly, ...], relations: tuple[dict[str, object], ...], first: int, second: int) -> dict[str, object]:
    vectors = coefficient_vectors(relations)
    first_scale, a, b = integral_vector(vectors[first])
    second_scale, c, d = integral_vector(vectors[second])
    require(p_scale(rows[first], first_scale) == p_add(p_mul(a, rows[0]), p_mul(b, rows[1])), "first endpoint identity")
    require(p_scale(rows[second], second_scale) == p_add(p_mul(c, rows[0]), p_mul(d, rows[1])), "second endpoint identity")
    determinant = p_sub(p_mul(a, d), p_mul(b, c))
    require(len(determinant) == 1, "nonconstant endpoint determinant")
    return {"indices": (first, second), "scales": (first_scale, second_scale), "matrix": ((a, b), (c, d)), "determinant": determinant[0]}


def jacobi(numerator: int, denominator: int) -> int:
    require(denominator > 0 and denominator % 2 == 1, "invalid Jacobi denominator")
    numerator %= denominator
    sign = 1
    while numerator:
        while numerator % 2 == 0:
            numerator //= 2
            if denominator % 8 in (3, 5):
                sign = -sign
        numerator, denominator = denominator, numerator
        if numerator % 4 == denominator % 4 == 3:
            sign = -sign
        numerator %= denominator
    return sign if denominator == 1 else 0


def roots_mod(poly: Poly, modulus: int) -> list[int]:
    return [value for value in range(modulus) if p_eval(poly, value) % modulus == 0]


def common_roots(left: Poly, right: Poly, modulus: int) -> list[int]:
    return [value for value in range(modulus) if p_eval(left, value) % modulus == p_eval(right, value) % modulus == 0]


def bareiss(matrix: list[list[int]]) -> int:
    require(matrix and all(len(row) == len(matrix) for row in matrix), "nonsquare determinant matrix")
    data = [row[:] for row in matrix]
    sign = 1
    prior = 1
    for column in range(len(data) - 1):
        pivot_row = next((row for row in range(column, len(data)) if data[row][column]), None)
        require(pivot_row is not None, "singular determinant pivot")
        if pivot_row != column:
            data[column], data[pivot_row] = data[pivot_row], data[column]
            sign = -sign
        pivot = data[column][column]
        for row in range(column + 1, len(data)):
            for target in range(column + 1, len(data)):
                numerator = data[row][target] * pivot - data[row][column] * data[column][target]
                require(numerator % prior == 0, "inexact Bareiss division")
                data[row][target] = numerator // prior
            data[row][column] = 0
        prior = pivot
    return sign * data[-1][-1]


def resultant(left: Poly, right: Poly) -> int:
    m = len(left) - 1
    n = len(right) - 1
    size = m + n
    matrix = [[0] * size for _ in range(size)]
    left_desc = list(reversed(left))
    right_desc = list(reversed(right))
    for row in range(n):
        matrix[row][row : row + m + 1] = left_desc
    for row in range(m):
        matrix[n + row][row : row + n + 1] = right_desc
    return bareiss(matrix)


@lru_cache(maxsize=None)
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


def factor_product(factors: Iterable[tuple[int, int]], sign: int = 1) -> int:
    require(sign in (-1, 1), "invalid factorization sign")
    result = sign
    for prime, exponent in factors:
        require(is_prime(prime) and exponent > 0, f"invalid prime factor {prime}")
        result *= prime**exponent
    return result


def odd_part(value: int) -> int:
    require(value > 0, "nonpositive support constant")
    while value % 2 == 0:
        value //= 2
    return value


def mod_trim(poly: Iterable[int], prime: int) -> Poly:
    return trim(coefficient % prime for coefficient in poly)


def mod_add(left: Poly, right: Poly, prime: int) -> Poly:
    width = max(len(left), len(right))
    return mod_trim(
        (
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
            for index in range(width)
        ),
        prime,
    )


def mod_sub(left: Poly, right: Poly, prime: int) -> Poly:
    return mod_add(left, tuple(-value for value in right), prime)


def mod_mul(left: Poly, right: Poly, prime: int) -> Poly:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = (result[i + j] + a * b) % prime
    return mod_trim(result, prime)


def mod_divmod(dividend: Poly, divisor: Poly, prime: int) -> tuple[Poly, Poly]:
    remainder = list(mod_trim(dividend, prime))
    divisor = mod_trim(divisor, prime)
    require(divisor != (0,), "zero modular divisor")
    quotient = [0] * max(1, len(remainder) - len(divisor) + 1)
    inverse = pow(divisor[-1], -1, prime)
    while tuple(remainder) != (0,) and len(remainder) >= len(divisor):
        coefficient = remainder[-1] * inverse % prime
        offset = len(remainder) - len(divisor)
        quotient[offset] = coefficient
        for index, value in enumerate(divisor):
            remainder[index + offset] = (remainder[index + offset] - coefficient * value) % prime
        remainder = list(mod_trim(remainder, prime))
    return mod_trim(quotient, prime), tuple(remainder)


def mod_gcd(left: Poly, right: Poly, prime: int) -> Poly:
    require(is_prime(prime), "modular modulus is not prime")
    left = mod_trim(left, prime)
    right = mod_trim(right, prime)
    while right != (0,):
        _, remainder = mod_divmod(left, right, prime)
        left, right = right, remainder
    inverse = pow(left[-1], -1, prime)
    return mod_trim((coefficient * inverse for coefficient in left), prime)


def verify_modular_bezout(record: object, left: Poly, right: Poly, prime: int, expected_gcd: Poly, label: str, *, telescope_names: bool) -> None:
    record = keys(record, {"prime", "gcd", "left", "right"} if telescope_names else {"index", "prime", "gcd", "bezout_left", "bezout_right"}, label)
    same(integer(record["prime"], f"{label}.prime"), prime, f"{label}.prime")
    gcd_poly = polynomial(record["gcd"], f"{label}.gcd")
    first_key, second_key = ("left", "right") if telescope_names else ("bezout_left", "bezout_right")
    first = polynomial(record[first_key], f"{label}.{first_key}")
    second = polynomial(record[second_key], f"{label}.{second_key}")
    same(gcd_poly, expected_gcd, f"{label}.gcd")
    same(mod_gcd(left, right, prime), expected_gcd, f"{label}.independent gcd")
    same(mod_add(mod_mul(first, left, prime), mod_mul(second, right, prime), prime), expected_gcd, f"{label}.Bezout identity")


def poly_sha256(poly: Poly) -> str:
    return sha256_bytes(canonical_bytes({"coefficients": encode(poly)}))


def recurrence_value(a: int, n: int) -> int:
    require(a >= 0 and n >= 0, "negative recurrence input")
    if n == 0:
        return 1
    previous, current = 1, a
    for _ in range(1, n):
        previous, current = current, 2 * a * current + previous
    return current


def lucas_v(p: int, n: int) -> int:
    """Return V_n(p,-1), independently of the maintained replay."""

    require(p >= 0 and n >= 0, "negative V input")
    if n == 0:
        return 2
    previous, current = 2, p
    for _ in range(1, n):
        previous, current = current, p * current + previous
    return current


def lucas_u(p: int, n: int) -> int:
    """Return U_n(p,-1), independently of the maintained replay."""

    require(p >= 0 and n >= 0, "negative U input")
    if n == 0:
        return 0
    previous, current = 0, 1
    for _ in range(1, n):
        previous, current = current, p * current + previous
    return current


def v2(value: int) -> int:
    """Use the natural-number convention v2(0)=0."""

    require(value >= 0, "negative valuation input")
    exponent = 0
    while value and value % 2 == 0:
        value //= 2
        exponent += 1
    return exponent


def row_stream_digest(rows: Iterable[tuple[object, ...]]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(canonical_bytes(row))
    return digest.hexdigest()


def verify_propagation() -> None:
    observed = load_json(PROPAGATION_PATH, max_bytes=8 * 1024, strings_only_numbers=False)
    composition = []
    for a in range(17):
        for m in range(9):
            for n in range(1, 16, 2):
                direct = recurrence_value(a, m * n)
                nested = recurrence_value(recurrence_value(a, n), m)
                require(direct == nested, f"propagation composition ({a},{m},{n})")
                composition.append((a, m, n, direct, nested))
    mod_four = []
    for a in range(2, 64, 4):
        for n in range(1, 42, 2):
            residue = recurrence_value(a, n) % 4
            require(residue == 2, f"propagation mod four ({a},{n})")
            mod_four.append((a, n, residue))
    mod_eight = []
    for a in range(6, 64, 8):
        for n in (17, 41):
            residue = recurrence_value(a, n) % 8
            require(residue == 6, f"propagation mod eight ({a},{n})")
            mod_eight.append((a, n, residue))

    even_valuation = []
    for a in (2, 6, 10):
        p = 2 * a
        require(p % 8 == 4, f"propagation P phase ({a})")
        for n in (2, 4, 6, 8, 10, 12, 16, 24):
            f = recurrence_value(a, n)
            v = lucas_v(p, n)
            require(v == 2 * f, f"propagation V=2F ({a},{n})")
            observed_valuation = v2(f - 1)
            expected_valuation = 2 * v2(n) + 1
            require(observed_valuation == expected_valuation, f"even valuation ({a},{n})")
            require(v2(v - 2) == expected_valuation + 1, f"V valuation ({a},{n})")
            even_valuation.append(
                (a, p, n, v2(n), str(v - 2), v2(v - 2), str(f - 1), observed_valuation, expected_valuation)
            )

    local_two = []
    tables = {2: (1, 2, 1, 6), 6: (1, 6, 1, 2)}
    odd_codes = {
        (2, 1): "ODD_2ADIC_ADMISSIBLE",
        (2, 3): "ODD_UNIT_CLASS_REJECTION",
        (6, 1): "ODD_UNIT_CLASS_REJECTION",
        (6, 3): "ODD_2ADIC_ADMISSIBLE",
    }
    for a_mod_eight, table in tables.items():
        for n_mod_four, residue in enumerate(table):
            observed_residue = recurrence_value(a_mod_eight, n_mod_four) % 8
            require(observed_residue == residue, f"local-two table ({a_mod_eight},{n_mod_four})")
            code = "EVEN_ODD_VALUATION_REJECTION" if n_mod_four % 2 == 0 else odd_codes[(a_mod_eight, n_mod_four)]
            local_two.append((a_mod_eight, n_mod_four, observed_residue, (observed_residue - 1) % 8, code))
    hostile_left = recurrence_value(1, 4)
    hostile_right = recurrence_value(recurrence_value(1, 2), 2)
    formula_left_bad = lucas_v(4, 2) - 2
    formula_right_bad = (4**2 + 4) * lucas_u(4, 1) ** 2
    formula_left_good = lucas_v(4, 4) - 2
    formula_right_good = (4**2 + 4) * lucas_u(4, 2) ** 2
    require(formula_left_bad == 16 and formula_right_bad == 20, "guarded U hostile values")
    require(formula_left_bad != formula_right_bad, "guarded U hostile rejection")
    require(formula_left_good == formula_right_good == 320, "guarded U valid control")
    witnesses = {
        "cross_phase_a2_n3": {"f": str(recurrence_value(2, 3)), "f_minus_one_mod_8": 5},
        "cross_phase_a6_n5": {"f": str(recurrence_value(6, 5)), "f_minus_one_mod_8": 5},
        "surviving_a2_n5": {
            "f": str(recurrence_value(2, 5)),
            "f_minus_one": str(recurrence_value(2, 5) - 1),
            "f_minus_one_mod_8": 1,
            "integer_square_bracket": [26, 27],
        },
    }
    require(recurrence_value(2, 3) - 1 == 37, "F3(2)-1 witness")
    require(recurrence_value(6, 5) - 1 == 128765, "F5(6)-1 witness")
    require(recurrence_value(2, 5) - 1 == 681, "F5(2)-1 witness")
    expected_result = {
        "arithmetic": {"backend": "python-int", "exact_arbitrary_precision": True, "randomness": False},
        "composition": {
            "a_bounds_inclusive": [0, 16], "all_equal": True, "cases": 1224,
            "m_bounds_inclusive": [0, 8], "odd_n_bounds_inclusive": [1, 15],
            "rows_sha256": row_stream_digest(composition),
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
                "a", "p", "n", "v2_n", "v_n_minus_two", "v2_v_n_minus_two",
                "f_n_minus_one", "observed_v2_f_n_minus_one", "expected_v2_f_n_minus_one",
            ],
            "rows": [list(row) for row in even_valuation],
            "rows_sha256": row_stream_digest(even_valuation),
            "theorem_formula": "v2(F_n(A)-1)=2*v2(n)+1 for A=2 mod 4 and positive even n",
        },
        "hostile_controls": {
            "guarded_u_formula": {
                "false_case": {"m": 1, "n": 2, "p": 4, "right": formula_right_bad, "v_n_minus_two": formula_left_bad},
                "identity_only_when_m_even": True,
                "valid_case": {"m": 2, "n": 4, "p": 4, "right": formula_right_good, "v_n_minus_two": formula_left_good},
            },
            "n_zero": {
                "a": 2,
                "f_n_minus_one": str(recurrence_value(2, 0) - 1),
                "is_divisible_by_17": True,
                "is_divisible_by_41": True,
                "n": 0,
                "v2_convention": v2(recurrence_value(2, 0) - 1),
            },
            "phase_boundary_n2": [
                {"a": a, "a_mod_4": a % 4, "v2_f_n_minus_one": v2(recurrence_value(a, 2) - 1)}
                for a in (0, 1, 3, 4)
            ],
            "wrong_phase_n2": {"a": 0, "a_mod_4": 0, "observed_v2": v2(recurrence_value(0, 2) - 1)},
        },
        "hostile_even_inner": {
            "a": 1, "composition_fails": True, "direct_f_4": hostile_left,
            "inner_n": 2, "nested_f_2_f_2": hostile_right, "outer_m": 2,
        },
        "mod_eight": {
            "a_bounds_inclusive": [0, 63], "a_residue": 6,
            "all_residues_equal_six": True, "cases": 16,
            "indices": [17, 41], "modulus": 8,
            "rows_sha256": row_stream_digest(mod_eight),
        },
        "mod_four": {
            "a_bounds_inclusive": [0, 63], "a_residue": 2,
            "all_residues_equal_two": True, "cases": 336, "modulus": 4,
            "odd_n_bounds_inclusive": [1, 41], "rows_sha256": row_stream_digest(mod_four),
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
            "complete_tables": {"a_mod_8_2": [1, 2, 1, 6], "a_mod_8_6": [1, 6, 1, 2]},
            "cross_phase_square_class": 5,
            "surviving_unit_square_class": 1,
        },
        "nonclaims": {
            "bounded_replay_is_proof": False, "canonical_status_changed": False,
            "even_inner_composition": False,
            "odd_2adic_admissible_implies_global_square": False,
            "source_terminal_scope_enlarged": False,
            "terminal_count": "1/4", "uniform_prime_index_theorem": False,
        },
        "witnesses": witnesses,
    }
    require(hostile_left == 17 and hostile_right == 19 and hostile_left != hostile_right, "propagation hostile control")
    require(len(composition) == 1224 and len(mod_four) == 336 and len(mod_eight) == 16, "propagation row count")
    require(len(even_valuation) == 24 and len(local_two) == 8, "propagation parity row count")
    expected = {
        "marker": "SHIFTED_SQUARE_PROPAGATION_OK",
        "result": expected_result,
        "result_sha256": sha256_bytes(canonical_bytes(expected_result)),
        "schema": "SHIFTED-SQUARE-PROPAGATION-REPLAY-V2",
    }
    same(canonical_bytes(observed), canonical_bytes(expected), "propagation packet")


def fixed17_rows() -> tuple[Poly, ...]:
    return (
        (-1, 17, 0, 816, 0, 11424, 0, 71808, 0, 239360, 0, 452608, 0, 487424, 0, 278528, 0, 65536),
        (-3, -4, -80, -32, -208, -32, 4480, 0, 26112, 0, 54272, 0, 49152, 0, 16384),
        (-1, 32, 20, 1228, 176, 12784, 288, 50240, 128, 90880, 0, 76800, 0, 24576),
        (9, 10, 304, 136, 3080, 448, 12128, 576, 22144, 256, 18944, 0, 6144),
        (-1, -4, -20, 12, -368, 464, -1504, 1728, -2176, 2304, -1024, 1024),
        (15, 40, 448, 184, 5216, -128, 18368, -768, 24832, -512, 11264),
        (73, -458, 3688, -3088, 16432, -5152, 24576, -2048, 11776, 512),
        (51, -322, 2590, -2268, 11576, -4096, 17344, -2176, 8320),
        (23, 854, -1200, 3336, -3232, 4352, -2048, 1792),
        (-1, -91, 82, -240, 216, -160, 128),
        (1, 41, -2, 104, -8, 64),
        (-5, 3, 18, 8, 40),
        (-5, 158, 8, 248),
        (187, 18, 296),
        (-3, 10),
    )


def prime_divisors(value: int) -> set[int]:
    value = abs(value)
    result: set[int] = set()
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            result.add(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        result.add(value)
    return result


def verify_fixed17_exceptions() -> None:
    rows = fixed17_rows()
    a = (0, 1)
    identities = (
        (1, rows[0], p_add(p_scale(p_mul(p_mul(a, a), a), 4), p_scale(a, 5)), rows[1], 1, rows[2]),
        (3, rows[1], p_scale(a, 2), rows[2], -1, rows[3]),
        (1, rows[2], p_scale(a, 4), rows[3], 1, rows[4]),
        (1, rows[3], p_add(p_scale(a, 6), (6,)), rows[4], 1, rows[5]),
        (242, rows[4], p_add(p_scale(a, 22), (-21,)), rows[5], 1, rows[6]),
        (1, rows[5], p_add(p_scale(a, 22), (-507,)), rows[6], 726, rows[7]),
        (4225, rows[6], p_add(p_scale(a, 260), (6048,)), rows[7], -1, rows[8]),
        (98, rows[7], p_add(p_scale(a, 455), (401,)), rows[8], 4225, rows[9]),
        (2, rows[8], p_add(p_scale(a, 28), (3,)), rows[9], 49, rows[10]),
        (4, rows[9], p_add(p_scale(a, 8), (-9,)), rows[10], -1, rows[11]),
        (25, rows[10], p_add(p_scale(a, 40), (-13,)), rows[11], 8, rows[12]),
        (961, rows[11], p_add(p_scale(a, 155), (26,)), rows[12], -25, rows[13]),
        (5476, rows[12], p_add(p_scale(a, 4588), (-131,)), rows[13], 961, rows[14]),
        (25, rows[13], p_add(p_scale(a, 740), (267,)), rows[14], 5476, (1,)),
    )
    exceptional: set[int] = set()
    for index, (left_scale, left, quotient, middle, right_scale, right) in enumerate(identities):
        same(p_scale(left, left_scale), p_add(p_mul(quotient, middle), p_scale(right, right_scale)), f"fixed17 PRS identity {index}")
        exceptional.update(prime_divisors(left_scale))
        exceptional.update(prime_divisors(right_scale))
    exceptional.discard(2)
    same(exceptional, {3, 5, 7, 11, 13, 31, 37}, "fixed17 exceptional prime set")
    # Every exceptional residue is evaluated, and the polynomial identities
    # are checked again after the source phase A=8*k+2.  This catches a bad
    # exceptional prime, phase, coefficient, sign, or omitted residue.
    for prime in sorted(exceptional):
        require(is_prime(prime), f"fixed17 exceptional composite {prime}")
        for k in range(prime):
            argument = 8 * k + 2
            values = tuple(p_eval(row, argument) for row in rows)
            for index, (left_scale, _, quotient, _, right_scale, _) in enumerate(identities):
                right_value = 1 if index == 13 else values[index + 2]
                require(
                    left_scale * values[index]
                    == p_eval(quotient, argument) * values[index + 1] + right_scale * right_value,
                    f"fixed17 exceptional specialization p={prime} k={k} row={index}",
                )


def independent_chains() -> dict[str, object]:
    source = source_pair(41, UNIT_41)
    require(tuple(len(row) - 1 for row in source) == (41, 40), "fixed41 source degrees")
    raw = primitive_chain(*source)
    require(tuple(len(row) - 1 for row in raw) == tuple(range(41, 1, -1)) + (0,), "fixed41 source chain degrees")
    phase = phase_41_rows(raw)
    divisors = tuple(2 if index in (5, 21) else 1 for index in range(len(raw)))
    relations = chain_relations(raw, divisors, 8, 10)
    source_endpoint = endpoint(phase, relations, 39, 40)
    require(source_endpoint["scales"] == (1, 1) and source_endpoint["determinant"] == -16, "fixed41 source endpoint")
    ((source_a, source_b), (source_c, source_d)) = source_endpoint["matrix"]
    alpha = p_exact_div(source_a, 2)
    beta = p_neg(source_b)
    gamma = p_exact_div(source_c, 2)
    delta = p_neg(source_d)
    require(p_sub(p_mul(beta, gamma), p_mul(alpha, delta)) == (-8,), "fixed41 reduced source determinant")
    coefficient_rows = primitive_chain(gamma, alpha)
    require(len(coefficient_rows) == 39 and coefficient_rows[-2:] == ((17, 14), (1,)), "fixed41 coefficient chain")
    coefficient_relations = chain_relations(coefficient_rows, (1,) * len(coefficient_rows), 1, 0)
    coefficient_vectors_raw = coefficient_vectors(coefficient_relations)
    coefficient_vectors_int = tuple(integral_vector(vector) for vector in coefficient_vectors_raw)
    for index, (scale, left, right) in enumerate(coefficient_vectors_int):
        same(p_scale(coefficient_rows[index], scale), p_add(p_mul(left, coefficient_rows[0]), p_mul(right, coefficient_rows[1])), f"coefficient vector {index}")
    return {
        "source_pair": source,
        "source_raw": raw,
        "source_rows": phase,
        "source_relations": relations,
        "source_endpoint": source_endpoint,
        "alpha": alpha,
        "beta": beta,
        "gamma": gamma,
        "delta": delta,
        "coefficient_rows": coefficient_rows,
        "coefficient_relations": coefficient_relations,
        "coefficient_vectors": coefficient_vectors_int,
    }


def in_shifted_parameter(coefficients: tuple[int, ...]) -> Poly:
    result: Poly = (0,)
    power: Poly = (1,)
    shifted = (1, 1)
    for coefficient in coefficients:
        result = p_add(result, p_scale(power, coefficient))
        power = p_mul(power, shifted)
    return result


def block_coefficients() -> tuple[Poly, Poly, Poly, Poly]:
    n3 = in_shifted_parameter((1_234_893, 15_376_256, 65_740_800, 96_890_880))
    n4 = in_shifted_parameter((712_955, 10_451_080, 59_168_000, 153_630_720, 155_025_408))
    c = p_scale(in_shifted_parameter((2_404_585, 37_847_145, 228_615_264, 628_471_040, 664_760_320)), 32)
    d = p_neg(in_shifted_parameter((44_423_683, 797_293_664, 5_867_790_592, 22_132_903_936, 42_813_882_368, 34_035_728_384)))
    return n3, n4, c, d


def verify_block_spin(actual: object, n3: Poly, n4: Poly) -> None:
    actual = keys(actual, {
        "C", "L", "common_roots_C_L", "common_roots_a_C", "constant",
        "constant_factorization", "direct_reduction_count", "direct_reduction_sha256",
        "h_counts", "k_counts", "lifts_mod_25", "lifts_mod_343", "lifts_mod_49",
        "quotient_rows_mod_7", "resultant_C_L", "resultant_a_C", "theorem",
    }, "block coefficient spin")
    c_poly: Poly = (25_782_221, 41_783_040, 16_955_904)
    l_poly: Poly = (1_882_609, 1_526_536)
    same(polynomial(actual["C"], "block spin C"), c_poly, "block spin C")
    same(polynomial(actual["L"], "block spin L"), l_poly, "block spin L")
    same(p_scale(n4, 10), p_add(p_mul((21, 16), n3), c_poly), "block spin identity zero")
    same(p_scale(n3, 49), p_add(p_mul((340, 280), c_poly), p_scale(l_poly, 9)), "block spin identity one")
    same(p_scale(c_poly, 14_641), p_add(p_mul((200_184, 162_624), l_poly), (609_297_605,)), "block spin identity two")
    resultant_ac = resultant(n3, c_poly)
    resultant_cl = resultant(c_poly, l_poly)
    same(resultant_ac, 2**24 * 3**6 * 5 * 19**6 * 83**6, "block spin resultant a,C")
    same(resultant_cl, 2**6 * 5 * 7**2 * 19**4 * 83**4, "block spin resultant C,L")
    common_ac = {str(prime): sorted(set(roots_mod(n3, prime)) & set(roots_mod(c_poly, prime))) for prime in (3, 5, 19, 83)}
    common_cl = {str(prime): sorted(set(roots_mod(c_poly, prime)) & set(roots_mod(l_poly, prime))) for prime in (5, 7, 19, 83)}
    lifts_25 = [(value, p_eval(n3, value) % 25, p_eval(c_poly, value) % 25) for value in range(1, 25, 5)]
    lifts_49 = [(value, p_eval(c_poly, value) % 49, p_eval(l_poly, value) % 49) for value in range(5, 49, 7)]
    lifts_343 = [(value, p_eval(c_poly, value) % 343, p_eval(l_poly, value) % 343) for value in range(47, 343, 49)]
    quotient_rows = [
        (value, p_eval(n3, value) % 7, (p_eval(c_poly, value) // 7) % 7, (p_eval(l_poly, value) // 7) % 7)
        for value in (5, 12, 19, 26, 33, 40)
    ]
    require(common_ac == {"3": [], "5": [1], "19": [], "83": []}, "block spin common roots a,C")
    require(common_cl == {"5": [1], "7": [5], "19": [], "83": []}, "block spin common roots C,L")
    require([value for value, left, right in lifts_49 if left == right == 0] == [47], "block spin mod49 lift")
    require(all(not (left == right == 0) for _, left, right in lifts_25 + lifts_343), "block spin higher lifts")
    digest = hashlib.sha256()
    h_counts: Counter[int] = Counter()
    k_counts: Counter[int] = Counter()
    for parameter in range(32_459):
        a_value = p_eval(n3, parameter)
        b_value = p_eval(n4, parameter)
        c_value = p_eval(c_poly, parameter)
        l_value = p_eval(l_poly, parameter)
        h = math.gcd(a_value, c_value)
        require(h in (1, 5) and l_value % h == 0, f"block spin h at {parameter}")
        a1, c1, l1 = a_value // h, c_value // h, l_value // h
        k = math.gcd(c1, l1)
        require(k in (1, 7, 49), f"block spin k at {parameter}")
        require((h == 5) == (parameter % 5 == 1), f"block spin h class at {parameter}")
        require((k == 49) == (parameter % 49 == 47), f"block spin k49 class at {parameter}")
        require((k in (7, 49)) == (parameter % 7 == 5), f"block spin k7 class at {parameter}")
        c2, l2 = c1 // k, l1 // k
        reduction = (
            jacobi(h, b_value) * jacobi(k, a1) * jacobi(49 // k, c2)
            * jacobi(-1, k) * jacobi(5 // h, l2) * jacobi(49 // k, l2)
            * jacobi(10 // h, a1)
        )
        require(reduction == jacobi(a_value, b_value) == -1, f"block coefficient reduction at {parameter}")
        require(jacobi(-a_value, b_value) == 1, f"block coefficient character at {parameter}")
        h_counts[h] += 1
        k_counts[k] += 1
        digest.update(f"{parameter}:{h}:{k}:{reduction}\n".encode())
    expected = {
        "C": c_poly,
        "L": l_poly,
        "common_roots_C_L": common_cl,
        "common_roots_a_C": common_ac,
        "constant": 609_297_605,
        "constant_factorization": [["5", "1"], ["7", "2"], ["19", "2"], ["83", "2"]],
        "direct_reduction_count": 32_459,
        "direct_reduction_sha256": digest.hexdigest(),
        "h_counts": dict(sorted(h_counts.items())),
        "k_counts": dict(sorted(k_counts.items())),
        "lifts_mod_25": lifts_25,
        "lifts_mod_343": lifts_343,
        "lifts_mod_49": lifts_49,
        "quotient_rows_mod_7": quotient_rows,
        "resultant_C_L": resultant_cl,
        "resultant_a_C": resultant_ac,
        "theorem": "J(-a(j),b(j))=1 for every j>=0",
    }
    same(actual, encode(expected), "block coefficient spin object")


def verify_block_gcd(actual: object, rows: tuple[Poly, ...], coefficients: tuple[Poly, Poly, Poly, Poly]) -> None:
    actual = keys(actual, {
        "common_mod_7", "direct_check_count", "direct_check_sha256", "exceptional_count",
        "lifts_mod_49", "missing_correction_failure_count", "raw_transfer_failure_count",
        "roots_4637_q5", "roots_4637_q6", "support_root_tables",
    }, "block gcd certificate")
    q0, q1, _, _, _, q5, q6 = rows
    n3, n4, c, d = coefficients
    common_seven = [value for value in range(7) if p_eval(q5, value) % 7 == p_eval(q6, value) % 7 == 0]
    lifts = [(value, p_eval(q5, value) % 49, p_eval(q6, value) % 49) for value in range(0, 49, 7)]
    require(common_seven == [0] and all((left, right) == (42, 7) for _, left, right in lifts), "block gcd seven-adic data")
    names = [f"Q{index}" for index in range(7)] + ["a", "b", "c", "d"]
    polys = list(rows) + [n3, n4, c, d]
    root_tables = {
        str(prime): {name: roots_mod(poly, prime) for name, poly in zip(names, polys, strict=True)}
        for prime in (7, 4_637)
    }
    require(root_tables["7"] == {
        "Q0": [3], "Q1": [5], "Q2": [4], "Q3": [4], "Q4": [1, 2],
        "Q5": [0], "Q6": [0], "a": [1], "b": [], "c": [1], "d": [],
    }, "block mod7 table")
    require(root_tables["4637"] == {
        "Q0": [723], "Q1": [3603], "Q2": [3039, 3502], "Q3": [1462, 4491],
        "Q4": [173, 1721, 4621], "Q5": [], "Q6": [], "a": [],
        "b": [1983, 2128], "c": [], "d": [1983, 2128],
    }, "block mod4637 table")
    digest = hashlib.sha256()
    exceptional = raw_failures = missing = 0
    for parameter in range(32_459):
        q0_value, q1_value, q5_value, q6_value = (
            p_eval(poly, parameter) for poly in (q0, q1, q5, q6)
        )
        endpoint_gcd = math.gcd(q5_value, q6_value)
        require(endpoint_gcd == (7 if parameter % 7 == 0 else 1), f"block endpoint gcd at {parameter}")
        exceptional += endpoint_gcd == 7
        initial = jacobi(q1_value, q0_value)
        reduced = jacobi(q6_value // endpoint_gcd, q5_value // endpoint_gcd)
        require(initial == jacobi(-1, endpoint_gcd) * reduced, f"block factor-safe transfer at {parameter}")
        raw = reduced if endpoint_gcd == 1 else jacobi(q6_value, q5_value)
        raw_failures += initial != raw
        missing += initial != reduced
        coefficient_symbol = jacobi(-p_eval(n3, parameter), p_eval(n4, parameter))
        require(coefficient_symbol == 1, f"block coefficient spin repeat at {parameter}")
        digest.update(f"{parameter}:{endpoint_gcd}:{initial}:{reduced}:{coefficient_symbol}\n".encode())
    expected = {
        "common_mod_7": common_seven,
        "direct_check_count": 32_459,
        "direct_check_sha256": digest.hexdigest(),
        "exceptional_count": exceptional,
        "lifts_mod_49": lifts,
        "missing_correction_failure_count": missing,
        "raw_transfer_failure_count": raw_failures,
        "roots_4637_q5": [],
        "roots_4637_q6": [],
        "support_root_tables": root_tables,
    }
    require((exceptional, raw_failures, missing) == (4_637, 4_637, 4_637), "block negative-control counts")
    same(actual, encode(expected), "block gcd object")


def verify_block(chains: dict[str, object]) -> None:
    payload = load_json(BLOCK_PATH, max_bytes=250_000, strings_only_numbers=True)
    keys(payload, {
        "adjacent_identities", "block_matrix", "boundary", "claim_ceiling",
        "coefficient_spin", "determinant", "factor_safe_identity", "gcd_certificate",
        "normalization", "payload_sha256", "rows", "schema", "upstream",
    }, "block payload")
    verify_payload_digest(payload, "block payload")
    same(payload["schema"], "sm2.outer41-jacobi-block.v1", "block schema")
    same(payload["claim_ceiling"], "exact_block_certificate_not_lean_or_full_chain", "block claim ceiling")
    same(payload["normalization"], {"A": "8*j+10", "Q5_divisor": "2", "boundary_A": "2", "boundary_j": "-1", "domain": "j>=0"}, "block normalization")
    same(payload["upstream"], {
        "path": "experiments/sm2_four_translate/interpolation/outer41_verify.gp",
        "resultant_g_u": "-1", "resultant_positive_unit_half_norm": str(2**1600),
        "resultant_scaling": "2^(41*40)/2^40", "sha256": SOURCE_41_SHA256,
    }, "block upstream")
    same(
        sha256_bytes(read_bounded(SOURCE_41_PATH, max_bytes=128 * 1024)),
        SOURCE_41_SHA256,
        "block upstream source hash",
    )
    raw_rows = chains["source_raw"]
    rows = []
    for index, row in enumerate(raw_rows[:7]):
        transformed = p_affine(row, 8, 10)
        if index == 5:
            transformed = p_exact_div(transformed, 2)
        rows.append(transformed)
    rows_tuple = tuple(rows)
    expected_rows = []
    residues = (1, 3, 3, 7, 5, None, 7)
    for index, row in enumerate(rows_tuple):
        entry: dict[str, object] = {
            "coefficients": encode(row), "degree": str(len(row) - 1), "index": str(index),
            "mod_8": str(residues[index]) if index != 5 else "phase-dependent",
        }
        if index == 5:
            even = p_affine(row, 2, 0)
            odd = p_affine(row, 2, 1)
            require(even[0] % 8 == 1 and odd[0] % 8 == 5, "block Q5 phase")
            entry["phase_mod_8"] = {"j_even": "1", "j_odd": "5"}
        expected_rows.append(entry)
    same(payload["rows"], expected_rows, "block rows")
    identity_data = (
        (10, (21, 16), 1),
        (49, (340, 280), 1),
        (43_923, (66_728, 54_208), 245),
        (2_486_929, (5_647_827, 4_579_608), 117_128),
        (1_053_586_681, (8_300_826_952, 6_552_043_904), 7_460_787),
    )
    expected_identities = []
    for index, (left_scale, quotient, right_scale) in enumerate(identity_data):
        same(p_scale(rows_tuple[index], left_scale), p_add(p_mul(quotient, rows_tuple[index + 1]), p_scale(rows_tuple[index + 2], right_scale)), f"block adjacent identity {index}")
        expected_identities.append(encode({
            "index": index, "left_row": index, "left_scale": left_scale,
            "middle_row": index + 1, "quotient": quotient,
            "right_row": index + 2, "right_scale": right_scale,
        }))
    same(payload["adjacent_identities"], expected_identities, "block adjacent identity records")
    n3, n4, c, d = block_coefficients()
    same(p_scale(rows_tuple[5], 4), p_add(p_mul(p_neg(n3), rows_tuple[0]), p_mul(n4, rows_tuple[1])), "block first matrix row")
    same(rows_tuple[6], p_add(p_mul(c, rows_tuple[0]), p_mul(d, rows_tuple[1])), "block second matrix row")
    determinant = p_sub(p_mul(p_neg(n3), d), p_mul(n4, c))
    same(determinant, (-(32_459**2),), "block determinant identity")
    expected_matrix = encode({"n3": n3, "n4": n4, "c": c, "d": d, "determinant": -(32_459**2)})
    same(payload["block_matrix"], expected_matrix, "block matrix")
    same(payload["determinant"], {"factorization": [["7", "1"], ["4637", "1"]], "matrix_determinant": str(-(32_459**2)), "s": "32459"}, "block determinant record")
    require(7 * 4_637 == 32_459 and is_prime(4_637), "block determinant factorization")
    verify_block_spin(payload["coefficient_spin"], n3, n4)
    verify_block_gcd(payload["gcd_certificate"], rows_tuple, (n3, n4, c, d))
    boundary_q0 = p_eval(rows_tuple[0], -1)
    boundary_q1 = p_eval(rows_tuple[1], -1)
    same(payload["boundary"], {"A": "2", "Q0": str(boundary_q0), "Q1": str(boundary_q1), "jacobi_Q1_Q0": str(jacobi(boundary_q1, boundary_q0))}, "block boundary")
    same(payload["factor_safe_identity"], {
        "chi4_g": "J(-1,g)", "g": "7 iff j mod 7 = 0; otherwise 1",
        "phase_10": "A=16*t+10; exceptional iff t mod 7=0",
        "phase_18": "A=16*t+18; exceptional iff t mod 7=3",
        "statement": "J(Q1,Q0)=chi4(g)*J(Q6/g,Q5/g)",
    }, "block factor-safe statement")


def build_p17_control() -> dict[str, object]:
    half_norm, detector = source_pair(17, UNIT_17)
    scaled_resultant = abs(resultant(half_norm, detector))
    same(scaled_resultant, 2**224, "fixed17 scaled resultant")
    reference_half_norm = p_eval(half_norm, 2)
    reference_detector = p_eval(detector, 2)
    same((reference_half_norm, reference_detector), (22_768_774_561, 532_303_029), "fixed17 reference values")
    same(jacobi(reference_detector, reference_half_norm), -1, "fixed17 reference Jacobi")
    for parameter in range(128):
        argument = 8 * parameter + 2
        same(jacobi(p_eval(detector, argument), p_eval(half_norm, argument)), -1, f"fixed17 phase control {parameter}")
    return {
        "bounded_phase_checks": 128,
        "claim": "exact_source_and_reference_control; bounded_phase_is_diagnostic",
        "dickson_coefficients": UNIT_17,
        "reference_A": 2,
        "reference_detector": reference_detector,
        "reference_half_norm": reference_half_norm,
        "reference_jacobi": -1,
        "scaled_resultant_abs": scaled_resultant,
        "scaled_resultant_factorization": ((2, 224),),
    }


def verify_certificate(chains: dict[str, object]) -> None:
    payload = load_json(CERTIFICATE_PATH, max_bytes=2_000_000, strings_only_numbers=True)
    keys(payload, {
        "claim_ceiling", "coefficient_chain", "downstream_change", "normalization",
        "p17_control", "payload_sha256", "plug_back", "proof_dag", "schema",
        "source_chain", "upstream",
    }, "certificate payload")
    verify_payload_digest(payload, "certificate payload")
    same(payload["schema"], "sm2.outer41-jacobi-certificate.v1", "certificate schema")
    same(payload["claim_ceiling"], "two_level_exact_certificate_not_lean_or_packet_closure", "certificate claim ceiling")
    same(payload["upstream"], {"path": "experiments/sm2_four_translate/interpolation/outer41_verify.gp", "sha256": SOURCE_41_SHA256}, "certificate upstream")
    same(
        sha256_bytes(read_bounded(SOURCE_41_PATH, max_bytes=128 * 1024)),
        SOURCE_41_SHA256,
        "certificate upstream hash",
    )
    same(payload["normalization"], {"A": "8*j+10", "boundary_A": "2", "divided_rows": ["5", "21"], "domain": "j>=0"}, "certificate normalization")
    same(payload["p17_control"], encode(build_p17_control()), "certificate fixed17 control")

    source_rows = chains["source_rows"]
    source_endpoint = chains["source_endpoint"]
    alpha: Poly = chains["alpha"]
    beta: Poly = chains["beta"]
    gamma: Poly = chains["gamma"]
    delta: Poly = chains["delta"]
    source_object = keys(payload["source_chain"], {
        "alpha", "beta", "boundary_A_2", "degrees", "delta", "endpoint",
        "gamma", "row_count", "rows_sha256", "transfer",
    }, "certificate source chain")
    for name, poly in (("alpha", alpha), ("beta", beta), ("gamma", gamma), ("delta", delta)):
        require(poly[0] > 0 and all(value >= 0 for value in poly), f"certificate {name} positivity")
        require(poly[0] % 8 == 7 and all(value % 8 == 0 for value in poly[1:]), f"certificate {name} phase")
        same(source_object[name], encode(poly), f"certificate {name}")
    same(integer(source_object["row_count"], "certificate source row count"), 41, "certificate source row count")
    same(integer_list(source_object["degrees"], "certificate source degrees"), tuple(range(41, 1, -1)) + (0,), "certificate source degrees")
    same(source_object["rows_sha256"], sha256_bytes(canonical_bytes({"rows": encode(source_rows)})), "certificate source rows digest")
    same(source_object["endpoint"], encode(source_endpoint), "certificate source endpoint")
    same(source_object["transfer"], "J(Q1,Q0)=-J(alpha,gamma)", "certificate source transfer")
    boundary_q0 = p_eval(source_rows[0], -1)
    boundary_q1 = p_eval(source_rows[1], -1)
    boundary = {
        "Q0": str(boundary_q0), "Q0_mod_8": str(boundary_q0 % 8),
        "Q1": str(boundary_q1), "Q1_mod_8": str(boundary_q1 % 8),
        "jacobi": str(jacobi(boundary_q1, boundary_q0)),
    }
    same(source_object["boundary_A_2"], boundary, "certificate A=2 boundary")

    coefficient_rows: tuple[Poly, ...] = chains["coefficient_rows"]
    coefficient_relations = chains["coefficient_relations"]
    coefficient_endpoint = endpoint(coefficient_rows, coefficient_relations, 37, 38)
    same(coefficient_endpoint["scales"], (800, 5), "certificate coefficient endpoint scales")
    same(coefficient_endpoint["determinant"], 245, "certificate coefficient endpoint determinant")
    ((terminal_a, terminal_b_signed), (terminal_c_signed, terminal_d_twice)) = coefficient_endpoint["matrix"]
    terminal_b = p_neg(terminal_b_signed)
    terminal_c = p_neg(terminal_c_signed)
    terminal_d = p_exact_div(terminal_d_twice, 2)
    terminal_l = coefficient_rows[-2]
    same(p_scale(terminal_l, 800), p_sub(p_mul(terminal_a, gamma), p_mul(terminal_b, alpha)), "certificate terminal first identity")
    same((5,), p_sub(p_scale(p_mul(terminal_d, alpha), 2), p_mul(terminal_c, gamma)), "certificate terminal second identity")
    same((245,), p_sub(p_scale(p_mul(terminal_a, terminal_d), 2), p_mul(terminal_b, terminal_c)), "certificate terminal determinant identity")
    terminal_polys = {
        "X": gamma, "Y": alpha, "L": terminal_l, "A": terminal_a,
        "B": terminal_b, "C": terminal_c, "D": terminal_d,
    }
    for name, poly in terminal_polys.items():
        require(poly[0] > 0 and all(value >= 0 for value in poly), f"certificate terminal {name} positivity")
    phases = {name: (p_eval(poly, 0) % 8, p_eval(poly, 1) % 8) for name, poly in terminal_polys.items()}
    roots_five = {name: roots_mod(poly, 5) for name, poly in terminal_polys.items()}
    roots_seven = {name: roots_mod(poly, 7) for name, poly in terminal_polys.items()}
    common_ac = {
        "mod_5": common_roots(terminal_a, terminal_c, 5),
        "mod_25": common_roots(terminal_a, terminal_c, 25),
        "mod_7": common_roots(terminal_a, terminal_c, 7),
        "mod_49": common_roots(terminal_a, terminal_c, 49),
        "mod_343": common_roots(terminal_a, terminal_c, 343),
    }
    exceptional_five = {name: p_eval(poly, 4) % 25 for name, poly in terminal_polys.items()}
    same(phases, {"X": (7, 7), "Y": (7, 7), "L": (1, 7), "A": (7, 7), "B": (7, 7), "C": (3, 7), "D": (3, 5)}, "certificate terminal phases")
    same(roots_five, {"X": [4], "Y": [0, 2], "L": [2], "A": [0, 2], "B": [4], "C": [0, 2, 4], "D": [4]}, "certificate roots mod five")
    same(roots_seven, {"X": [1], "Y": [], "L": [], "A": [5], "B": [], "C": [5], "D": []}, "certificate roots mod seven")
    same(common_ac, {"mod_5": [0, 2], "mod_25": [], "mod_7": [5], "mod_49": [26], "mod_343": []}, "certificate A,C lifts")
    same(exceptional_five, {"X": 20, "Y": 1, "L": 23, "A": 24, "B": 5, "C": 5, "D": 15}, "certificate exceptional mod25 class")
    coefficient_resultant = abs(resultant(alpha, gamma))
    terminal_resultant = abs(resultant(terminal_a, terminal_b))
    same(coefficient_resultant, 2**5735 * 5**76, "certificate alpha,gamma resultant")
    same(terminal_resultant, 2**5075 * 3**72 * 11**144, "certificate terminal resultant")
    coefficient_object = keys(payload["coefficient_chain"], {
        "alpha_roots_mod_5", "degrees", "endpoint", "gamma_roots_mod_5",
        "resultant_abs", "resultant_factorization", "row_count", "rows_sha256",
        "target", "terminal_obstruction", "terminal_orientation", "terminal_rows",
    }, "certificate coefficient chain")
    expected_coefficient_object = {
        "alpha_roots_mod_5": ["0", "2"],
        "degrees": encode([len(row) - 1 for row in coefficient_rows]),
        "endpoint": encode(coefficient_endpoint),
        "gamma_roots_mod_5": ["4"],
        "resultant_abs": str(coefficient_resultant),
        "resultant_factorization": [["2", "5735"], ["5", "76"]],
        "row_count": "39",
        "rows_sha256": sha256_bytes(canonical_bytes({"rows": encode(coefficient_rows)})),
        "target": "J(alpha(j),gamma(j))=1",
        "terminal_obstruction": {
            "conclusion": "the determinant-245 transfer does not close with 5/7 support",
            "resultant_A_B_abs": str(terminal_resultant),
            "resultant_A_B_factorization": [["2", "5075"], ["3", "72"], ["11", "144"]],
        },
        "terminal_orientation": {
            "common_A_C_lifts": encode(common_ac),
            "determinant": "2*A*D-B*C=245",
            "exceptional_j_4_mod_25": encode(exceptional_five),
            "identities": ["800*L=A*X-B*Y", "5=2*D*Y-C*X"],
            "phases_even_odd_mod_8": encode(phases),
            "polynomials": encode(terminal_polys),
            "roots_mod_5": encode(roots_five),
            "roots_mod_7": encode(roots_seven),
        },
        "terminal_rows": encode(coefficient_rows[-2:]),
    }
    same(coefficient_object, expected_coefficient_object, "certificate coefficient object")
    same(payload["proof_dag"], [
        {"id": "L1", "kind": "PrimitivePRS", "status": "exact"},
        {"id": "L2", "kind": "GlobalBezoutDetMinus16", "status": "exact"},
        {"id": "L3", "kind": "DyadicJacobiTransfer", "status": "human_exact"},
        {"id": "L4", "kind": "CoefficientCoprimality", "status": "exact"},
        {"id": "L5", "kind": "CoefficientTerminalDet245", "status": "exact"},
        {"id": "L6", "kind": "FactorSafeFiveSevenTransfer", "status": "refuted_by_new_3_11_support"},
        {"id": "L7", "kind": "ShiftedSquareContradiction", "status": "blocked_pending_3_11_orientation_or_new_identity"},
    ], "certificate proof DAG")
    same(payload["downstream_change"], {
        "lean_readiness": "not_ready_for_full_SS41",
        "new_hinge": "control J(A(j),B(j)) with exact 3/11 orientation or cancel it",
        "retired": "determinant-245 five/seven-only closure",
        "survives": "global determinant-minus-16 transfer",
    }, "certificate downstream status")
    digest = hashlib.sha256()
    main_failures = coefficient_failures = 0
    for parameter in range(10_000):
        q0 = p_eval(source_rows[0], parameter)
        q1 = p_eval(source_rows[1], parameter)
        alpha_value = p_eval(alpha, parameter)
        gamma_value = p_eval(gamma, parameter)
        require(math.gcd(q0, q1) == math.gcd(alpha_value, gamma_value) == 1, f"certificate plug-back gcd at {parameter}")
        source_symbol = jacobi(q1, q0)
        coefficient_symbol = jacobi(alpha_value, gamma_value)
        main_failures += source_symbol != -coefficient_symbol
        coefficient_failures += coefficient_symbol != 1
        digest.update(f"{parameter}:{source_symbol}:{coefficient_symbol}\n".encode())
    require(main_failures == coefficient_failures == 0, "certificate plug-back failures")
    same(payload["plug_back"], {"bound": "10000", "claim": "diagnostic_only", "sha256": digest.hexdigest()}, "certificate plug-back record")


EXPECTED_DETERMINANTS = {
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

EXPECTED_SUPPORT = {
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


def telescope_pairs(chains: dict[str, object]) -> dict[int, tuple[Poly, Poly]]:
    vectors = chains["coefficient_vectors"]
    result: dict[int, tuple[Poly, Poly]] = {1: ((0,), (1,))}
    for index in PAIR_INDICES[:-1]:
        _, left, right = vectors[index]
        require(left[-1] * right[-1] < 0, f"telescope endpoint signs {index}")
        sign = 1 if left[-1] > 0 else -1
        first = p_scale(left, sign)
        second = p_scale(right, -sign)
        require(first[0] > 0 and second[0] > 0, f"telescope orientation {index}")
        require(len(second) == len(first) + 1, f"telescope pair degrees {index}")
        require(first[0] % 2 == second[0] % 2 == 1, f"telescope pair constants {index}")
        require(all(value % 2 == 0 for value in first[1:] + second[1:]), f"telescope pair parity {index}")
        result[index] = (first, second)
    same(tuple(result), (1, *PAIR_INDICES[:-1]), "telescope pair insertion order")
    same(set(result), set(PAIR_INDICES), "telescope pair indices")
    return result


def telescope_links(
    chains: dict[str, object], pairs: dict[int, tuple[Poly, Poly]], observed: object
) -> tuple[list[dict[str, object]], list[object]]:
    observed_links = as_list(observed, "telescope links", 18)
    vectors = chains["coefficient_vectors"]
    links: list[dict[str, object]] = []
    modular: list[object] = []
    for position, index in enumerate(PAIR_INDICES[:-1]):
        first, second = pairs[index]
        nested = primitive_chain(second, first)
        same(tuple(len(row) - 1 for row in nested), tuple(range(index - 1, -1, -1)), f"nested degrees {index}")
        same(nested[-1], (1,), f"nested terminal constant {index}")
        relations = chain_relations(nested, (1,) * len(nested), 1, 0)
        nested_endpoint = endpoint(nested, relations, len(nested) - 2, len(nested) - 1)
        same(
            nested_endpoint["matrix"],
            ((vectors[index - 2][1], vectors[index - 2][2]), (vectors[index - 1][1], vectors[index - 1][2])),
            f"nested endpoint matrix {index}",
        )
        determinant_sign, determinant_factors = EXPECTED_DETERMINANTS[index]
        same(nested_endpoint["determinant"], factor_product(determinant_factors, determinant_sign), f"nested determinant {index}")
        support_factors = EXPECTED_SUPPORT[index]
        support_constant = nested_endpoint["scales"][1]
        same(odd_part(support_constant), factor_product(support_factors), f"nested support {index}")
        for prime, _ in determinant_factors + support_factors:
            require(is_prime(prime), f"telescope certified prime {prime}")
        observed_link = keys(observed_links[position], {
            "determinant_factorization", "endpoint", "index", "input_degrees",
            "modular_gcds", "nested_row_count", "nested_rows_sha256",
            "support_constant", "support_factorization_odd_part", "terminal_rows",
        }, f"telescope link {index}")
        same(integer(observed_link["index"], f"telescope link {index}.index"), index, f"telescope link index {index}")
        checks = as_list(observed_link["modular_gcds"], f"telescope modular gcds {index}", len(support_factors))
        for check_position, ((prime, _), check) in enumerate(zip(support_factors, checks, strict=True)):
            expected_gcd = (1, 1) if (index, prime) == (23, 13) else (1,)
            check_object = keys(check, {"index", "prime", "gcd", "bezout_left", "bezout_right"}, f"telescope gcd {index}/{prime}")
            same(integer(check_object["index"], f"telescope gcd {index}/{prime}.index"), index, f"telescope gcd index {index}/{prime}")
            verify_modular_bezout(check_object, first, second, prime, expected_gcd, f"telescope gcd {index}/{prime}", telescope_names=False)
            modular.append(check)
        expected_link = {
            "index": index,
            "input_degrees": (len(second) - 1, len(first) - 1),
            "nested_row_count": len(nested),
            "nested_rows_sha256": sha256_bytes(canonical_bytes({"rows": encode(nested)})),
            "terminal_rows": nested[-2:],
            "endpoint": nested_endpoint,
            "determinant_factorization": {"sign": determinant_sign, "factors": determinant_factors},
            "support_constant": support_constant,
            "support_factorization_odd_part": support_factors,
            "modular_gcds": checks,
        }
        same(observed_link, encode(expected_link), f"telescope link object {index}")
        links.append(expected_link)
    same(len(modular), 41, "telescope modular check total")
    return links, modular


def p_adic_exponent(value: int, prime: int, ceiling: int) -> int:
    require(value >= 0 and is_prime(prime) and ceiling > 0, "p-adic inputs")
    exponent = 0
    while exponent < ceiling and value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def primary_partition(
    pairs: dict[int, tuple[Poly, Poly]], index: int, modulus: int, precision: int
) -> dict[str, object]:
    require(index in (37, 25, 11) and precision == 3 * modulus, "primary partition contract")
    ceiling = 0
    power = precision
    while power > 1:
        require(power % 3 == 0, f"primary precision {index}")
        power //= 3
        ceiling += 1
    source, target = pairs[index], pairs[index - 2]
    records = []
    for residue in range(modulus):
        refinements = []
        exponents = set()
        for parameter in range(residue, precision, modulus):
            source_q = p_eval(source[1], parameter) % precision
            target_q = p_eval(target[1], parameter) % precision
            exponent = min(p_adic_exponent(source_q, 3, ceiling), p_adic_exponent(target_q, 3, ceiling))
            require(exponent < ceiling, f"primary exact depth {index}/{parameter}")
            exponents.add(exponent)
            refinements.append({"residue": parameter, "source_q": source_q, "target_q": target_q})
        require(len(exponents) == 1, f"primary branch constancy {index}/{residue}")
        exponent = exponents.pop()
        common = 3**exponent
        correction = jacobi(p_eval(source[0], residue), common) * jacobi(p_eval(target[0], residue), common)
        require(correction in (-1, 1), f"primary correction {index}/{residue}")
        records.append({
            "residue": residue, "common_exponent": exponent, "common_power": common,
            "correction_symbol": correction, "refinements": refinements,
        })
    same(tuple(record["residue"] for record in records), tuple(range(modulus)), f"primary coverage {index}")
    return {
        "index": index, "prime": 3, "modulus": modulus, "precision_modulus": precision,
        "records": records, "claim": "exact_common_3_primary_factor_and_local_correction",
    }


def telescope_local_certificate(
    chains: dict[str, object], pairs: dict[int, tuple[Poly, Poly]],
    links: list[dict[str, object]], observed: object,
) -> dict[str, object]:
    observed_local = keys(observed, {
        "claim_ceiling", "coverage", "direct_i3", "factor_thirteen", "links",
        "primary_partitions", "root", "sha256", "squareclass_neutral_links",
    }, "telescope local certificate")
    alpha: Poly = chains["alpha"]
    gamma: Poly = chains["gamma"]
    vectors = chains["coefficient_vectors"]
    p37, q37 = pairs[37]
    same(p_sub(p_mul(p37, gamma), p_mul(q37, alpha)), p_scale((17, 14), 800), "telescope root cross")
    _, root_left, root_right = vectors[38]
    same(p_add(p_mul(root_left, gamma), p_mul(root_right, alpha)), (5,), "telescope root support")
    same(p_add(p_mul(p37, root_right), p_mul(q37, root_left)), (245,), "telescope root determinant")

    root_records = []
    for residue in range(25):
        alpha_value, gamma_value = p_eval(alpha, residue), p_eval(gamma, residue)
        p_value, q_value = p_eval(p37, residue), p_eval(q37, residue)
        exponent = min(p_adic_exponent(gamma_value % 25, 5, 2), p_adic_exponent(q_value % 25, 5, 2))
        require(exponent < 2 and ((exponent == 1) == (residue % 5 == 4)), f"root partition {residue}")
        common = 5**exponent
        correction = jacobi(alpha_value, common) * jacobi(p_value, common)
        same(correction, 1, f"root correction {residue}")
        root_records.append({
            "residue": residue, "isolated_residue_four": residue == 4,
            "alpha": alpha_value % 25, "gamma": gamma_value % 25,
            "target_p": p_value % 25, "target_q": q_value % 25,
            "common_exponent": exponent, "common_power": common, "correction_symbol": correction,
        })
    root = {
        "modulus": 25, "determinant": 245, "determinant_factorization": ((5, 1), (7, 2)),
        "support_constant": 5, "cross_scale": 800, "cross_linear": (17, 14),
        "records": root_records, "claim": "exact_pre_telescope_local_partition_not_transfer",
    }

    primary = {
        37: primary_partition(pairs, 37, 3, 9),
        25: primary_partition(pairs, 25, 27, 81),
        11: primary_partition(pairs, 11, 27, 81),
    }

    p23, q23 = pairs[23]
    quotient_p = p_exact_div(p_affine(p23, 13, 12), 13)
    quotient_q = p_exact_div(p_affine(q23, 13, 12), 13)
    observed_factor = keys(observed_local["factor_thirteen"], {
        "claim", "index", "modulus", "prime", "quotient_bezout", "quotient_p",
        "quotient_p_sha256", "quotient_q", "quotient_q_sha256",
        "quotient_substitution", "records",
    }, "telescope factor thirteen")
    quotient_bezout = as_list(observed_factor["quotient_bezout"], "factor thirteen Bezout", 3)
    for position, prime in enumerate((13, 10_639, 290_737)):
        verify_modular_bezout(quotient_bezout[position], quotient_p, quotient_q, prime, (1,), f"factor thirteen quotient {prime}", telescope_names=True)
    factor_records = []
    for residue in range(13):
        p_residue = p_eval(p23, residue) % 13
        q_residue = p_eval(q23, residue) % 13
        on_class = residue == 12
        same((p_residue == 0 and q_residue == 0), on_class, f"factor thirteen roots {residue}")
        factor_records.append({
            "residue": residue, "factor": 13 if on_class else 1,
            "p": p_residue, "q": q_residue,
            "off_class_symbol": 1 if on_class else jacobi(residue + 1, 13),
        })
    factor_thirteen = {
        "index": 23, "prime": 13, "modulus": 13, "records": factor_records,
        "quotient_substitution": {"scale": 13, "shift": 12},
        "quotient_p": quotient_p, "quotient_q": quotient_q,
        "quotient_bezout": quotient_bezout,
        "quotient_p_sha256": poly_sha256(quotient_p), "quotient_q_sha256": poly_sha256(quotient_q),
        "claim": "exact_division_on_class_and_J_j_plus_one_13_off_class",
    }

    link_by_index = {int(link["index"]): link for link in links}
    local_links = []
    neutral = []
    exceptional = {37, 25, 23, 11, 3}
    permitted = {37: ({3}, {3}), 25: ({3}, {3, 13}), 23: ({13}, set()), 11: ({3}, {3}), 3: ({3}, {3})}
    for index in PAIR_INDICES[:-1]:
        source_p, source_q = pairs[index]
        target_p, target_q = pairs[index - 2]
        link = link_by_index[index]
        target_orientation = 1 if vectors[index - 2][1][-1] > 0 else -1
        cross_scale = int(link["endpoint"]["scales"][0])
        cross_linear = link["terminal_rows"][0]
        raw_cross = p_sub(p_mul(target_p, source_q), p_mul(target_q, source_p))
        same(raw_cross, p_scale(cross_linear, target_orientation * cross_scale), f"local cross identity {index}")
        _, endpoint_left, endpoint_right = vectors[index - 1]
        support_constant = int(link["support_constant"])
        same(p_add(p_mul(endpoint_left, source_q), p_mul(endpoint_right, source_p)), (support_constant,), f"local support identity {index}")
        determinant = int(link["endpoint"]["determinant"])
        delta = target_orientation * determinant
        determinant_sign, determinant_factors = EXPECTED_DETERMINANTS[index]
        support_factors = EXPECTED_SUPPORT[index]
        support_odd = {prime for prime, exponent in support_factors if exponent % 2}
        determinant_odd = {prime for prime, exponent in determinant_factors if prime != 2 and exponent % 2}
        same((support_odd, determinant_odd), permitted.get(index, (set(), set())), f"local squareclasses {index}")
        if index not in exceptional:
            neutral.append(index)
        cases = [{"condition": "all", "residue": None, "source_divisor": 1, "target_divisor": 1}]
        if index == 25:
            cases = [
                {"condition": "j%13!=12", "residue": None, "source_divisor": 1, "target_divisor": 1},
                {"condition": "j%13=12", "residue": 12, "source_divisor": 1, "target_divisor": 13},
            ]
        elif index == 23:
            cases = [
                {"condition": "j%13!=12", "residue": None, "source_divisor": 1, "target_divisor": 1},
                {"condition": "j%13=12", "residue": 12, "source_divisor": 13, "target_divisor": 1},
            ]
        checked_cases = []
        for case in cases:
            source_divisor = case["source_divisor"]
            target_divisor = case["target_divisor"]
            adjusted_support = support_constant // source_divisor
            adjusted_delta = delta // target_divisor
            same(adjusted_support * source_divisor, support_constant, f"local support division {index}")
            same(adjusted_delta * target_divisor, delta, f"local delta division {index}")
            reduced_cross = raw_cross if case["residue"] is None else p_exact_div(p_affine(raw_cross, 13, case["residue"]), source_divisor * target_divisor)
            checked_cases.append({**case, "adjusted_support": adjusted_support, "adjusted_delta": adjusted_delta,
                "adjusted_gcd": math.gcd(abs(adjusted_support), abs(adjusted_delta)),
                "reduced_cross": reduced_cross, "reduced_cross_sha256": poly_sha256(reduced_cross)})
        local_links.append({
            "index": index, "target_index": index - 2, "target_orientation": target_orientation,
            "cross_scale": cross_scale, "cross_linear": cross_linear,
            "support_constant": support_constant, "support_factorization_odd_part": support_factors,
            "determinant": determinant, "oriented_delta": delta,
            "determinant_factorization": {"sign": determinant_sign, "factors": determinant_factors},
            "reduction_cases": checked_cases,
            "kernel_data": {"h": "gcd(reduced_Q_i,reduced_Q_target)", "Q0": "reduced_Q_i/h", "q0": "reduced_Q_target/h", "r": "(reduced_P_target*reduced_Q_i-reduced_Q_target*reduced_P_i)/h"},
            "claim": "exact_local_data_not_directed_link_transfer",
        })
    same(neutral, [35, 33, 31, 29, 27, 21, 19, 17, 15, 13, 9, 7, 5], "local neutral links")

    direct_p, direct_q = pairs[3]
    same(pairs[1], ((0,), (1,)), "telescope terminal pair")
    direct_records = []
    for residue in range(27):
        symbol = jacobi(p_eval(direct_p, residue), p_eval(direct_q, residue))
        same(symbol, -1, f"direct i3 symbol {residue}")
        direct_records.append({"residue": residue, "p_mod_27": p_eval(direct_p, residue) % 27,
            "q_mod_27": p_eval(direct_q, residue) % 27, "symbol": symbol})
    body = {
        "claim_ceiling": "exact_local_certificate_not_link_transfer_telescope_or_SS41",
        "root": root, "links": local_links, "primary_partitions": primary,
        "factor_thirteen": factor_thirteen,
        "direct_i3": {"source_index": 3, "target_pair": {"p": (0,), "q": (1,)},
            "source_pair": {"P": direct_p, "Q": direct_q}, "modulus": 27,
            "records": direct_records, "generic_nonzero_p_wrapper_used": False},
        "squareclass_neutral_links": neutral,
        "coverage": {"directed_links": 18, "root_mod_25": 25, "i37_mod_3": 3,
            "i25_mod_27": 27, "i23_mod_13": 13, "i11_mod_27": 27,
            "all_partitions_total_and_pairwise_disjoint": True},
    }
    expected = {**body, "sha256": sha256_bytes(canonical_bytes(encode(body)))}
    same(observed_local, encode(expected), "telescope local certificate object")
    return expected


def telescope_controls(pairs: dict[int, tuple[Poly, Poly]]) -> dict[str, object]:
    spans = {
        (left, right): set()
        for left_position, left in enumerate(PAIR_INDICES)
        for right in PAIR_INDICES[left_position + 1:]
    }
    counts = {index: Counter() for index in PAIR_INDICES}
    digest = hashlib.sha256()
    for parameter in range(10_000):
        symbols = {}
        for index in PAIR_INDICES:
            first, second = pairs[index]
            first_value, second_value = p_eval(first, parameter), p_eval(second, parameter)
            common = math.gcd(first_value, second_value)
            expected_common = 13 if index == 23 and parameter % 13 == 12 else 1
            same(common, expected_common, f"telescope bounded gcd {index}/{parameter}")
            symbol = jacobi(first_value // common, second_value // common)
            require(symbol in (-1, 1), f"telescope bounded symbol {index}/{parameter}")
            symbols[index] = symbol
            counts[index][symbol] += 1
        same(symbols[23], 1 if parameter % 13 == 12 else jacobi(parameter + 1, 13), f"telescope factor13 control {parameter}")
        for span in spans:
            spans[span].add(symbols[span[0]] * symbols[span[1]])
        digest.update((f"{parameter}:" + ",".join(f"{index}={symbols[index]}" for index in PAIR_INDICES) + "\n").encode())
    constant = [span for span, values in spans.items() if len(values) == 1]
    variable = [span for span, values in spans.items() if len(values) > 1]
    expected_variable = [span for span in spans if (span[0] == 23) != (span[1] == 23)]
    same((len(spans), len(constant), len(variable)), (171, 153, 18), "telescope span counts")
    same(variable, expected_variable, "telescope variable spans")
    same(spans[(25, 21)], {-1}, "telescope factor13 span")
    same(spans[(37, 1)], {1}, "telescope full span")
    return {
        "bound": 10_000, "symbol_counts": {index: dict(sorted(value.items())) for index, value in counts.items()},
        "span_count": 171, "constant_span_count": 153, "variable_spans": variable,
        "factor_thirteen_span": {"indices": (25, 21), "ratio": -1},
        "full_span": {"indices": (37, 1), "ratio": 1}, "sha256": digest.hexdigest(),
        "claim": "diagnostic_only",
    }


def verify_telescope(chains: dict[str, object]) -> None:
    payload = load_json(TELESCOPE_PATH, max_bytes=2_000_000, strings_only_numbers=True)
    keys(payload, {"bounded_controls", "claim_ceiling", "coefficient_chain", "dual_telescope",
        "local_certificate", "marker", "nonclaims", "payload_sha256", "proof_dag", "schema", "upstream"}, "telescope payload")
    verify_payload_digest(payload, "telescope payload")
    same(
        sha256_bytes(read_bounded(TELESCOPE_PRODUCER_PATH, max_bytes=128 * 1024)),
        TELESCOPE_PRODUCER_SHA256,
        "telescope upstream producer hash",
    )
    same(
        sha256_bytes(read_bounded(SOURCE_41_PATH, max_bytes=128 * 1024)),
        SOURCE_41_SHA256,
        "telescope upstream source hash",
    )
    pairs = telescope_pairs(chains)
    chain = {
        "row_count": 39,
        "rows_sha256": sha256_bytes(canonical_bytes({"rows": encode(chains["coefficient_rows"])})),
        "indices": PAIR_INDICES,
        "oriented_pairs": {index: pairs[index] for index in PAIR_INDICES},
    }
    same(payload["coefficient_chain"], encode(chain), "telescope coefficient chain")
    dual_observed = keys(payload["dual_telescope"], {"link_count", "links", "modular_gcd_check_count",
        "modular_gcd_checks", "structural_sha256", "terminal_pair", "unique_specialization_gcd", "universal_status"}, "dual telescope")
    links, modular = telescope_links(chains, pairs, dual_observed["links"])
    same(dual_observed["modular_gcd_checks"], modular, "telescope flattened modular checks")
    local = telescope_local_certificate(chains, pairs, links, payload["local_certificate"])
    controls = telescope_controls(pairs)
    same(payload["bounded_controls"], encode(controls), "telescope bounded controls")
    structural = {"pairs": {index: pairs[index] for index in PAIR_INDICES}, "links": links,
        "modular_checks": modular, "local_certificate": local}
    dual = {
        "link_count": 18, "links": links, "modular_gcd_check_count": 41,
        "modular_gcd_checks": modular,
        "unique_specialization_gcd": {"index": 23, "prime": 13, "condition": "j%13=12", "value_on_condition": 13, "value_otherwise": 1},
        "structural_sha256": sha256_bytes(canonical_bytes(encode(structural))),
        "terminal_pair": {"P1": (0,), "Q1": (1,)},
        "universal_status": "pending_concrete_specialization_safe_link_theorems",
    }
    same(dual_observed, encode(dual), "dual telescope object")
    proof_dag = [
        {"id": "L1", "kind": "OrientedEndpointVectors", "status": "exact"},
        {"id": "L2", "kind": "DualPRSReversal18", "status": "exact"},
        {"id": "L3a", "kind": "GenericFactorSafeJacobiKernel", "status": "formalized_external_Lean", "theorem": "ss41_crossJacobiTransfer"},
        {"id": "L3b", "kind": "GenericEndpointFactorCorrection", "status": "formalized_external_Lean", "theorem": "ss41_endpointFactorCorrection"},
        {"id": "L3c", "kind": "ConcreteLinkCoprimalityOrientation", "status": "exact_replayed"},
        {"id": "L4", "kind": "GcdSupport", "status": "exact"},
        {"id": "L5", "kind": "UniqueFactor13", "status": "exact_replayed"},
        {"id": "L6", "kind": "OrdinaryLinkTransfers", "status": "open"},
        {"id": "L7", "kind": "Factor13TwoBlock", "status": "open"},
        {"id": "L8", "kind": "UniversalTelescope", "status": "open"},
    ]
    nonclaims = [
        "the local certificate does not assert a directed-link equality",
        "bounded controls do not prove the universal Jacobi-symbol telescope",
        "the certificate does not prove SS41", "no packet adapter or terminal closure follows",
        "maintained terminal status remains 1/4",
    ]
    upstream = {"path": "experiments/sm2_four_translate/interpolation/outer41_jacobi_certificate.py",
        "sha256": TELESCOPE_PRODUCER_SHA256,
        "source_path": "experiments/sm2_four_translate/interpolation/outer41_verify.gp", "source_sha256": SOURCE_41_SHA256}
    body = {"schema": "sm2.outer41-jacobi-telescope.v2", "marker": "OUTER41_JACOBI_LOCAL_OK",
        "claim_ceiling": "exact_local_certificate_not_link_transfer_telescope_or_SS41",
        "upstream": upstream, "coefficient_chain": chain, "dual_telescope": dual,
        "local_certificate": local, "bounded_controls": controls, "proof_dag": proof_dag, "nonclaims": nonclaims}
    expected = {**encode(body), "payload_sha256": sha256_bytes(canonical_bytes(encode(body)))}
    same(payload, expected, "telescope whole object")


def verify_a2_mod23() -> None:
    value = recurrence_value(2, 41) % 23
    same(value, 21, "A=2 fixed41 value modulo 23")
    target = (value - 1) % 23
    same(target, 20, "A=2 square target modulo 23")
    require(all((candidate * candidate) % 23 != target for candidate in range(23)), "A=2 target unexpectedly square modulo 23")


def main() -> int:
    try:
        verify_propagation()
        verify_fixed17_exceptions()
        chains = independent_chains()
        verify_block(chains)
        verify_certificate(chains)
        verify_telescope(chains)
        verify_a2_mod23()
    except (AuditError, OSError, ValueError) as error:
        print(f"PAPER1_INDEPENDENT_FINITE_FAIL: {error}", file=sys.stderr)
        return 1
    print(
        f"{MARKER} composition_cases=1224 mod4_cases=336 mod8_cases=16 "
        "fixed17_exceptions=7 source_rows=41 coefficient_rows=39 "
        "telescope_links=18 modular_gcd_checks=41 telescope_controls=10000 "
        "a2_mod23_residues=23"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
