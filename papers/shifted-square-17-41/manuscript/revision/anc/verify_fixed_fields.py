"""Exact finite certificate for the 17/41 paper.

Run: python verify_fixed_fields.py
Reference environment: Python 3.11+ and SymPy 1.14.0.
No bounded parameter search or number-field class-group routine is used.
"""
from __future__ import annotations

import sympy as sp

T = sp.Symbol("T")
C17 = [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1]
C41 = [
    -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
    3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
    -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5,
]
DATA = {
    17: (
        C17, 67, T**4 + T + 1,
        T**4 + T**3 + T**2 + T + 1,
        [13, 1751444197], [-1, 1], 532303029, 12,
    ),
    41: (
        C41, 163, T**10 + T**8 + T**7 + T**4 + T**3 + T + 1,
        T**10 + T**9 + T**4 + T + 1,
        [79, 1373, 115471, 1506563, 1344905911],
        [1, -1, -1, -1, 1], -43956715453803235217163523, 26,
    ),
}


def require(condition: object, label: str) -> None:
    if not bool(condition):
        raise ArithmeticError(label)


def modpoly(expr: object, prime: int) -> sp.Poly:
    return sp.Poly(expr, T, modulus=prime)


def verify(p: int) -> None:
    c, aux, phi, psi, factors, signs, u4, residue = DATA[p]
    d = [sp.Poly(2, T), sp.Poly(T, T)]
    for _ in range(2, p + 1):
        d.append(sp.Poly(T, T) * d[-1] + d[-2])
    g = d[p] - 2
    u = sp.Poly(c[0], T)  # c[0] multiplies 1, not D_0.
    for k in range(1, len(c)):
        u += c[k] * d[k]

    require(modpoly(g, aux).is_irreducible, "irreducibility")
    require(g.degree() == p and g.LC() == 1, "monic degree")
    require(g.eval(0) == -2, "constant term and theta norm")
    disc = 2 ** (3 * (p - 1) // 2) * p**p
    require(g.discriminant() == disc, "polynomial discriminant")
    require(sp.resultant(g, u) == -1, "unit resultant")

    # Dedekind's index criterion at 2.
    f2, h2 = modpoly(phi, 2), modpoly(psi, 2)
    require(f2.is_irreducible and h2.is_irreducible, "dyadic factors")
    require(f2 != h2, "distinct dyadic factors")
    require(f2.degree() == (p - 1) // 4, "first residue degree")
    require(h2.degree() == (p - 1) // 4, "second residue degree")
    lifted = sp.Poly(T * phi**2 * psi**2, T)
    difference = g - lifted
    require(all(a % 2 == 0 for a in difference.all_coeffs()), "mod 2")
    correction = sp.Poly(difference.as_expr() / 2, T, domain=sp.ZZ)
    remainder = modpoly(correction, 2).rem(f2 * h2)
    require(remainder == modpoly(1, 2), "2-maximality")

    # The only other possible index prime is p.
    difference = g - sp.Poly((T - 2)**p, T)
    require(all(a % p == 0 for a in difference.all_coeffs()), "mod p")
    value = int(g.eval(2))
    require(value % p == 0, "integral odd correction")
    require((value // p) % p == residue != 0, "p-maximality")

    # Rational-prime reference data recover the dyadic product.
    H = int(g.eval(4)) // 2
    require(int(g.eval(4)) % 2 == 0 and H % 8 == 1, "reference phase")
    require(len(set(factors)) == len(factors), "distinct factors")
    require(all(sp.isprime(q) for q in factors), "proven reference primes")
    require(sp.prod(factors) == H, "reference factorisation")
    require(u.eval(4) == u4, "unit reference value")
    actual = [int(sp.legendre_symbol(4 * u4, q)) for q in factors]
    require(actual == signs and sp.prod(signs) == -1, "reference signs")
    require(sp.jacobi_symbol(u4, H) == -1, "reference Jacobi symbol")
    print(f"p={p}: polynomial, index and reference checks passed")


if __name__ == "__main__":
    print(f"SymPy {sp.__version__}")
    for prime in (17, 41):
        verify(prime)
    print("FIXED_FIELDS_OK")
