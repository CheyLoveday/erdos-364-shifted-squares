#!/usr/bin/env python3
"""Independent statement-strength audit of Paper I (shifted squares, p = 17, 41).

Every check below tests the *statement* of a numbered claim of
papers/shifted-square-17-41/manuscript/revision/paper_1.md at its printed
quantifier strength, using only exact integer arithmetic written here from
scratch (no project script, no number-field package).

Conventions of the paper:
    F_0(A) = 1, F_1(A) = A, F_{n+2}(A) = 2A F_{n+1}(A) + F_n(A)      (1.1)
    D_0(T) = 2, D_1(T) = T, D_{n+2}(T) = T D_{n+1}(T) + D_n(T)       (2.1)
    g_p(T)  = D_p(T) - 2                                             (2.3 sec. 2.1)

Run:  python3 audit_statements.py
Exit status is nonzero iff some check fails.  A failed check is a candidate
gap in the paper, not a bug to be silenced; every failure is printed with the
witness.
"""
from __future__ import annotations

import sys
from math import isqrt

FAILURES: list[str] = []
CHECKS = 0


def require(cond: bool, label: str) -> None:
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILURES.append(label)
        print(f"FAIL {label}", flush=True)


# ---------------------------------------------------------------- arithmetic


def F(A: int, n: int) -> int:
    """Recurrence (1.1)."""
    a, b = 1, A
    if n == 0:
        return a
    for _ in range(n - 1):
        a, b = b, 2 * A * b + a
    return b


def D(T: int, n: int) -> int:
    """Recurrence (2.1)."""
    a, b = 2, T
    if n == 0:
        return a
    for _ in range(n - 1):
        a, b = b, T * b + a
    return b


def dpoly_coeffs(n: int) -> list[int]:
    """Coefficients of D_n in increasing degree."""
    a, b = [2], [0, 1]
    if n == 0:
        return a
    for _ in range(n - 1):
        # b_new = T*b + a
        nb = [0] + list(b)
        while len(nb) < len(a):
            nb.append(0)
        for i, c in enumerate(a):
            nb[i] += c
        a, b = b, nb
    return b


def dpoly_eval(coeffs: list[int], T: int) -> int:
    return sum(c * T**i for i, c in enumerate(coeffs))


def is_square(n: int) -> bool:
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


def v2(n: int) -> int:
    assert n != 0
    s = 0
    while n % 2 == 0:
        n //= 2
        s += 1
    return s


def jacobi(a: int, n: int) -> int:
    """Jacobi symbol (a/n) for odd positive n, computed from scratch.

    Returns 0 when gcd(a, n) > 1.  Uses the standard reciprocity algorithm and
    is deliberately *not* sympy's implementation.
    """
    if n <= 0 or n % 2 == 0:
        raise ValueError("denominator must be positive odd")
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def legendre(a: int, p: int) -> int:
    return jacobi(a, p)


def ring_mul(x: tuple[int, int], y: tuple[int, int], K: int) -> tuple[int, int]:
    """Multiplication in Z[sqrt K] with sqrt(K)^2 = K (the `Zsqrtd K` rule)."""
    a, b = x
    c, d = y
    return (a * c + K * b * d, a * d + b * c)


def ring_pow(x: tuple[int, int], N: int, K: int) -> tuple[int, int]:
    r = (1, 0)
    base = x
    while N:
        if N & 1:
            r = ring_mul(r, base, K)
        base = ring_mul(base, base, K)
        N >>= 1
    return r


# ------------------------------------------------------------------- data


def D_coeffs(p: int) -> list[int]:
    return dpoly_coeffs(p)


def U_from_coeffs(c: list[int]) -> list[int]:
    """U(T) = c[0] + sum_{k>=1} c[k] D_k(T), returned as plain coefficients."""
    p = len(c) - 1
    out = [0] * (p + 1)
    out[0] += c[0]
    for k in range(1, len(c)):
        if c[k] == 0:
            continue
        dk = dpoly_coeffs(k)
        for i, v in enumerate(dk):
            out[i] += c[k] * v
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_eval(coeffs: list[int], T: int) -> int:
    return dpoly_eval(coeffs, T)


def poly_trim(a: list[int]) -> list[int]:
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return poly_trim(out)


def poly_mod(a: list[int], b: list[int]) -> list[int]:
    a = list(a)
    b = poly_trim(list(b))
    db, lb = len(b) - 1, b[-1]
    while len(a) - 1 >= db and any(a):
        if a[-1] == 0:
            a.pop()
            continue
        shift = len(a) - 1 - db
        q = a[-1] // lb
        for i, c in enumerate(b):
            a[i + shift] -= q * c
        a = poly_trim(a)
        if all(x == 0 for x in a):
            return [0]
    return poly_trim(a)


def poly_div_exact(a: list[int], b: list[int]) -> list[int]:
    a = list(a)
    b = poly_trim(list(b))
    db = len(b) - 1
    q = [0] * (len(a) - db)
    while len(a) - 1 >= db and any(a):
        if a[-1] == 0:
            a.pop()
            continue
        shift = len(a) - 1 - db
        c = a[-1] // b[-1]
        q[shift] = c
        for i, v in enumerate(b):
            a[i + shift] -= c * v
        a = poly_trim(a)
    assert all(x == 0 for x in a), "inexact division"
    return poly_trim(q)


def poly_rem_mod2(a: list[int], b: list[int]) -> list[int]:
    """Remainder of a on division by monic b over F_2."""
    a = [x % 2 for x in a]
    b = [x % 2 for x in b]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    db = len(b) - 1
    assert b[-1] % 2 == 1
    while len(a) - 1 >= db and any(a):
        shift = len(a) - 1 - db
        for i in range(db + 1):
            a[i + shift] ^= b[i]
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    return a or [0]


def poly_mul_mod2(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x % 2:
            for j, y in enumerate(b):
                out[i + j] ^= y % 2
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def all_monic_mod2(d: int) -> list[list[int]]:
    """All monic polynomials over F_2 of degree exactly d, low degree first."""
    out = []
    for bits in range(1 << d):
        c = [(bits >> i) & 1 for i in range(d)] + [1]
        out.append(c)
    return out


def irreducible_mod2(f: list[int]) -> bool:
    f = [x % 2 for x in f]
    d = len(f) - 1
    assert f[-1] % 2 == 1
    if d == 0:
        return False
    for e in range(1, d // 2 + 1):
        for g in all_monic_mod2(e):
            if not any(poly_rem_mod2(f, g)):
                return False
    return True


def resultant(f: list[int], g: list[int]) -> int:
    """Sylvester-matrix determinant over the integers (small degrees only)."""
    n, m = len(f) - 1, len(g) - 1
    size = n + m
    mat = [[0] * size for _ in range(size)]
    for i in range(m):
        for j in range(n + 1):
            mat[i][i + j] = f[n - j]
    for i in range(n):
        for j in range(m + 1):
            mat[m + i][i + j] = g[m - j]
    # fraction-free Gaussian elimination (Bareiss)
    prev = 1
    for k in range(size - 1):
        if mat[k][k] == 0:
            for r in range(k + 1, size):
                if mat[r][k] != 0:
                    mat[k], mat[r] = mat[r], mat[k]
                    break
            else:
                return 0
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                mat[i][j] = (mat[i][j] * mat[k][k] - mat[i][k] * mat[k][j]) // prev
        prev = mat[k][k]
        for i in range(k + 1, size):
            mat[i][k] = 0
    return mat[-1][-1]


def iroot(n: int, k: int) -> int:
    """floor(n^(1/k)) for n >= 1."""
    if n < 2:
        return n
    lo, hi = 0, 1 << ((n.bit_length() + k - 1) // k + 1)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo


def gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


# ----------------------------------------------------------------- checks


def check_printed_values():
    """Numbers printed in the paper, recomputed from (1.1) alone."""
    require([F(2, n) for n in range(6)] == [1, 2, 9, 38, 161, 682],
            "§1.1 initial sequence at A = 2")
    require(F(2, 2) - 1 == 8 and F(2, 4) - 1 == 160 and F(2, 8) - 1 == 51840,
            "§2.3 worked valuations at A = 2")
    require(v2(F(2, 2) - 1) == 3 and v2(F(2, 4) - 1) == 5 and v2(F(2, 8) - 1) == 7,
            "§2.3 printed valuations 3, 5, 7")
    require(F(6, 51) == F(882, 17), "§5.3 composition example F_51(6) = F_17(882)")
    require(F(6, 3) == 882, "§5.3 inner iterate F_3(6) = 882")
    require((F(6, 51) - 1) % 8 == 1, "§5.3 F_51(6)-1 = 1 mod 8")
    require(F(2, 4) == 161 and F(F(2, 2), 2) == 163,
            "§5.2 numbers F_4(2) = 161 and F_2(F_2(2)) = 163")


def check_recurrences():
    for A in (0, 2, 6, 10, 1014):
        for n in range(0, 12):
            require(D(2 * A, n) == 2 * F(A, n), f"(2.2) D_n(2A)=2F_n(A) A={A} n={n}")
    # (2.4) closed forms / doubling
    for A in (2, 6, 10, 30):
        for n in range(0, 9):
            require(F(A, 2 * n) == 2 * F(A, n) ** 2 - (-1) ** n,
                    f"(2.4) doubling A={A} n={n}")
    # (2.5) odd n and (2.6) even n forms
    for A in (2, 6, 14):
        for n in range(1, 9):
            if n % 2:
                require(F(A, 2 * n) - 1 == 2 * F(A, n) ** 2, f"(2.5) A={A} n={n}")
            else:
                require(F(A, 2 * n) - 1 == 2 * (F(A, n) - 1) * (F(A, n) + 1),
                        f"(2.6) A={A} n={n}")
    # (2.7) and (2.8) residues
    for A in range(2, 260, 4):
        for n in range(0, 61):
            v = F(A, n)
            if n % 2 == 0:
                require(v % 4 == 1, f"(2.7) even A={A} n={n} F%4={v%4}")
            else:
                require(v % 4 == 2, f"(2.7) odd A={A} n={n} F%4={v%4}")
                if n % 4 == 1:
                    require(v % 8 == A % 8, f"(2.8) n=1mod4 A={A} n={n}")
                else:
                    require(v % 8 == (A + 4) % 8, f"(2.8) n=3mod4 A={A} n={n}")


def check_valuation_theorem():
    """Theorem 1.3 / (1.5): v_2(F_N(A)-1) = 2 v_2(N) + 1 for positive even N."""
    for A in range(2, 1000, 4):
        for N in range(2, 600, 2):
            lhs = v2(F(A, N) - 1)
            rhs = 2 * v2(N) + 1
            require(lhs == rhs, f"(1.5) A={A} N={N}: {lhs} != {rhs}")


def check_composition():
    """Lemma 5.1: F_{mn}(A) = F_m(F_n(A)) for odd n."""
    for A in (0, 2, 6, 10, 42, 1234):
        for n in (1, 3, 5, 7, 9, 11, 17, 41):
            for m in (0, 1, 2, 3, 5, 17, 40):
                require(F(A, m * n) == F(F(A, n), m),
                        f"(5.1) A={A} m={m} n={n}")
    # the parity guard is essential: exhibit the paper's even counterexample
    require(F(2, 4) != F(F(2, 2), 2), "even-inner-index guard witness")


def check_main_theorem():
    """Theorem 1.1 at printed strength, for a range of A and indices."""
    for A in range(2, 200, 4):
        for p in (17, 41):
            for m in range(1, 21, 2):  # N = p*m odd
                N = p * m
                require(not is_square(F(A, N) - 1), f"(1.3) A={A} N={N}")
            for m in range(1, 12):     # N = p*m with even m too
                N = p * m
                require(not is_square(F(A, N) - 1), f"(1.3) A={A} N={N}")


def check_two_adic_criterion():
    """Proposition 2.1 at printed strength, including the 2-adic sufficiency."""
    square_cases = {(2, 1), (6, 3)}
    for A in range(2, 2000, 4):
        for n in range(1, 140, 2):
            val = F(A, n) - 1
            r = val % 8
            predicted = (A % 8, n % 4) in square_cases
            # odd 2-adic unit is a square iff congruent 1 mod 8
            require((r == 1) == predicted,
                    f"(2.9) residue step A={A} n={n} r={r} predicted={predicted}")
            if predicted:
                # explicit Hensel lifting of a square root mod 2^k
                x = 1
                for k in range(3, 65):
                    m = 1 << k
                    require((x * x - val) % m == 0,
                            f"(2.9) Hensel invariant A={A} n={n} k={k}")
                    t = ((x * x - val) // m) % 2
                    if t:
                        x += 1 << (k - 1)


def check_pell_corollary():
    """Corollary 1.4: the real coordinate of (u+v sqrt K)^N is F_N(u).

    The paper writes the power in Z[sqrt K]; we use the formal rule
    sqrt(K)^2 = K, which is exactly Mathlib's `Zsqrtd`.
    """
    data = [(2, 1), (6, 1), (10, 1), (14, 1), (18, 1), (22, 1)]
    # u^2 + 1 = K v^2 families found by search, including non-squarefree K
    for K in range(2, 5000):
        for v in range(1, 61):
            u2 = K * v * v - 1
            u = isqrt(u2)
            if u * u == u2 and u % 4 == 2:
                data.append((u, v))
    seen = set()
    tested = 0
    nonsquarefree = 0
    for (u, v) in data:
        K = (u * u + 1) // (v * v)
        require(K * v * v == u * u + 1, f"(1.6) reconstruction u={u} v={v}")
        if (u, v) in seen:
            continue
        seen.add((u, v))
        tested += 1
        if not is_squarefree(K):
            nonsquarefree += 1
        for N in (1, 2, 3, 4, 5, 6, 17, 18, 41):
            re, im = ring_pow((u, v), N, K)
            require(re == F(u, N), f"(6.1) re((u+v sqrtK)^N)=F_N(u) u={u} v={v} N={N}")
            require(re * re - K * im * im == (-1) ** N,
                    f"norm of power u={u} v={v} N={N}")
    print(f"  Corollary 1.4 identity verified for {tested} (K,u,v) triples, "
          f"{nonsquarefree} of them with K not squarefree", flush=True)


def check_fixed_field_data():
    """Tables 3, 4, A1 and Appendix A.2, recomputed from the paper's own data."""
    C17 = [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1]
    C41 = [-1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
           3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
           -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5]
    U_coeffs = {}
    for p, c in ((17, C17), (41, C41)):
        g = D_coeffs(p)
        # g_p(T) = D_p(T) - 2
        g[0] -= 2
        u = U_from_coeffs(c)
        U_coeffs[p] = u
        require(len(g) - 1 == p and g[-1] == 1, f"monic degree p={p}")
        require(g[0] == -2, f"theta norm 2 p={p}")
        res = resultant(g, u)
        require(res == -1, f"(4.5)/(4.9) Res(g_p,U_p) p={p}: {res}")
        # disc = (-1)^{n(n-1)/2} Res(g, g'); both exponent pairs are even here
        require((p * (p - 1) // 2) % 2 == 0, f"disc sign trivial p={p}")
        disc = resultant(list(g), [i * g[i] for i in range(1, len(g))])
        want = 2 ** (3 * (p - 1) // 2) * p**p
        require(disc == want, f"polynomial discriminant p={p}: {disc} != {want}")
        printed = {17: 45537549122, 41: 50755107359004694554823202}[p]
        require(poly_eval(g, 4) == printed, f"(A.1) g_p(4) p={p}")
        H = (D(4, p) - 2) // 2
        require((D(4, p) - 2) % 2 == 0, f"H_p integral p={p}")
        require(H % 8 == 1, f"reference phase H_p=1 mod 8 p={p}")
        u4 = poly_eval(u, 4)
        require(jacobi(u4, H) == -1, f"reference Jacobi p={p}")
        # (A.2)/(A.3): 2-adic factorisation and Dedekind index criterion at 2
        if p == 17:
            phi = [1, 1, 0, 0, 1]           # T^4+T+1
            psi = [1, 1, 1, 1, 1]           # T^4+T^3+T^2+T+1
            factors, signs = [13, 1751444197], [-1, 1]
        else:
            phi = [1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1]      # T^10+T^8+T^7+T^4+T^3+T+1
            psi = [1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1]      # T^10+T^9+T^4+T+1
            factors, signs = ([79, 1373, 115471, 1506563, 1344905911],
                              [1, -1, -1, -1, 1])
        # T*phi^2*psi^2 has the same reduction as g_p modulo 2
        prod = poly_mul(poly_mul(phi, phi), poly_mul(psi, psi))
        prod = poly_mul([0, 1], prod)
        diff = [a - b for a, b in zip(g + [0] * len(prod), prod + [0] * len(g))]
        require(all(x % 2 == 0 for x in diff), f"(A.3) mod 2 p={p}")
        correction = [x // 2 for x in diff]
        rem = poly_rem_mod2(correction, poly_mul(phi, psi))
        require(poly_trim(rem) == [1], f"(A.2) correction remainder 1 p={p}: {rem}")
        require(irreducible_mod2(phi) and irreducible_mod2(psi),
                f"(A.2) irreducible dyadic factors p={p}")
        require(phi != psi, f"(A.2) distinct dyadic factors p={p}")
        require(len(phi) - 1 == (p - 1) // 4 and len(psi) - 1 == (p - 1) // 4,
                f"(A.2) residue degrees p={p}")
        # p-adic: g_p(T) = (T-2)^p mod p, correction (g_p(2)/p) not 0 mod p
        binom = [0] * (p + 1)
        for i in range(p + 1):
            from math import comb
            binom[i] = comb(p, i) * (-2) ** (p - i)
        diffp = [a - b for a, b in zip(g + [0] * (p + 1), binom + [0] * len(g))]
        require(all(x % p == 0 for x in diffp), f"(A.4) mod p p={p}")
        g2 = D(2, p) - 2
        require(g2 % p == 0, f"(A.5) integrality p={p}")
        require((g2 // p) % p != 0, f"(A.5) nonzero residue p={p}")
        # reference factorisation and characters
        require(all(is_prime(q) for q in factors), f"primes p={p}")
        prod_f = 1
        for q in factors:
            prod_f *= q
        require(prod_f == H, f"(4.6)/(4.10) factorisation p={p}: {prod_f} != {H}")
        require(len(set(factors)) == len(factors), f"distinct factors p={p}")
        got = [legendre(4 * u4, q) for q in factors]
        require(got == signs, f"Table A1 characters p={p}: {got} != {signs}")
        require(abs(jacobi(u4, H)) == 1, f"coprime numerator p={p}")
        # dyadic row data are consequences of (A.3) plus Dedekind-Kummer;
        # here we only re-check the degree bookkeeping of Table 4
        h = (p - 1) // 4
        require(1 + 4 * h == p, f"Table 4 degree sum p={p}")


def check_jacobi_certificate():
    """Proposition 7.1: J(U_p(2A), F_p(A)-1) = -1 for every A = 2 mod 8."""
    C17 = [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1]
    C41 = [-1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
           3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
           -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5]
    for p, c in ((17, C17), (41, C41)):
        u = U_from_coeffs(c)
        count = 0
        for A in range(2, 500000, 8):
            Q = F(A, p) - 1
            num = poly_eval(u, 2 * A)
            require(Q > 0 and Q % 2 == 1, f"(7.1) Q odd p={p} A={A}")
            require(gcd(num, Q) == 1, f"(7.1) coprimality p={p} A={A}")
            j = jacobi(num, Q)
            require(j == -1, f"(7.1) J(U_p(2A),F_p(A)-1) p={p} A={A} got {j}")
            # the two reciprocity steps of the paper's proof of (7.4)
            mm = A // 2
            require(jacobi(mm, Q) == 1, f"(7.4) J(m,Q)=1 p={p} A={A}")
            require(Q % mm == mm - 1 or mm == 1, f"(7.4) Q=-1 mod m p={p} A={A}")
            require(jacobi(2 * A * poly_eval(u, 2 * A), Q) == j,
                    f"(7.3) J(x U_p(x),Q)=J(U_p(x),Q) p={p} A={A}")
            require(not is_square(Q), f"(4.13) hard phase p={p} A={A}")
            count += 1
        print(f"  Proposition 7.1 verified for p={p} at {count} values of A", flush=True)


def check_endpoint():
    """The degree-41 endpoint A = 2 used by the separated formal branch."""
    q = F(2, 41) - 1
    require(q % 23 == 20, f"A=2 endpoint: F_41(2)-1 = {q % 23} mod 23")
    require(legendre(20 % 23, 23) == -1, "20 is a nonresidue mod 23")
    # and no integral square, by direct exact test
    require(not is_square(q), "F_41(2)-1 is not a square")
    q17 = F(2, 17) - 1
    require(not is_square(q17), "F_17(2)-1 is not a square")
    # Section 7.2: at A = 2 the factor 13 of H_17 has odd valuation and
    # (U_17(4)/13) = -1, so 13 alone obstructs the reference value.
    require(q17 % 13 == 0 and q17 % 169 != 0, "13 has valuation one in H_17")
    C17 = [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1]
    u17 = U_from_coeffs(C17)
    require(legendre(poly_eval(u17, 4), 13) == -1, "U_17(4) is a nonresidue mod 13")


def is_squarefree(n: int) -> bool:
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1 if d == 2 else 2
    return True


def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin, exact for n < 3.3e24 by known bases."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def main():
    print("statement audit of paper_1 (p = 17, 41)", flush=True)
    for name, fn in [
        ("numbers printed in the paper", check_printed_values),
        ("recurrence identities (2.2)-(2.8)", check_recurrences),
        ("Theorem 1.3 exact 2-adic valuation (1.5)", check_valuation_theorem),
        ("Lemma 5.1 composition (5.1)", check_composition),
        ("Theorem 1.1 index-divisibility exclusion (1.3)", check_main_theorem),
        ("Proposition 2.1 odd 2-adic criterion (2.9)", check_two_adic_criterion),
        ("Corollary 1.4 Pell coordinate (6.1)", check_pell_corollary),
        ("fixed-field certificates (Tables 3, 4, A1; App. A.2)", check_fixed_field_data),
        ("Proposition 7.1 uniform Jacobi identity (7.1)", check_jacobi_certificate),
        ("degree-41 endpoint A = 2", check_endpoint),
    ]:
        print(f"[{name}]", flush=True)
        fn()
    print(f"\n{CHECKS} assertions; {len(FAILURES)} failures", flush=True)
    if FAILURES:
        for f in FAILURES[:40]:
            print("  FAILED:", f)
        return 1
    print("STATEMENT_AUDIT_OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
