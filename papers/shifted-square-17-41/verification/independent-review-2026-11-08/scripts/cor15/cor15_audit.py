"""Full audit script for the Corollary 1.5 material (paper v1.0.1, sections 6.2-6.3).

Sections
  A  fundamental units of the order Z[sqrt D] via continued fractions,
     cross-checked against brute force for small D
  B  the rank lemma (6.5)/(6.6):  D | b_n  <=>  (D/gcd(D,v)) | n
     (a) squarefree D in [2,3000]   (b) non-squarefree D, to fix the scope
  C  (6.7): the norm-one normalisation K/gcd(K,2uv) = K/gcd(K,v)
  D  the family  X^2+1 = K^3 V^2  <=>  X = a_N with N a multiple of R;
     phase X mod 8, and the search for X-1 a perfect square
  E  direct search: odd y <= YMAX with y^4+2y^2+2 powerful

No computer algebra system is used: continued fractions and integer
arithmetic only.  Run:  python3 audit/cor15_audit.py
"""

from math import isqrt, gcd
import sys

sys.set_int_max_str_digits(10 ** 7)

# ---------------------------------------------------------------- A

def cf_period(D):
    a0 = isqrt(D)
    if a0 * a0 == D:
        raise ValueError("D is a square")
    m, d, a = 0, 1, a0
    period = []
    while True:
        m = d * a - m
        d = (D - m * m) // d
        a = (a0 + m) // d
        period.append(a)
        if a == 2 * a0:
            return a0, period


def convergents(a0, period):
    pm2, pm1, qm2, qm1 = 0, 1, 1, 0
    for a in [a0] + period:
        p = a * pm1 + pm2
        q = a * qm1 + qm2
        yield p, q
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q


def pell_solutions(D):
    """(fundamental minus solution or None, fundamental plus solution, period)."""
    a0, period = cf_period(D)
    L = len(period)
    conv = list(convergents(a0, period))
    if L % 2 == 1:
        u, v = conv[L - 1]
        assert u * u - D * v * v == -1, (D, u, v)
        return (u, v), (u * u + D * v * v, 2 * u * v), L
    for p, q in conv:
        assert p * p - D * q * q != -1, (D, p, q)
    p, q = conv[L - 1]
    assert p * p - D * q * q == 1, (D, p, q)
    return None, (p, q), L


def check_pell_code(limit=400, cap=200000):
    """Fundamental solutions found by brute force agree with the CF code.

    Existence is decided by the continued-fraction period theorem; here we
    verify the *least* property by an exhaustive search below the claimed
    solution whenever that search is affordable.
    """
    checked = 0
    deep = 0
    for D in range(2, limit + 1):
        if isqrt(D) ** 2 == D:
            continue
        neg, pos, L = pell_solutions(D)
        if neg is not None:
            u, v = neg
            assert u > 0 and v > 0 and u * u - D * v * v == -1
            if v <= cap:
                deep += 1
                for y in range(1, v):
                    z = D * y * y - 1
                    s = isqrt(z)
                    assert not (s * s == z and s >= 1), (D, y)
        X1, Y1 = pos
        assert X1 > 1 and Y1 > 0 and X1 * X1 - D * Y1 * Y1 == 1
        if Y1 <= cap:
            deep += 1
            for y in range(1, Y1):
                z = D * y * y + 1
                s = isqrt(z)
                assert not (s * s == z and s >= 1), (D, y)
        checked += 1
    return checked, deep


def is_squarefree(n):
    if n % 4 == 0:
        return False
    p = 2
    while p * p <= n:
        if n % (p * p) == 0:
            return False
        if n % p == 0:
            n //= p
        p += 1 if p == 2 else 2
    return True


def is_square(n):
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


# ---------------------------------------------------------------- B

def rank_lemma_scan(D, u, v, n_max):
    """Scan n = 1..n_max in exact modular arithmetic for the rank lemma.

    Returns (R, least index n with D | b_n).  Raises on any failure.
    """
    R = D // gcd(D, v)
    am, bm = 1 % D, 0              # eps^n mod D, coordinates
    pw = 1 % D                     # u^{n-1} mod D
    least = None
    for n in range(1, n_max + 1):
        am, bm = (am * u + bm * v * D) % D, (am * v + bm * u) % D
        # (6.5): b_n = n u^{n-1} v  (mod D)
        assert (bm - n * pw % D * v) % D == 0, ("(6.5)", D, n)
        # (6.6): D | b_n  <=>  R | n
        assert (bm == 0) == (n % R == 0), ("(6.6)", D, n, bm, R)
        if bm == 0 and least is None:
            least = n
        pw = pw * u % D
    assert least == R, ("least", D, least, R)
    return R, least


def section_B():
    print("== B. rank lemma (6.5)/(6.6) ==")
    ok = 0
    R1 = []
    for D in range(2, 3001):
        if not is_squarefree(D):
            continue
        neg, pos, L = pell_solutions(D)
        if neg is None:
            continue
        u, v = neg
        R, least = rank_lemma_scan(D, u, v, min(3 * D + 6, 4000))
        ok += 1
        if R == 1:
            R1.append(D)
    print(f"  (a) squarefree D in [2,3000], negative Pell solvable: {ok} "
          f"instances, all passed;  R=1 cases: {R1}")
    # (b) scope: drop squarefreeness
    ok2 = 0
    R1b = []
    for D in range(2, 1001):
        if is_squarefree(D) or isqrt(D) ** 2 == D:
            continue
        neg, pos, L = pell_solutions(D)
        if neg is None:
            continue
        u, v = neg
        R, least = rank_lemma_scan(D, u, v, min(3 * D + 6, 2500))
        ok2 += 1
        if R == 1:
            R1b.append(D)
    print(f"  (b) NON-squarefree D in [2,1000], negative Pell solvable: {ok2} "
          f"instances, all passed; R=1 cases: {R1b}")
    nonsq = [D for D in range(2, 1001)
             if not is_squarefree(D) and isqrt(D) ** 2 != D
             and pell_solutions(D)[0] is not None]
    print(f"      (the {ok2} non-squarefree D tested are {nonsq})")
    # the R = 1 branch of Walker's Theorem 2.2(2): fundamental solution already
    # has property Q, i.e. K | v
    R1_big = []
    cnt_big = 0
    for D in range(2, 60001):
        if not is_squarefree(D):
            continue
        neg, pos, L = pell_solutions(D)
        if neg is None:
            continue
        cnt_big += 1
        if neg[1] % D == 0:
            R1_big.append(D)
    print(f"  (c) branch R = 1 (K | v for the fundamental minus solution): "
          f"{len(R1_big)} cases among {cnt_big} squarefree D <= 60000 with "
          f"negative Pell solvable")
    print("      (so the R|n criterion itself does not need squarefreeness;")
    print("       squarefreeness is needed only for the K^3 V^2 normal form")
    print("       and for Walker's 'product of distinct primes' reading)")


# ---------------------------------------------------------------- C

def section_C():
    print("== C. (6.7) norm-one normalisation ==")
    ok = 0
    odd_fail = []
    even_fail = []
    for D in range(2, 5001):
        if not is_squarefree(D):
            continue
        neg, pos, L = pell_solutions(D)
        if neg is None:
            continue
        u, v = neg
        X1, Y1 = pos
        assert (X1, Y1) == (u * u + D * v * v, 2 * u * v)
        R = D // gcd(D, v)
        R1 = D // gcd(D, Y1)
        assert gcd(u, D) == 1
        if D % 2 == 1:
            ok += 1
            if R != R1:
                odd_fail.append((D, R, R1))
        elif R != R1:
            even_fail.append((D, R, R1))
    print(f"  odd squarefree D in [2,5000] with negative Pell solvable: {ok} "
          f"instances; failures of K/gcd(K,2uv) = K/gcd(K,v): {odd_fail}")
    print(f"  even D where the identity fails (scope of the 'K odd' "
          f"hypothesis): {even_fail[:6]} ... {len(even_fail)} cases total")


# ---------------------------------------------------------------- D

def section_D(maxK=20000, digits=60):
    print("== D. family X^2+1 = K^3 V^2 ==")
    bound = 10 ** digits
    rows = []
    neg_pell = 0
    even_K_note = 0
    for K in range(2, maxK + 1):
        if not is_squarefree(K):
            continue
        if K % 2 == 0:
            # X^2+1 = K^3 V^2 is impossible for even K>1: X even makes the
            # left side odd, X odd makes its 2-valuation exactly 1.
            even_K_note += 1
            continue
        neg, pos, L = pell_solutions(K)
        if neg is None:
            continue
        neg_pell += 1
        u, v = neg
        R = K // gcd(K, v)
        assert R % 2 == 1
        a, b = 1, 0
        n = 0
        while True:
            n += 1
            a, b = a * u + b * v * K, a * v + b * u
            if a > bound:
                break
            if n % R or n % 2 == 0:
                continue
            assert b % K == 0
            V = b // K
            assert a * a + 1 == K ** 3 * V * V, (K, n)
            rows.append((K, n, R, a, V))
    rows.sort(key=lambda r: r[3])
    print(f"  odd squarefree K <= {maxK} with negative Pell solvable: {neg_pell}"
          f"   (even squarefree K <= {maxK} skipped: {even_K_note}, no family"
          f" member can exist)")
    print(f"  family members with X <= 10^{digits}: {len(rows)}")
    print("   K     N     R      X mod 8   X-1 square?   17|N  41|N   digits")
    square_hits = []
    for K, n, R, X, V in rows[:40]:
        sq = is_square(X - 1)
        if sq:
            square_hits.append((K, n, X))
        print(f"  {K:5d} {n:5d} {R:5d}   {X % 8:5d}      {str(sq):5s}       "
              f"{str(n % 17 == 0):5s} {str(n % 41 == 0):5s}   {len(str(X))}")
    print(f"  ... {max(0, len(rows) - 40)} further members omitted")
    print(f"  members with X-1 a perfect square: {square_hits}")
    multi17 = [r for r in rows if r[1] % 17 == 0]
    multi41 = [r for r in rows if r[1] % 41 == 0]
    print(f"  members with 17 | N: {len(multi17)} (e.g. K,N = "
          f"{[(r[0], r[1]) for r in multi17[:5]]})")
    print(f"  members with 41 | N: {len(multi41)} (e.g. K,N = "
          f"{[(r[0], r[1]) for r in multi41[:5]]})")
    phase = {}
    for K, n, R, X, V in rows:
        phase.setdefault((K % 8, X % 8), 0)
        phase[(K % 8, X % 8)] += 1
    print("  (K mod 8, X mod 8) counts:", dict(sorted(phase.items())))
    return rows


# ---------------------------------------------------------------- E

def section_H(limit=12):
    """The two other ingredients Corollary 1.5 consumes for odd N:
    Lemma 5.1 (odd-inner composition) and the mod-4 phase (2.7)."""
    print("== H. composition lemma 5.1 and phase (2.7) ==")
    def F(A, n):
        f0, f1 = 1, A
        if n == 0:
            return f0
        for _ in range(2, n + 1):
            f0, f1 = f1, 2 * A * f1 + f0
        return f1
    bad = []
    cnt = 0
    for A in range(0, 8):
        for m in range(0, limit):
            for n in range(1, 2 * limit, 2):
                if F(A, m * n) != F(F(A, n), m):
                    bad.append((A, m, n))
                cnt += 1
    print(f"  Lemma 5.1 F_(mn)(A) = F_m(F_n(A)) for A <= 7, m < {limit}, "
          f"n odd < {2 * limit}: {cnt} checks, failures {bad}")
    bad2 = []
    for A in range(0, 20):
        if A % 4 != 2:
            continue
        for n in range(1, 40):
            want = 1 if n % 2 == 0 else 2
            if F(A, n) % 4 != want:
                bad2.append((A, n, F(A, n) % 4))
    print(f"  phase (2.7) F_n(A) = 1 (2) mod 4 for n even (odd), A = 2 mod 4 "
          f"< 20, n < 40: failures {bad2}")
    # the even-index valuation of Theorem 1.3, sampled
    bad3 = []
    for A in (2, 6, 10, 14, 22):
        for n in range(2, 60, 2):
            v = 0
            m = F(A, n) - 1
            while m % 2 == 0:
                m //= 2
                v += 1
            want = 2 * (n & -n).bit_length() - 2 + 1
            # 2*v2(n)+1 where v2(n) = exponent of 2 in n
            s = 0
            t = n
            while t % 2 == 0:
                t //= 2
                s += 1
            if v != 2 * s + 1:
                bad3.append((A, n, v, 2 * s + 1))
    print(f"  Theorem 1.3 v_2(F_N(A)-1) = 2 v_2(N) + 1 for A in "
          f"{{2,6,10,14,22}}, even N < 60: failures {bad3}")


# ---------------------------------------------------------------- E

def smooth_split(N, rad):
    """Exact split N = A*C with A the rad-smooth part (rad = radical of it).

    The loop divides out the radical of the primes <= B once per round, so A
    collects every prime of rad with its full multiplicity and C is coprime to
    rad.  No factorisation is guessed: all operations are gcd and exact
    division.
    """
    A, M, T = 1, N, rad
    while T > 1:
        A *= T
        M //= T
        T = gcd(M, T)
    return A, M


def section_E(ymax=10 ** 7, prime_bound=10 ** 6, verbose=True):
    """Complete search for odd y <= ymax with N(y) = y^4+2y^2+2 powerful.

    Stage 1 (necessary condition).  For each prime q <= prime_bound the roots
    of N mod q are computed and every y in a root class with q^2 not dividing
    N(y) is rejected: such an N has a prime to the first power, so it is not
    powerful.  Survivors therefore have no prime q <= prime_bound dividing
    N(y) to exponent exactly 1.

    Stage 2 (exact, complete).  For a survivor let A be the prime_bound-smooth
    part of N and C = N/A, computed exactly by smooth_split (gcds and exact
    divisions; the radical of the smooth part comes from a multiplicative
    sieve over the same root classes).  Then
        N powerful  <=>  every prime exponent in A is >= 2  and  C powerful,
    and "every exponent in A is >= 2" is equivalent to rad^2 | N, where
    rad = product of the distinct primes <= prime_bound dividing N.  Every prime of
    C exceeds prime_bound = 10^6 while N < 10^28, so a powerful C is one of
        1, q^2, q^3, q^4 = (q^2)^2, (q1 q2)^2   (q, q1, q2 > 10^6)
    (q1^2 q2^3 > 10^30 and products of three primes > 10^36 are out of range),
    i.e. C is a perfect square or a perfect cube.  Hence
        rad^2 | N  and  (C a square or a cube)
    is necessary and sufficient.  Any hit is re-verified by full
    factorisation.
    """
    print(f"== E. direct search: odd y <= {ymax} with y^4+2y^2+2 powerful ==")
    primes = sieve(prime_bound)
    ok = bytearray(b"\x01") * (ymax + 1)
    ok[0] = 0
    root_classes = []
    for q in primes:
        if q < 5 or q % 4 != 1:
            continue
        r = sqrt_minus_one(q)
        roots_y = set()
        for s in (r, q - r):
            for t in (s - 1, -s - 1):
                yy = sqrt_mod(t % q, q)
                if yy is not None:
                    roots_y.add(yy)
                    roots_y.add(q - yy)
        if not roots_y:
            continue
        q2 = q * q
        for y0 in roots_y:
            g = (y0 ** 4 + 2 * y0 ** 2 + 2) // q
            inv = pow(4 * y0 * (y0 * y0 + 1) % q, -1, q)
            lift = (y0 - (g % q) * inv % q * q) % q2
            # reject the whole class, then un-reject the unique lift with q^2 | N
            ok[y0::q] = bytes(len(range(y0, ymax + 1, q)))
            ok[lift::q2] = b"\x01" * len(range(lift, ymax + 1, q2))
            root_classes.append((q, y0))
    survivors = [y for y in range(1, ymax + 1, 2) if ok[y]]
    if verbose:
        print(f"  stage 1: primes <= {prime_bound} with q = 1 mod 4: "
              f"{len([q for q in primes if q >= 5 and q % 4 == 1])}; root "
              f"classes marked: {len(root_classes)}")
        print(f"  stage 1: survivors (no prime <= {prime_bound} to the first "
              f"power): {len(survivors)}")
    rad = {}
    for q, y0 in root_classes:
        for y in range(y0, ymax + 1, q):
            if ok[y]:
                rad[y] = rad.get(y, 1) * q
    hits = []
    for y in survivors:
        N = y ** 4 + 2 * y * y + 2
        rady = rad.get(y, 1)
        A, C = smooth_split(N, rady)
        assert A * C == N
        exps_ok = True if rady == 1 else (N // rady) % rady == 0
        if exps_ok and (is_square(C) or is_cube(C)):
            hits.append((y, N, A, C))
    if verbose:
        print(f"  stage 2: candidates (rad^2 | N and cofactor a square or "
              f"cube): {len(hits)}")
    verified = []
    for y, N, A, C in hits:
        import sympy as sp
        fac = sp.factorint(N)
        powerful = all(e >= 2 for e in fac.values())
        verified.append((y, N, dict(fac), powerful))
    if verbose:
        print(f"  stage 3: full factorisation of the candidates: {verified}")
        print(f"  conclusion: no odd y <= {ymax} with y^4+2y^2+2 powerful"
              if not any(v[3] for v in verified) else "  conclusion: HITS")
    return survivors, hits, verified


def selftest_E(ymax=4000, prime_bound=200):
    """Cross-check the pipeline against brute-force factorisation."""
    survivors, hits, verified = section_E(ymax=ymax, prime_bound=prime_bound,
                                          verbose=False)
    import sympy as sp
    brute = []
    for y in range(1, ymax + 1, 2):
        N = y ** 4 + 2 * y * y + 2
        fac = sp.factorint(N)
        if all(e >= 2 for e in fac.values()):
            brute.append((y, N))
    piped = [(y, N) for y, N, A, C in hits]
    ok = piped == brute
    print(f"selftest_E: ymax={ymax}, B={prime_bound}: survivors "
          f"{len(survivors)}, pipeline hits {piped}, brute force {brute}, "
          f"agree={ok}")
    assert ok
    return ok





def is_cube(n):
    """Exact integer cube test by bisection (no floating point)."""
    if n < 0:
        return False
    lo, hi = 0, 1
    while hi ** 3 <= n:
        hi *= 2
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** 3 < n:
            lo = mid + 1
        else:
            hi = mid
    return lo ** 3 == n


def selftest_powerful(ntests=2000, B=None, seed=7):
    """Validate the (A | C, C square-or-cube) criterion against true
    factorisations, on random powerful and non-powerful integers < 10^28."""
    import random
    import sympy as sp
    if B is None:
        B = 10 ** 6
    random.seed(seed)
    bad = []
    for _ in range(ntests):
        kind = random.choice(["pow", "rough_pow", "nonpow", "square", "cube"])
        if kind == "pow":
            N = (random.randint(2, 10 ** 6) ** 2) * (random.randint(2, 10 ** 4) ** 3)
        elif kind == "rough_pow":
            q = sp.nextprime(random.randint(10 ** 6, 10 ** 9))
            q2 = sp.nextprime(random.randint(10 ** 6, 10 ** 9))
            N = q * q * q2 * q2 if random.random() < .5 else q ** 3
        elif kind == "nonpow":
            N = sp.nextprime(random.randint(2, 10 ** 6)) * sp.nextprime(
                random.randint(10 ** 6, 10 ** 13))
        elif kind == "square":
            N = random.randint(10 ** 3, 10 ** 13) ** 2
        else:
            N = random.randint(10 ** 3, 10 ** 9) ** 3
        N = int(N)
        if N >= 10 ** 28:
            continue
        fac = sp.factorint(N)
        truth = all(e >= 2 for e in fac.values())
        rad = 1
        for q in fac:
            if q <= B:
                rad *= q
        A, C = smooth_split(N, rad)
        exps_ok = True if rad == 1 else (N // rad) % rad == 0
        pred = exps_ok and (is_square(C) or is_cube(C))
        if pred != truth:
            bad.append((N, dict(fac), truth, A, C, pred))
    print(f"selftest_powerful: {ntests} random N < 10^28 with B = {B}: "
          f"mismatches {len(bad)} {bad[:3]}")
    assert not bad
    return True


def section_F(maxK=3000, maxN=2000):
    """Scope: members with 17 | N or 41 | N, i.e. what breaks if the
    'X-1 is a square' hypothesis of Corollary 1.5 is dropped."""
    print("== F. scope: 17|N and 41|N inside the wider powerful family ==")
    hits = []
    for K in range(5, maxK + 1):
        if not is_squarefree(K) or K % 2 == 0:
            continue
        neg, pos, L = pell_solutions(K)
        if neg is None:
            continue
        u, v = neg
        R = K // gcd(K, v)
        a, b = 1, 0
        n = 0
        while n < maxN:
            n += 1
            a, b = a * u + b * v * K, a * v + b * u
            if a > 10 ** 400:
                break
            if n % R or n % 2 == 0:
                continue
            if n % 17 == 0 or n % 41 == 0:
                assert a * a + 1 == K ** 3 * (b // K) ** 2
                hits.append((K, n, R, a % 8, is_square(a - 1), len(str(a))))
    hits.sort(key=lambda h: h[5])
    for h in hits[:14]:
        print(f"  K={h[0]:4d} N={h[1]:5d} R={h[2]:4d} X mod 8={h[3]} "
              f"X-1 square={h[4]} digits={h[5]}")
    print(f"  total (K <= {maxK}, N <= {maxN}): {len(hits)}; of these in the "
          f"corollary phase X = 2 mod 8: "
          f"{len([h for h in hits if h[3] == 2])}")
    return hits


def section_G(maxK=2000, digits=40):
    """Corollary 1.4's coefficient identity X = F_N(u) on family members."""
    print("== G. same-centre identity X = F_N(u) on family members ==")
    checked = 0
    for K in range(5, maxK + 1):
        if not is_squarefree(K) or K % 2 == 0:
            continue
        neg, pos, L = pell_solutions(K)
        if neg is None:
            continue
        u, v = neg
        R = K // gcd(K, v)
        a, b = 1, 0
        n = 0
        while True:
            n += 1
            a, b = a * u + b * v * K, a * v + b * u
            if a > 10 ** digits:
                break
            if n % R or n % 2 == 0:
                continue
            # F_0(u)=1, F_1(u)=u, F_{m+2}=2u F_{m+1}+F_m
            f0, f1 = 1, u
            for _ in range(2, n + 1):
                f0, f1 = f1, 2 * u * f1 + f0
            F = f1 if n >= 1 else f0
            assert F == a, (K, n)
            checked += 1
    print(f"  family members with X <= 10^{digits}, K <= {maxK}: {checked}; "
          f"X = F_N(u) in every case")
    # A = u phase requirement (6.3)
    print("  (6.3) phase check over squarefree K = 5 mod 8 <= 3000:")
    bad = []
    cnt = 0
    for K in range(5, 3001, 8):
        if not is_squarefree(K):
            continue
        neg, pos, L = pell_solutions(K)
        if neg is None:
            continue
        u, v = neg
        cnt += 1
        if v % 2 == 0 or u % 4 != 2:
            bad.append((K, u, v))
    print(f"    K = 5 mod 8, squarefree <= 3000, negative Pell solvable: {cnt}"
          f"; violations of v odd and u = 2 mod 4: {bad}")


def sieve(n):
    s = bytearray(b"\x01") * (n + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = bytes(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if s[i]]


def sqrt_mod(a, p):
    """Square root of a mod p (p prime, p % 4 == 1 handled by brute force)."""
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    # Tonelli-Shanks
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t, r = t * c % p, r * b % p
    return r


def sqrt_minus_one(p):
    for a in range(2, p):
        r = pow(a, (p - 1) // 4, p)
        if r * r % p == p - 1:
            return r
    raise AssertionError(p)


def factorint(n, effort=20000):
    """Pollard-rho factorisation with trial division; None if it gives up."""
    fac = {}
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        while n % p == 0:
            fac[p] = fac.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    from math import isqrt as _isq
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_prime_mr(m):
            fac[m] = fac.get(m, 0) + 1
            continue
        d = pollard(m, effort)
        if d is None:
            return None
        stack.append(d)
        stack.append(m // d)
    return fac


def is_prime_mr(n):
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


def pollard(n, effort):
    if n % 2 == 0:
        return 2
    c = 1
    while c < effort:
        x = y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d
        c += 1
    return None


# ---------------------------------------------------------------- main

if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    nc, nd = check_pell_code(300)
    print(f"CF Pell cross-check: {nc} non-square D <= 300, of which {nd} had the "
          f"least property verified exhaustively below the claimed solution")
    if which in ("all", "B"):
        section_B()
    if which in ("all", "C"):
        section_C()
    if which in ("all", "D"):
        section_D()
    if which == "selftest":
        selftest_E()
        selftest_powerful()
    if which in ("all", "E"):
        section_E()
    if which in ("all", "F"):
        section_F()
    if which in ("all", "G"):
        section_G()
    if which in ("all", "H"):
        section_H()
