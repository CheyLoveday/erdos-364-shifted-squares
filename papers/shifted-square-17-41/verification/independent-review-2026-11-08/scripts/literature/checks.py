"""Independent checks of the two literature-derived steps in the 17/41 paper.

A. Sanna (Fib. Quart. 54 (2016) 118-124, Thm 1.5) specialised to a=2A, b=1:
   for A = 2 mod 4,  v_2(w_r) = v_2(r) + 1 for r even, = 0 for r odd,
   where w_0=0, w_1=1, w_{r+2} = 2A w_{r+1} + w_r (Sanna's u_r with a=2A,b=1).
   Also checks the paper's transfer F_{2r}-1 = 2(A^2+1) w_r^2 (r even).

B. Walker (Fib. Quart. 14 (1976) 111-116, eq.(3), Thm 2.2(2)-(3), Thm 2.5):
   for squarefree odd K, fundamental norm(-1) unit eps = u+v*sqrt(K),
   the least i>0 with K | b_i in eps^i = a_i + b_i sqrt(K) equals K/gcd(K,v).
   This is the paper's (6.5)-(6.6) and its R = K/gcd(K,v).

C. Scope: for odd primes p and A = 2 mod 4, search for F_p(A)-1 a square.
"""
from math import gcd, isqrt

def F(A, n):
    """F_0=1, F_1=A, F_{n+2}=2A F_{n+1}+F_n  (exact)."""
    a, b = 1, A
    if n == 0:
        return 1
    if n == 1:
        return A
    for _ in range(n - 1):
        a, b = b, 2 * A * b + a
    return b

def w(A, n):
    """w_0=0, w_1=1, w_{n+2}=2A w_{n+1}+w_n."""
    if n == 0:
        return 0
    a, b = 0, 1
    for _ in range(n - 1):
        a, b = b, 2 * A * b + a
    return b

def v2(m):
    assert m != 0
    m = abs(m)
    k = 0
    while m % 2 == 0:
        m //= 2
        k += 1
    return k

def part_A(nA=120, nR=40):
    bad = []
    for i in range(nA):
        A = 4 * i + 2
        for r in range(1, nR + 1):
            # Sanna's formula, specialised
            pred = (v2(r) + 1) if r % 2 == 0 else 0
            if v2(w(A, r)) != pred:
                bad.append(("sanna", A, r, v2(w(A, r)), pred))
            # conjugate-power identity F_r^2 - (A^2+1) w_r^2 = (-1)^r
            if F(A, r) ** 2 - (A * A + 1) * w(A, r) ** 2 != (-1) ** r:
                bad.append(("identity", A, r))
        for r in range(1, nR // 2 + 1):
            if r % 2 == 0 and F(A, 2 * r) - 1 != 2 * (A * A + 1) * w(A, r) ** 2:
                bad.append(("transfer", A, r))
    return bad

def sqrt_neg1_unit(K, bound=10 ** 7):
    """Least u+v sqrt(K) > 1 with u^2 - K v^2 = -1, brute force, or None."""
    for v in range(1, bound):
        u2 = K * v * v - 1
        u = isqrt(u2)
        if u * u == u2 and u > 0:
            return u, v
    return None

def part_B(Ks=None, imax=None):
    bad, checked, skipped = [], [], []
    if Ks is None:
        Ks = [2, 5, 10, 13, 17, 26, 29, 37, 41, 50, 53, 58, 61, 65, 73, 74, 82, 85,
              89, 97, 101, 106, 109, 113, 122, 125, 130, 137, 145, 149, 157, 170,
              173, 181, 185, 193, 197, 202, 205, 218, 221, 226, 229, 233, 241]
    for K in Ks:
        # squarefree test
        n, q, sq = K, 2, True
        while q * q <= n:
            if n % (q * q) == 0:
                sq = False
                break
            q += 1
        if not sq or K % 2 == 0:
            continue
        got = sqrt_neg1_unit(K)
        if got is None:
            skipped.append(K)
            continue
        u, v = got
        if u * u - K * v * v != -1:
            bad.append(("negpell", K))
            continue
        R = K // gcd(K, v)
        # brute-force least index with K | b_i
        a, b = 1, 0            # eps^0 = 1 + 0 sqrt(K)
        least = None
        for i in range(1, (imax if imax else K + 2) + 1):
            a, b = a * u + b * v * K, a * v + b * u
            if b % K == 0:
                least = i
                break
        if least != R:
            bad.append(("rank", K, least, R))
        else:
            checked.append((K, R))
    return bad, checked, skipped

def part_C(ps=(3, 5, 7, 11, 13), amax=400000):
    hits = {}
    for p in ps:
        sol = []
        A = 2
        while A <= amax:
            m = F(A, p) - 1
            y = isqrt(m)
            if y * y == m:
                sol.append((A, y))
            A += 4
        hits[p] = sol
    return hits

if __name__ == "__main__":
    print("A:", "OK" if not part_A() else part_A()[:5])
    bad, checked, skipped = part_B()
    print("B: checked", len(checked), "mismatches:", bad, "no-negPell:", skipped[:5])
    hits = part_C()
    for p, sol in hits.items():
        print("C: p=%d  #solutions with A=2 mod 4, A<=4e5: %d  first few: %s"
              % (p, len(sol), sol[:4]))
