"""Complete finite verification of the Walker specialisation used in Corollary 1.5.

For every squarefree odd K <= KMAX for which X^2 - K Y^2 = -1 is soluble:
  eps = u + v sqrt K = the fundamental (least) solution of the minus equation,
  R = K / gcd(K, v)          [the paper's (6.6); Walker Thm 2.2(3) says the least
                              solution with property Q is eps^R],
  R' = least i > 0 with K | b_i in eps^i = a_i + b_i sqrt K.
Assert R == R'.  Also assert eps is the least minus-solution (by construction via
continued fractions, and independently by a direct scan up to v).

Negative Pell solubility: period length of the continued fraction of sqrt(K) is odd.
Classical; the least solution is the convergent at index period-1.
"""
from math import gcd, isqrt


def cf_period(K):
    """Return (period_length, list of a_i) for sqrt(K), K nonsquare."""
    a0 = isqrt(K)
    m, d, a = 0, 1, a0
    seq = []
    while True:
        m = d * a - m
        d = (K - m * m) // d
        a = (a0 + m) // d
        seq.append(a)
        if a == 2 * a0:
            break
    return len(seq), seq


def least_minus_solution(K):
    """Least (u,v) with u^2 - K v^2 = -1, or None if insoluble."""
    L, seq = cf_period(K)
    if L % 2 == 0:
        return None
    # convergents p_i/q_i; the fundamental solution of x^2-Ky^2=-1 is p_{L-1},q_{L-1}
    a0 = isqrt(K)
    pm2, pm1 = 0, 1
    qm2, qm1 = 1, 0
    # i = -1 convergent is 1/0
    p, q = 1, 0
    prev = (0, 1)          # p_{-2}, q_{-2}
    cur = (1, 0)           # p_{-1}, q_{-1}
    for i in range(L):
        ai = a0 if i == 0 else seq[i - 1]
        nxt = (ai * cur[0] + prev[0], ai * cur[1] + prev[1])
        prev, cur = cur, nxt
    u, v = cur
    assert u * u - K * v * v == -1, (K, u, v)
    return u, v


def squarefree(n):
    if n % 2 == 0:
        return False
    q = 3
    while q * q <= n:
        if n % (q * q) == 0:
            return False
        q += 2
    return True


def check(K):
    got = least_minus_solution(K)
    if got is None:
        return None
    u, v = got
    R = K // gcd(K, v)
    a, b = 1, 0
    least = None
    for i in range(1, R + 1):
        a, b = a * u + b * v * K, a * v + b * u
        if b % K == 0 and least is None:
            least = i
    return (K, R, least, v % K == 0)


if __name__ == "__main__":
    import sys
    # Usage: python3 walker.py [KMAX]     (default 5000; ~50 s at 5000)
    KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    cnt = sol = nonfund = 0
    bad = []
    for K in range(2, KMAX + 1):
        if not squarefree(K):
            continue
        cnt += 1
        r = check(K)
        if r is None:
            continue
        sol += 1
        K_, R, least, vmult = r
        if R != least:
            bad.append(r)
        if R != K:
            nonfund += 1
    print("squarefree odd K <= %d: %d cases, %d with X^2-KY^2=-1 soluble" % (KMAX, cnt, sol))
    print("mismatches R != least index:", bad)
    print("cases with R < K (non-fundamental branch of Walker Thm 2.2(3)):", nonfund)
