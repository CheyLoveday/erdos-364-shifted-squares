"""Search for members of Corollary 1.5's family.

Cor 1.5 assumes X >= 2, X-1 = square, X^2+1 powerful.  By (1.7)-(1.8) such an X
arises exactly from a squarefree odd K and a solution X + Y*sqrt(K) of X^2-KY^2 = -1
with K | Y (then X^2+1 = K^3 V^2, V = Y/K), together with X = 2 mod 8.

Enumerate all such (K, X) with K squarefree odd <= KMAX and X <= XMAX:
  eps = fundamental minus-solution of X^2-KY^2 = -1 (odd CF period),
  take odd powers eps^n, keep those with K | Y, test X = 2 mod 8 and X-1 square.
Report every hit.  Complete for X <= XMAX among kernels K <= KMAX.
"""
from math import gcd, isqrt
import sys

sys.setrecursionlimit(10000)


def cf_period_odd(K):
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
    return len(seq) % 2 == 1, len(seq), seq


def fund_minus(K):
    odd, L, seq = cf_period_odd(K)
    if not odd:
        return None
    a0 = isqrt(K)
    prev, cur = (0, 1), (1, 0)
    for i in range(L):
        ai = a0 if i == 0 else seq[i - 1]
        prev, cur = cur, (ai * cur[0] + prev[0], ai * cur[1] + prev[1])
    u, v = cur
    assert u * u - K * v * v == -1
    return u, v


def squarefree(n):
    q = 3
    while q * q <= n:
        if n % (q * q) == 0:
            return False
        q += 2
    return True


def run(KMAX, XMAX):
    hits = []
    kernels = 0
    candidates = 0
    for K in range(3, KMAX + 1, 2):
        if not squarefree(K):
            continue
        got = fund_minus(K)
        if got is None:
            continue
        kernels += 1
        u, v = got
        # eps^n for odd n, by repeated multiplication by eps^2
        U2 = u * u + K * v * v          # eps^2 = U2 + V2 sqrt(K)
        V2 = 2 * u * v
        X, Y = u, v                      # n = 1
        while X <= XMAX:
            if Y % K == 0:               # property Q
                candidates += 1
                if X % 8 == 2:
                    r = isqrt(X - 1)
                    if r * r == X - 1:
                        hits.append((K, X, Y // K))
            X, Y = X * U2 + Y * V2 * K, X * V2 + Y * U2
    return hits, kernels, candidates


if __name__ == "__main__":
    KMAX, XMAX = 30000, 10 ** 30
    hits, kernels, cand = run(KMAX, XMAX)
    print("K squarefree odd <= %d with X^2-KY^2=-1 soluble: %d kernels" % (KMAX, kernels))
    print("property-Q canonical candidates X <= 10^30: %d" % cand)
    print("hits (X-1 a square):", hits)
