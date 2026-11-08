from exact import *
from math import isqrt
import json, sys
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
u = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
out = {}

# ---------- (A) 2-adic square criterion for Q_0(A) = F_p(A)-1, as a polynomial identity mod 8 ----------
c1 = {}
for p in (17, 41):
    Q = [c // 2 for c in [c * (2 ** k) for k, c in enumerate(g[p])]]
    Q = trim(Q)
    # Q(A) - (A - 1) mod 8 coefficients
    Qminus = psub(Q, [-1, 1])
    coeffs_mod8 = [c % 8 for c in Qminus]
    ident = all(c == 0 for c in coeffs_mod8)
    c1[p] = {"Q0_mod8_is_A_minus_1": ident,
             "coeffs_of_Q0_minus(A-1)_mod8": coeffs_mod8}
    print(f"p={p}: Q_0(A) == A - 1 (mod 8) as polynomial: {ident}   (Q_0 coeff of A = {Q[1]}, p mod 8 = {p%8})")

# numeric confirmation over all A = 2..4000
bad = []
for p in (17, 41):
    for A in range(2, 2001):
        Q = peval(g[p], 2 * A) // 2
        if (Q - (A - 1)) % 8 != 0:
            bad.append((p, A))
print("numeric Q0 == A-1 mod 8 failures for A<=2000:", bad[:5], "count", len(bad))

# ---------- (B) Theorem 1.3: v_2(F_N(A)-1) = 2 v_2(N) + 1 for A = 2 mod 4, N even ----------
def F(n, A):
    f0, f1 = 1, A
    if n == 0: return f0
    for _ in range(2, n + 1):
        f0, f1 = f1, 2 * A * f1 + f0
    return f1
def v2(m):
    k = 0
    while m % 2 == 0:
        m //= 2; k += 1
    return k
fails = []
tested = 0
for A in range(2, 400, 4):
    for N in range(2, 60, 2):
        val = F(N, A) - 1
        tested += 1
        if v2(val) != 2 * v2(N) + 1:
            fails.append((A, N, v2(val), 2 * v2(N) + 1))
print(f"Theorem 1.3: tested {tested} (A,N) pairs, failures: {fails[:5]} (count {len(fails)})")
out["thm13"] = {"tested": tested, "failures": fails[:10]}

# ---------- (C) direct test of Theorems 1.1/1.2: F_N(A)-1 never a square ----------
sq_fail = []
tested = 0
for A in range(2, 302, 4):
    for N in (17, 41, 34, 82, 51, 119, 68, 85, 102, 123):
        val = F(N, A) - 1
        tested += 1
        if val < 0:
            continue
        r = isqrt(val)
        if r * r == val:
            sq_fail.append((A, N, r))
print(f"Thm 1.1/1.2 direct: tested {tested} (A,N) pairs (A=2 mod 4, 17|N or 41|N), squares found: {sq_fail[:5]} (count {len(sq_fail)})")
out["thm11_direct"] = {"tested": tested, "squares": sq_fail[:10]}

# extra: A = 6 mod 8 branch specifically, larger A
sq6 = []
for A in range(6, 1200, 8):
    for N in (17, 41):
        val = F(N, A) - 1
        r = isqrt(val)
        if r * r == val:
            sq6.append((A, N))
print("A = 6 mod 8 branch squares:", sq6[:5], "count", len(sq6))

json.dump(out, open("claims.json", "w"), indent=1)
