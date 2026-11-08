from exact import *
from math import isqrt
import sys, json
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
u = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
out = {}
for p, AMAX in ((17, 1000000), (41, 300000)):
    cnt = 0; fails = []
    for A in range(2, AMAX + 1, 8):
        x = 2*A
        Q = peval(g[p], x) // 2
        U = peval(u[p], x)
        cnt += 1
        if gcd(U, Q) != 1 or Q <= 0 or Q % 2 == 0:
            fails.append((A, "side")); continue
        if jacobi(U % Q, Q) != -1:
            fails.append((A, "jacobi"))
    print(f"p={p}: {cnt} phase values up to A={AMAX}: failures {fails[:3]} (count {len(fails)})")
    out[p] = {"A_max": AMAX, "tested": cnt, "failures": fails[:5]}

# theorem conclusion, wider: F_N(A)-1 not a square
bad = []; tested = 0
for A in range(2, 402, 4):
    for N in (17, 51, 85, 119, 153, 187, 41, 123, 205, 287, 34, 68, 102, 136):
        v = 0
        f0, f1 = 1, A
        for _ in range(2, N+1):
            f0, f1 = f1, 2*A*f1+f0
        val = f1 - 1
        tested += 1
        if val > 0:
            r = isqrt(val)
            if r*r == val:
                bad.append((A, N))
print(f"direct non-square test: {tested} (A,N) pairs, squares: {bad[:3]} count {len(bad)}")
out["nonsquare"] = {"tested": tested, "squares": bad[:5]}
json.dump(out, open("extended.json","w"), indent=1)
