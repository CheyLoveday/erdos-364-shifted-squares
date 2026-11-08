from exact import *
import json, sys
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
u = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
ref = {}

# ---- reference value x = 4 (A = 2) ----
for p in (17, 41):
    g4, u4 = peval(g[p], 4), peval(u[p], 4)
    b4 = 4 * u4
    N = g4 // 2
    ref[p] = {"g4": g4, "u4": u4, "b4": b4, "N": N,
              "g4_odd": g4 % 2, "N_odd": N % 2, "N_mod8": N % 8,
              "J_u4_N": jacobi(u4 % N if N > 0 else u4, N),
              "J_b4_N": jacobi(b4 % N, N),
              "gcd_u4_N": gcd(u4, N), "gcd_b4_N": gcd(b4, N)}
    print(f"p={p}: g(4)={g4}  u(4)={u4}  b(4)={b4}")
    print(f"      N=g(4)/2={N}  N mod 8={N%8}  J(u4,N)={ref[p]['J_u4_N']}  J(b4,N)={ref[p]['J_b4_N']}")
    # factorisation of N
    fac = []
    m = N
    d = 2
    while d * d <= m and d < 10**7:
        while m % d == 0:
            fac.append(d); m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        fac.append(m)
    ref[p]["N_factors"] = fac
    print("      N factored:", fac, " all prime:", all(is_prime(f) for f in fac))

# ---- phase stress test ----
for p, AMAX in ((17, 60000), (41, 20000)):
    bad_j, bad_gcd, bad_odd, bad_pos, worst = [], [], [], [], None
    cnt = 0
    for A in range(2, AMAX + 1, 8):
        x = 2 * A
        Q = peval(g[p], x) // 2
        U = peval(u[p], x)
        cnt += 1
        if Q <= 0: bad_pos.append(A)
        if Q % 2 == 0: bad_odd.append(A)
        gg = gcd(U, Q)
        if gg != 1: bad_gcd.append((A, gg))
        j = jacobi(U % Q, Q) if Q > 0 else None
        if j != -1: bad_j.append((A, j))
    ref[p]["phase"] = {"A_values": cnt, "A_max": AMAX,
                       "nonpos": bad_pos[:5], "even": bad_odd[:5],
                       "gcd_failures": bad_gcd[:5], "jacobi_failures": bad_j[:5]}
    print(f"p={p}: tested {cnt} phase values A=2..{AMAX} (step 8): "
          f"Q<=0 {len(bad_pos)}, Q even {len(bad_odd)}, gcd!=1 {len(bad_gcd)}, J!=-1 {len(bad_j)}")
json.dump({str(k): v for k, v in ref.items()}, open("references.json", "w"), indent=1)
