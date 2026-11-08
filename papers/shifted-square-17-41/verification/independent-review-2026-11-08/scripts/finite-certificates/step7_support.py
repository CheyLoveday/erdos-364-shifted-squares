from exact import *
import json, sys
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
u = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
claimed = {17: [(13, -1), (1751444197, 1)],
           41: [(79, 1), (1373, -1), (115471, -1), (1506563, -1), (1344905911, 1)]}
out = {}
deriv = {p: psub([(k * c) for k, c in enumerate(g[p])][1:], []) for p in g}
for p in (17, 41):
    g4, u4 = peval(g[p], 4), peval(u[p], 4)
    b4 = 4 * u4
    N = g4 // 2
    rows = []
    prod = 1
    for (ell, hs) in claimed[p]:
        simple = peval(g[p], 4) % ell == 0 and peval(deriv[p], 4) % ell != 0
        leg = jacobi(b4 % ell, ell)
        prod *= leg
        rows.append({"ell": ell, "simple_root_at_4": simple,
                     "v_ell(N)": sum(1 for e in range(1, 3) if N % ell**e == 0),
                     "legendre(b4,ell)": leg, "certificate_hilbert": hs,
                     "match": leg == hs})
        print(f"p={p} ell={ell}: 4 simple root of g mod ell = {simple}; "
              f"Legendre(b4)={leg}  certificate={hs}  {'MATCH' if leg==hs else 'MISMATCH'}")
    # product of the primes equals N exactly
    m = 1
    for (ell, _) in claimed[p]:
        m *= ell
    sq = all(N % (ell * ell) != 0 for (ell, _) in claimed[p])
    print(f"p={p}: prod(support) == N: {m == N};  N squarefree: {sq};  prod(Legendre) = {prod};  J(b4,N) = {jacobi(b4 % N, N)}")
    out[p] = {"rows": rows, "prod_eq_N": m == N, "prod_legendre": prod,
              "J_b4_N": jacobi(b4 % N, N)}
json.dump(out, open("support.json", "w"), indent=1)
