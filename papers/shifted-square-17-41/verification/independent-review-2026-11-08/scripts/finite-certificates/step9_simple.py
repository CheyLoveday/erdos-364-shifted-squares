from exact import *
import json, sys
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
der = {p: trim([(k * c) for k, c in enumerate(g[p])][1:]) for p in g}
out = {}
for p, AMAX in ((17, 200000), (41, 60000)):
    bad, badram = [], []
    cnt = 0
    for A in range(2, AMAX + 1, 8):
        x = 2 * A
        Q = peval(g[p], x) // 2
        G = gcd(Q, peval(der[p], x))
        cnt += 1
        if G != 1:
            # split into the ramified part p^v and the rest
            vp = 0
            while G % p == 0:
                G //= p; vp += 1
            if G != 1:
                bad.append((A, G, x))
            else:
                badram.append((A, vp))
    print(f"p={p}: {cnt} phase values A<={AMAX}: gcd(Q, g_p'(x))>1 in {len(badram)+len(bad)} cases")
    print(f"   of these, non-{p}-part trivial: {len(badram)}   NON-RAMIFIED failures: {len(bad)}")
    if bad: print("   first non-ramified failures:", [(a, str(b)[:60]) for a, b, _x in bad[:5]])
    out[p] = {"tested": cnt, "A_max": AMAX, "ramified_only": len(badram),
              "nonramified_failures": [(a, str(b)[:80]) for a, b, _x in bad[:10]]}

# also: for the ramified branch, is v_p(Q) ever >= 2 (which would break the exponent match)?
for p in (17, 41):
    hits = []
    for A in range(2, 400000, 8):
        if A % p == 1:
            Q = peval(g[p], 2 * A) // 2
            v = 0; q = Q
            while q % p == 0:
                q //= p; v += 1
            if v != 1:
                hits.append((A, v))
    print(f"p={p}: phase A<400000 with A=1 mod {p}: v_p(Q) != 1 in {len(hits)} cases; first {hits[:5]}")
    out[p]["vp_not_one"] = hits[:5]
json.dump(out, open("simple.json", "w"), indent=1)
