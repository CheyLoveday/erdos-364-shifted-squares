from exact import *
import json, sys
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
u = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
out = {}
for p in (17, 41):
    # (i) ramified prime ell = p divides Q_0(A) iff A = 1 mod p
    hits = []
    for A in range(2, 3000, 8):
        if A % p == 1:
            x = 2 * A
            Q = peval(g[p], x) // 2
            v = 0; q = Q
            while q % p == 0:
                q //= p; v += 1
            J = jacobi(peval(u[p], x) % Q, Q)
            hits.append({"A": A, "v_p(Q)": v, "J(Up,Q)": J})
    print(f"p={p}: phase values A<=3000 with A=1 mod {p} (ramified prime divides Q_0): "
          f"{len(hits)} of which v_p>=2: {sum(1 for h in hits if h['v_p(Q)']>=2)}; J values: {sorted(set(h['J(Up,Q)'] for h in hits))}")
    print("   first few:", hits[:4])
    # (ii) small primes whose square divides Q_0(A) in the phase
    sq_hits = []
    for A in range(2, 20000, 8):
        Q = peval(g[p], 2 * A) // 2
        for ell in primes_upto(300):
            if Q % (ell * ell) == 0:
                sq_hits.append((A, ell))
    print(f"p={p}: phase A<=20000 with ell^2 | Q_0(A) for some prime ell<=300: {len(sq_hits)}; first {sq_hits[:6]}")
    out[p] = {"ramified_hits": hits[:6], "n_ramified": len(hits),
              "n_vp_ge2": sum(1 for h in hits if h["v_p(Q)"] >= 2),
              "sq_hits": sq_hits[:10], "n_sq_hits": len(sq_hits)}
json.dump(out, open("edges.json", "w"), indent=1)
