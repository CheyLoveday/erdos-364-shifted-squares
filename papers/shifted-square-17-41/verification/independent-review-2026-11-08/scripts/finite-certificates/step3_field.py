from exact import *
import json
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
out = {}
for p, small in ((17, 67), (41, 163)):
    gp = g[p]
    # (1) irreducibility over Q via reduction mod a prime
    gs = gtrim([c % small for c in gp], small)
    facs = factor_fp(gs, small)
    irr = (len(facs) == 1 and len(facs[0]) - 1 == p)
    out[p] = {"irred_mod": small, "irred_mod_ok": irr}
    # (2) Dedekind criterion at the primes dividing disc(g)
    for q in (2, p):
        ok, det, chk = dedekind_index_free(gp, q)
        out[p][f"ded_p{q}"] = {"index_coprime": ok, "ef": det, "rebuild": chk}
        print(f"p={p} q={q}: index coprime to q = {ok}; (deg,mult) of g mod q = {det}; rebuild={chk}")
    print(f"p={p}: g irreducible mod {small}: {irr}; factors = {[(len(f)-1) for f in facs]}")
json.dump(out, open("field_data.json", "w"), indent=1)
