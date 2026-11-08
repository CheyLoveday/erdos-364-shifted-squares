from exact import *
import json, sys
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
u = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
N = 96          # 2-adic precision

def hens_root(gp, N):
    """root r of g_p in Z_2 with v_2(r) = 1 (the P1-embedding: theta -> 0 mod 2)."""
    r = 2
    for _ in range(200):
        gr = peval(gp, r) % (1 << N)
        if gr == 0:
            break
        gp_r = peval(trim([(k * c) for k, c in enumerate(gp)][1:]), r)
        assert gp_r % 2 == 1, "derivative not a unit"
        inv = pow(gp_r, -1, 1 << N)
        step = (gr * inv) % (1 << N)
        # r must be corrected by a quantity divisible by v_2(gr)
        r = (r - step) % (1 << N)
    return r % (1 << N)

def eps2(x):
    """x odd 2-adic unit mod 2^N -> (x-1)/2 mod 2"""
    return ((x - 1) // 2) % 2

def sq2(x):
    """(x^2-1)/8 mod 2 for x odd"""
    return ((x * x - 1) // 8) % 2

out = {}
for p in (17, 41):
    r = hens_root(g[p], N)
    assert peval(g[p], r) % (1 << N) == 0
    assert r % 4 == 2, ("v_2(r) should be 1", r % 8)
    s = r // 2                      # odd unit, r = 2s
    assert s % 2 == 1
    M = N - 4
    # u = delta_4 under theta -> r :  (4 - r)/r = (2 - s)/s
    num = (2 - s) % (1 << M)
    uu = (num * pow(s % (1 << M), -1, 1 << M)) % (1 << M)
    # w = b/2 = s * U_p(2s)
    w = (s * peval(u[p], r)) % (1 << M)
    assert uu % 2 == 1 and w % 2 == 1
    # (uu, 2)_2 * (uu, w)_2
    sym = (-1) ** (sq2(uu) + eps2(uu) * eps2(w))
    out[p] = {"r mod 2^6": r % 64, "s mod 8": s % 8, "u mod 32": uu % 32, "w mod 32": w % 32,
              "hilbert_P1": sym}
    print(f"p={p}: 2-adic root r = {r % 64} mod 64 (v_2(r)=1); "
          f"u=(4-r)/r = {uu % 32} mod 32; w=b/2 = {w % 32} mod 32")
    print(f"      (delta_4,b)_P1 = (u,2)_2 (u,w)_2 = {sym}   [certificate: +1]")
json.dump({str(k): v for k, v in out.items()}, open("dyadic.json", "w"), indent=1)
