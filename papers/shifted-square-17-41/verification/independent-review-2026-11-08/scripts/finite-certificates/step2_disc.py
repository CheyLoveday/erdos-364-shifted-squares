from exact import *
import json
D = dickson_polys(41)
def load(f): return eval(open(f).read())
g = {17: g_poly(17), 41: g_poly(41)}
claim = {17: 2**24 * 17**17, 41: 2**60 * 41**41}

def l2(a): return sum(c*c for c in a)

for p in (17,41):
    gp = g[p]; n = pdeg(gp)
    # rigorous bound: |disc(P)| <= n^n * M(P)^(2n-2), M(P) <= ||P||_2
    norm2 = l2(gp)
    # integer bound: disc^2 ... use crude float-free: bound = n^n * norm2^(n-1)
    bound = n**n * norm2**(n-1)
    print(p, "deg", n, "||g||^2 =", norm2, "bound ~ 10^%.1f" % (len(str(bound))-1))
    M = 1
    ps = []
    for q in primes_upto(60000):
        if q in (2, 17, 41):   # keep all, but avoid division hazards anyway
            continue
        if pdeg(trim([c % q for c in gp])) < n:
            continue
        ps.append(q)
        M *= q
        if M > 4 * bound:
            break
    print("   using", len(ps), "primes, M ~ 10^%d" % (len(str(M))-1))
    res = 0
    for q in ps:
        r = disc_mod([c % q for c in gp], q)
        # CRT
        Minv = pow(M // q, -1, q)
        res = (res + (r - res) * (M // q) * Minv) % M
    if res > M // 2:
        res -= M
    print("   disc(g) mod M  ==  claim mod M:", res % M == claim[p] % M)
    print("   exact residue  =", res, " claim =", claim[p], " MATCH:", res == claim[p])
