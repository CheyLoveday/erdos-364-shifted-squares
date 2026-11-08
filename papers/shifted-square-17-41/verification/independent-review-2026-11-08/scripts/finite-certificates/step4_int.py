from exact import *
from math import isqrt
import json
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
u = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
res = {}

# ---------- exact resultant over Z via modular residues + CRT with rigorous bound ----------
def resultant_exact(a, b, verbose=False):
    import sys
    sys.set_int_max_str_digits(0)
    m, n = pdeg(a), pdeg(b)
    # Landau-Mignotte: |Res(P,Q)| <= ||P||_2^{deg Q} * ||Q||_2^{deg P}
    na = sum(c * c for c in a); nb = sum(c * c for c in b)
    # integer-safe version: bound^2 = na^n * nb^m
    bound = na ** (n // 2) * nb ** ((m + 1) // 2) * (na ** (n % 2 and 1 or 0)) * (nb ** (m % 2 and 1 or 0))
    bound = na ** n * nb ** m
    bound = isqrt(bound) + 1
    M = 1; ps = []
    for q in primes_upto(200000):
        ps.append(q); M *= q
        if M > 4 * bound:
            break
    acc = 0
    for q in ps:
        r = resultant_mod([c % q for c in a], [c % q for c in b], q)
        acc = (acc + (r - acc) * (M // q) * pow(M // q, -1, q)) % M
    if acc > M // 2:
        acc -= M
    if verbose:
        print("   resultant bound 10^%d, %d primes" % (len(str(bound)) - 1, len(ps)))
    return acc, bound, len(ps)

for p in (17, 41):
    r, bd, npr = resultant_exact(g[p], u[p], verbose=True)
    print(f"p={p}: Res(g_p, u_p) = {r}   (claimed -1)  digits(bound)={len(str(bd))-1}")
    res[p] = {"resultant_g_u": r, "digits_bound": len(str(bd)) - 1, "nprimes": npr}
    # N(theta) = (-1)^n g(0)
    nth = (-1) ** p * g[p][0]
    print(f"p={p}: N(theta) = {nth} (claimed 2);  N(u) = {r} (claimed -1);  N(b) = {-2*r}")
json.dump({str(k): v for k, v in res.items()}, open("resultants.json", "w"), indent=1)
