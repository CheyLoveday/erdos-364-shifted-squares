"""Independent reconstruction and audit of the shifted-square 17/41 finite certificates.

Reproduces, from scratch with this author's own exact-integer / F_p / 2-adic code
(no PARI, no number-field routine), every finite datum in
  papers/shifted-square-17-41/manuscript/revision/paper_1_github.md
plus the exact statements the paper asserts without proof, plus stress tests.

Run:  python3 verify_independent.py       (about 15 s)
"""
import sys, json
from math import isqrt, gcd
sys.path.insert(0, ".")
sys.set_int_max_str_digits(0)
from exact import (padd, psub, pmul, pscale, pshift, peval, pdeg, trim,
                   dickson_polys, g_poly, jacobi, gcd as _g, ggcd, gtrim, gdivmod,
                   gmul, factor_fp, resultant_mod, disc_mod, primes_upto, is_prime,
                   dedekind_index_free)

FAIL = []
def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + ("   " + detail if detail else ""))
    if not cond:
        FAIL.append(name)

# ------------------------------------------------------------------ data
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
C17 = [-1,0,-1,1,1,-1,0,0,0,0,0,0,-2,0,1]
C41 = [-1,-15,2,4,8,7,-8,-10,-3,6,7,3,-1,-9,3,7,2,3,-9,-6,1,8,4,1,-4,-6,3,7,
       0,2,-7,-4,1,6,-1,0,-2,-5,4,5,-5]
U17GP = [-3,-2,-20,-4,-13,-1,70,0,102,0,53,0,12,0,1]   # literal u_17 in outer17_verify.gp

def from_dickson(c):
    u = [c[0]]                      # c_0 multiplies 1, not D_0 = 2   (4.7)/(4.8)
    for k in range(1, len(c)):
        u = padd(u, pscale(D[k], c[k]))
    return trim(u)

u = {17: from_dickson(C17), 41: from_dickson(C41)}

# ---- (1) polynomial reconstruction
check("g_17 = D_17 - 2 matches the certificate polynomial",
      g[17] == [-2,17,0,204,0,714,0,1122,0,935,0,442,0,119,0,17,0,1])
check("(4.4) equals the literal u_17 of outer17_verify.gp", u[17] == trim(U17GP))
check("U_17(4) = 532303029  (4.6)", peval(u[17], 4) == 532303029)
check("U_41(4) = -43956715453803235217163523  (4.10)",
      peval(u[41], 4) == -43956715453803235217163523)

# ---- (2) Lucas bridge  g_p(2A) = 2(F_p(A) - 1)
def Fpoly(p):
    f = [[1], [0, 1]]
    for n in range(2, p + 1):
        f.append(padd(pshift(pscale(f[n - 1], 2), 1), f[n - 2]))
    return trim(f[p])
for p in (17, 41):
    lhs = trim([c * 2 ** k for k, c in enumerate(g[p])])
    check(f"p={p}: g_p(2A) = 2(F_p(A)-1) as polynomials",
          lhs == psub(pscale(Fpoly(p), 2), [2]))
    Q = [c // 2 for c in lhs]
    check(f"p={p}: Q_0(A) = g_p(2A)/2 has integral coefficients and Q_0(0) = -1",
          all(c % 2 == 0 for c in lhs) and Q[0] == -1)
    check(f"p={p}: Q_0(A) == A - 1 (mod 8) as a polynomial  [2-adic criterion]",
          all(c % 8 == 0 for c in psub(trim(Q), [-1, 1])),
          f"coefficient of A is {Q[1]} = p")

# ---- (3) discriminant, irreducibility, Dedekind index
import sympy as sp
def resultant_exact(a, b):
    m, n = pdeg(a), pdeg(b)
    na, nb = sum(c*c for c in a), sum(c*c for c in b)
    bound = isqrt(na**n * nb**m) + 1
    M = 1; acc = 0
    for q in primes_upto(200000):
        M *= q
        if M > 4 * bound: break
    # rebuild with exactly the primes used
    M = 1; ps = []
    for q in primes_upto(200000):
        ps.append(q); M *= q
        if M > 4 * bound: break
    acc = 0
    for q in ps:
        r = resultant_mod([c % q for c in a], [c % q for c in b], q)
        acc = (acc + (r - acc) * (M // q) * pow(M // q, -1, q)) % M
    return (acc - M if acc > M // 2 else acc), len(ps)

def disc_exact(a):
    n = pdeg(a)
    r, k = resultant_exact(a, trim([(i * a[i]) for i in range(1, len(a))]))
    return (-r if (n*(n-1)//2) % 2 else r), k

for p, claim in ((17, 2**24 * 17**17), (41, 2**60 * 41**41)):
    d, k = disc_exact(g[p])
    check(f"p={p}: disc(g_p) = {claim}", d == claim, f"{k} primes, CRT")
    aux = 67 if p == 17 else 163
    fa = factor_fp(gtrim([c % aux for c in g[p]], aux), aux)
    check(f"p={p}: g_p irreducible over Q (single degree-{p} factor mod {aux})",
          len(fa) == 1 and len(fa[0]) - 1 == p)
    for q in (2, p):
        ok, det, reb = dedekind_index_free(g[p], q)
        check(f"p={p}: q={q} does not divide the power-order index (Dedekind)",
              ok and reb, f"(deg,mult) = {det}")
    r, k = resultant_exact(g[p], u[p])
    check(f"p={p}: Res(g_p, U_p) = -1", r == -1, f"{k} primes, CRT")

# ---- (4) reference values and Table A1
TABLE = {17: [(13, -1), (1751444197, 1)],
         41: [(79, 1), (1373, -1), (115471, -1), (1506563, -1), (1344905911, 1)]}
for p in (17, 41):
    g4, u4 = peval(g[p], 4), peval(u[p], 4)
    b4 = 4 * u4
    H = g4 // 2
    check(f"p={p}: H_p = g_p(4)/2 is squarefree with the stated factorisation",
          all(is_prime(l) for l, _ in TABLE[p]) and
          __import__('functools').reduce(lambda a, b: a*b, [l for l,_ in TABLE[p]], 1) == H)
    ok = all(jacobi(b4 % l, l) == s for l, s in TABLE[p])
    check(f"p={p}: Legendre(4U_p(4), ell) matches Table A1", ok)
    check(f"p={p}: J(U_p(4), H_p) = -1", jacobi(u4 % H, H) == -1)
    check(f"p={p}: H_p = 1 mod 8", H % 8 == 1)

# ---- (5) Appendix A.2 finite claims
PHI = {17: [1,1,0,0,1], 41: [1,1,0,1,1,0,0,1,1,0,1]}
PSI = {17: [1,1,1,1,1], 41: [1,1,0,0,1,0,0,0,0,1,1]}
for p in (17, 41):
    f, h = PHI[p], PSI[p]
    check(f"p={p}: phi_p, psi_p are distinct irreducibles over F_2 of degree (p-1)/4",
          factor_fp(f,2) == [gtrim(f,2)] and factor_fp(h,2) == [gtrim(h,2)]
          and gtrim(f,2) != gtrim(h,2) and len(f)-1 == (p-1)//4 == len(h)-1)
    prod = pshift(pmul(pmul(f, f), pmul(h, h)), 1)
    diff = psub(g[p], prod)
    corr = [c // 2 for c in diff]
    rem = gdivmod(gtrim([c % 2 for c in corr], 2), gmul(f, h, 2), 2)[1]
    check(f"p={p}: g_p = T phi^2 psi^2 mod 2 and the correction is 1 mod phi*psi (A.3)",
          all(c % 2 == 0 for c in diff) and gtrim(rem, 2) == [1])
    val = peval(g[p], 2)
    check(f"p={p}: (A.5) g_p(2)/p mod p = {(12 if p==17 else 26)}",
          (val // p) % p == (12 if p == 17 else 26))
    c = g[p]
    sc = lambda a: sum(1 for i in range(1, len(a)) if a[i-1]*a[i] < 0)
    cn = [(c[i] if i % 2 == 0 else -c[i]) for i in range(len(c))]
    check(f"p={p}: signature (1,{(p-1)//2}) by Descartes' rule", sc(c) == 1 and sc(cn) == 0)

# ---- (6) excluded statement-level claims: Table 1 / (2.9), Lemma 5.1, (2.7)
def F(n, A):
    f0, f1 = 1, A
    if n == 0: return 1
    for _ in range(2, n+1):
        f0, f1 = f1, 2*A*f1 + f0
    return f1
tab = {}
for A in (2,6,10,14,18,22,26,30,34):
    for n in (1,3,5,7,9,11,13,17,41):
        tab[(A % 8, n % 4)] = (F(n,A)-1) % 8
check("Table 1: (F_n(A)-1) mod 8 = n*A - 1 mod 8 for every odd n and even A",
      set(tab.values()) == {1, 5} and
      all(v == (a*n - 1) % 8 for (a, n), v in tab.items()) and
      tab[(2,1)] == 1 and tab[(2,3)] == 5 and tab[(6,1)] == 5 and tab[(6,3)] == 1)
check("Lemma 5.1: F_{mn}(A) = F_m(F_n(A)) for odd n",
      all(F(m*n, A) == F(m, F(n, A)) for A in (2,6,10,22) for n in (1,3,5,7)
          for m in (1,2,3,5,17)))
check("(2.7): F_m(A) = 2 mod 4 for A = 2 mod 4 and m odd",
      all(F(m, A) % 4 == 2 for A in range(2, 200, 4) for m in range(1, 40, 2)))
check("F_41(2)-1 = 20 mod 23 and 20 is a non-residue mod 23",
      (F(41,2)-1) % 23 == 20 and pow(20, 11, 23) != 1)

# ---- (7) dyadic symbol at the (e,f)=(1,1) prime  (its completion is Q_2)
NP = 128
def hens(r0, gp):
    r = r0 % (1 << NP)
    for _ in range(300):
        gr = peval(gp, r) % (1 << NP)
        if gr == 0: break
        gp_r = peval(trim([(i*c) for i, c in enumerate(gp)][1:]), r)
        r = (r - gr * pow(gp_r, -1, 1 << NP)) % (1 << NP)
    return r
def eps(x): return ((x - 1)//2) % 2
def delt(x): return ((x*x - 1)//8) % 2
for p in (17, 41):
    r = hens(2, g[p])
    s = r // 2
    M = NP - 8
    uu = ((2 - s) * pow(s, -1, 1 << M)) % (1 << M)
    ww = (s * peval(u[p], r)) % (1 << M)
    sym = (-1) ** (delt(uu) + eps(uu)*eps(ww))
    check(f"p={p}: (delta_4, b_p) = +1 at the degree-1 dyadic prime (direct Q_2 computation)",
          sym == 1 and peval(g[p], r) % (1 << NP) == 0 and r % 4 == 2,
          f"r = {r % 64} mod 64")

# ---- (8) stress tests
out = {}
for p, AMAX in ((17, 200000), (41, 60000)):
    bad = 0; cnt = 0
    for A in range(2, AMAX + 1, 8):
        x = 2*A
        Q = peval(g[p], x) // 2
        U = peval(u[p], x)
        cnt += 1
        if Q <= 0 or Q % 2 == 0 or gcd(U, Q) != 1 or jacobi(U % Q, Q) != -1:
            bad += 1
    check(f"p={p}: J(U_p(2A), F_p(A)-1) = -1, gcd = 1, Q>0 odd for all {cnt} phase A <= {AMAX}",
          bad == 0)

# ---- (9) ramified branch really occurs in the phase
for p in (17, 41):
    hits = [A for A in range(2, 20000, 8) if A % p == 1]
    vs = []
    for A in hits:
        Q = peval(g[p], 2*A) // 2
        v = 0
        while Q % p == 0:
            Q //= p; v += 1
        vs.append(v)
    check(f"p={p}: ramified branch A = 1 mod {p} occurs in the phase ({len(hits)} of A<20000) "
          f"and v_p(Q_0) = 1 there", len(hits) > 0 and set(vs) == {1})

print()
print("FIXED_CERTIFICATE_INDEPENDENT_OK" if not FAIL else f"FAILURES: {FAIL}")
sys.exit(1 if FAIL else 0)
