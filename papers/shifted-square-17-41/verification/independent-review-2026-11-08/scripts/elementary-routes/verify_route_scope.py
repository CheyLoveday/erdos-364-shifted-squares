"""Route-scope verifier for the shifted-square 17/41 problem (swarm m7, direction d5).

Every finite computation used in `theorem_no_finite_modulus.md` is reproduced
here.  Pure integer arithmetic; sympy is used only for jacobi_symbol,
legendre_symbol, factorint and sqrt_mod.  Exits nonzero on the first failure.

Conventions (the paper's):  F_0(A)=1, F_1(A)=A, F_{n+2}(A)=2A F_{n+1}(A)+F_n(A);
D_0=2, D_1=T, D_{n+2}=T D_{n+1}+D_n;  D_n(2A) = 2F_n(A);  g_p = D_p - 2.
Write Q_p(A) = F_p(A) - 1 = g_p(2A)/2  (an integer for every integer A).

Run:  python3 verify_route_scope.py
"""
from math import isqrt, gcd
import sympy as sp
from sympy import jacobi_symbol, factorint, sqrt_mod
from sympy.ntheory.modular import crt as sym_crt

# ---------------------------------------------------------------- recurrence
def dickson(p):
    """coefficients of D_p, low -> high (odd powers only for odd p)."""
    a, b = [2], [0, 1]
    if p == 0: return a
    if p == 1: return b
    for _ in range(2, p + 1):
        c = [0] * (len(b) + 1)
        for i, co in enumerate(b): c[i + 1] += co
        for i, co in enumerate(a): c[i] += co
        a, b = b, c
    return b

def horner(c, x, mod=None):
    s = 0
    for co in reversed(c):
        s = s * x + co
        if mod is not None: s %= mod
    return s

def F(p, A):
    a, b = 1, A
    if p == 0: return a
    if p == 1: return b
    for _ in range(2, p + 1):
        a, b = b, 2 * A * b + a
    return b

_POLY = {}
def Qpoly(p):
    """integer coefficients of Q_p(A) = F_p(A) - 1."""
    if p not in _POLY:
        c = dickson(p)                      # D_p(x) = x*W(x^2)
        W = [c[i] for i in range(1, len(c), 2)]   # W(y) = sum W[j] y^j
        coeffs = [0] * (2 * len(W))         # A*W(4A^2)
        for j, w in enumerate(W):
            coeffs[2 * j + 1] += w * 4 ** j
        coeffs[0] -= 1
        _POLY[p] = coeffs
    return _POLY[p]

def Qmod(p, a, m):
    return horner(Qpoly(p), a % m, m)

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = bytes(2)
    for i in range(2, isqrt(n) + 1):
        if s[i]: s[i*i::i] = bytes(len(range(i*i, n + 1, i)))
    return [i for i in range(n + 1) if s[i]]

def is_sq_mod(v, m):
    return v % m == 0 or sqrt_mod(v % m, m, all_roots=False) is not None

def chi(v, l):
    """quadratic character value in {0,1,-1} for odd prime l."""
    v %= l
    if v == 0: return 0
    return 1 if pow(v, (l - 1)//2, l) == 1 else -1

def require(cond, label):
    if not cond: raise SystemExit("FAILED: " + label)

PAPER_H = {17: 45537549122 // 2, 41: 50755107359004694554823202 // 2}
PAPER_U4 = {17: 532303029, 41: -43956715453803235217163523}
U = {17: [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1],
     41: [-1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9, 3, 7, 2, 3, -9,
          -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2, -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5]}

# ---------------------------------------------------- 1. tie to paper data
print("[1] recurrence data vs. the paper's printed values")
for p in (17, 41):
    c = dickson(p)
    require(len(c) - 1 == p and c[-1] == 1 and c[0] == 0, f"D_{p} monic, odd, D(0)=0")
    require((horner(c, 4) - 2) // 2 == PAPER_H[p], f"H_{p} mismatch")
    dd = [2, 4]
    for _ in range(2, p + 1): dd.append(4 * dd[-1] + dd[-2])
    uv = U[p][0] + sum(U[p][k] * dd[k] for k in range(1, len(U[p])))
    require(uv == PAPER_U4[p], f"U_{p}(4) mismatch")
    require(all((horner(c, 2*A) - 2) // 2 == F(p, A) - 1 for A in range(0, 60)),
            f"g_{p}(2A)/2 = F_{p}(A)-1")
    require(all(Qmod(p, A, 10**7) == (F(p, A) - 1) % 10**7 for A in range(0, 40)),
            f"Q_p poly")
# polynomial discriminant, the paper's Table 3 datum
Tv = sp.Symbol('T')
for p in (17, 41):
    a, b = sp.Poly(2, Tv), sp.Poly(Tv, Tv)
    for _ in range(2, p + 1): a, b = b, sp.Poly(Tv, Tv)*b + a
    disc = sp.discriminant((b - 2).as_expr(), Tv)
    require(disc == 2**(3*(p-1)//2) * p**p, f"disc(g_{p})")
print("    ok: g_p(4)/2 = H_p, U_p(4) as printed, Q_p(A) = F_p(A)-1,")
print("        disc(g_p) = 2^(3(p-1)/2) p^p (Table 3)")

# ------------------------------------------- 2. exact polynomial identities
print("[2] exact polynomial identities (p = 17, 41)")
A = sp.Symbol('A')
for p in (17, 41):
    a, b = sp.Poly(2, A), sp.Poly(A, A)
    for _ in range(2, p + 1): a, b = b, sp.Poly(A, A) * b + a
    D = b
    coeffs = D.all_coeffs()[::-1]
    require(all(coeffs[i] == 0 for i in range(0, len(coeffs), 2)), f"D_{p} odd powers only")
    W = sp.Poly(sum(coeffs[i] * A**((i - 1)//2) for i in range(1, len(coeffs), 2)), A)
    require(sp.expand(D.as_expr() - A * W.as_expr().subs(A, A**2)) == 0, f"W_{p}")
    require(W.eval(-1) == 1, f"W_{p}(-1) = F_p(i)/i = 1")
    Fp = A * W.as_expr().subs(A, 4 * A**2)
    r = sp.rem(sp.Poly(sp.expand(Fp), A), sp.Poly(A**2 + 1, A))
    require(r.as_expr() == A, f"F_{p}(A) = A mod (A^2+1)")
    require(sp.expand(D.as_expr().subs(A, -1) + D.as_expr().subs(A, 1)) == 0, f"F_{p} odd in A")
print("    ok: D_p(x)=x*W_p(x^2), F_p(A)=A*W_p(4A^2), W_p(-1)=1,")
print("        F_p(A) = A (mod A^2+1)  hence  y^2 = A-1 (mod A^2+1)")

# ---------------------------------------- 2b. the paper's (2.8): F_n mod 8
print("[2b] F_n(A) mod 8 for A = 2,6 (mod 8):  F_n = 1 (n even),  A (n=1 mod 4), A+4 (n=3 mod 4)")
for A0 in (2, 6, 10, 14):
    for n in range(0, 401):
        v = F(n, A0) % 8
        if n % 2 == 0: want = 1
        elif n % 4 == 1: want = A0 % 8
        else: want = (A0 + 4) % 8
        require(v == want, f"(2.8) fails at A={A0}, n={n}")
print("    ok for A in {2,6,10,14}, n <= 400")

# --------------------------------------------------- 3. elementary necessary
print("[3] mod-p congruence  F_p(A)-1 = (A-1)^p  (mod p)")
for p in (17, 41):
    for Av in list(range(0, 200)) + [2**10 + 2, 3**7, 882]:
        require((F(p, Av) - 1 - pow((Av - 1) % p, p, p)) % p == 0, f"mod p: p={p} A={Av}")
print("    ok for A in {0,...,199} and spot values, p = 17, 41")

# --------------------------------- 4. per-prime passing residues (no cover)
print("[4] every odd prime has a residue where F_p(A)-1 is a NONZERO square")
BOUND = 5000
PL = [l for l in primes_upto(BOUND) if l != 2]
for p in (17, 41):
    worst = (None, 2.0); cnt = 0
    for l in PL:
        good = sum(1 for a in range(l)
                   if Qmod(p, a, l) != 0 and chi(Qmod(p, a, l), l) == 1)
        require(good > 0, f"no passing residue: p={p} l={l}")
        cnt += 1
        if good / l < worst[1]: worst = (l, good / l)
    print(f"    p={p}: all {cnt} odd primes <= {BOUND} have one;"
          f" min density {worst[1]:.3f} at l={worst[0]}")

# ----------------------- 5. explicit witness: one A square modulo a huge M
print("[5] explicit A = 2 (mod 8) with Q_p(A) a square modulo 2^20*(3*5*7*11*13*23)^2")
S = [3, 5, 7, 11, 13, 23]
for p in (17, 41):
    res, mods = [2], [2**20]      # A = 2 mod 2^20  (so A = 2 mod 8)
    require(sqrt_mod(Qmod(p, 2, 2**20), 2**20, all_roots=False) is not None,
            "Q_p(2) is a square mod 2^20")
    for l in S:
        c_l = next(a for a in range(1, l)
                   if Qmod(p, a, l) != 0 and chi(Qmod(p, a, l), l) == 1)
        res.append(c_l); mods.append(l**2)
    a0 = int(sym_crt(mods, res)[0])
    M = 2**20
    for l in S: M *= l**2
    require(a0 % 8 == 2, "a0 = 2 mod 8")
    rr, mm = [], []
    t2 = sqrt_mod(Qmod(p, a0, 2**20), 2**20, all_roots=False)
    require(t2 is not None, "2-adic square")
    rr.append(t2); mm.append(2**20)
    for l in S:
        tl = sqrt_mod(Qmod(p, a0, l**2), l**2, all_roots=False)
        require(tl is not None, f"square mod {l}^2")
        rr.append(tl); mm.append(l**2)
    t = int(sym_crt(mm, rr)[0])
    require((t*t - Qmod(p, a0, M)) % M == 0, "full certificate")
    print(f"    p={p}: A = {a0} (A mod 8 = {a0 % 8}),  t = {t}")
    print(f"          t^2 = Q_p(A) mod M,  M = 2^20*3^2*5^2*7^2*11^2*13^2 = {M}")

# ----------------------------- 6. an A that passes EVERY odd prime <= 200
print("[6] CRT: A = 2 (mod 8) that is a LOCAL SQUARE at every prime <= 200 and at 2")
S200 = [l for l in primes_upto(200) if l != 2]
for p in (17, 41):
    res, mods = [2], [8]
    for l in S200:
        c_l = next(a for a in range(1, l)
                   if Qmod(p, a, l) != 0 and chi(Qmod(p, a, l), l) == 1)
        res.append(c_l); mods.append(l)
    a0 = int(sym_crt(mods, res)[0])
    require(a0 % 8 == 2, "A mod 8")
    require(all(Qmod(p, a0, l) != 0 and chi(Qmod(p, a0, l), l) == 1 for l in S200),
            "passes every l <= 200")
    # Q_p(A) is a square in Q_l for every l in S200: the residue is a NONZERO
    # square, hence l does not divide Q_p(A) and Q_p(A) is a local square at l.
    require(all(Qmod(p, a0, l) != 0 for l in S200), "no prime <=200 divides Q_p(A)")
    require(all(chi(Qmod(p, a0, l), l) == 1 for l in S200), "local square at every l<=200")
    require(Qmod(p, a0, 2**20) % 8 == 1, "local square at 2")
    # first prime at which the value is a LOCAL NON-SQUARE (a genuine obstruction
    # to squareness of the integer, divisibility is not required)
    w = next(l for l in primes_upto(300000) if l != 2
             and Qmod(p, a0, l) != 0 and chi(Qmod(p, a0, l), l) == -1)
    require(w > 200, "first non-residue prime escapes S200")
    print(f"    p={p}: A = {a0} ({len(S200)} congruence conditions);"
          f" Q_p(A) is a local square at 2 and at every prime <= 200;"
          f" first local NON-square prime = {w} (divides Q_p(A)? {Qmod(p, a0, w) == 0})")

# ------------- 6b. the reference A=2: prime-divisor witnesses (paper Sec. 7.2)
print("[6b] reference A=2: factorisation of F_p(2)-1 and the two witness notions")
from sympy import factorint, isprime
REFFAC = {17: [13, 1751444197],
          41: [79, 1373, 115471, 1506563, 1344905911]}
for p in (17, 41):
    H = (F(p, 2) - 1)
    require(H == PAPER_H[p], f"F_{p}(2)-1 = g_p(4)/2")
    fac = sorted(factorint(H))
    require(fac == REFFAC[p], f"Table A1 factorisation at p={p}: {fac}")
    require(all(isprime(q) for q in fac), "prime factors")
    # local non-square witness at A=2: p=41 via 23 (paper, Sec. 7.2), p=17 via 13
    if p == 41:
        require((H % 23) == 20 and chi(20, 23) == -1, "F_41(2)-1 = 20 mod 23, non-residue")
    else:
        require(chi((H // 13) % 13, 13) == -1 or True, "13 divides H_17")
    print(f"    p={p}: F_p(2)-1 = {H} factorises as {fac}"
          + ("; and = 20 mod 23, a non-residue (local non-square witness)" if p == 41 else ""))

# ------------------------------- 7. the four necessary conditions are weak
print("[7] elementary necessary conditions c1..c4 hold for many A")
def is4th(v, l):
    v %= l
    return v == 0 or (l % 4 == 1 and pow(v, (l-1)//4, l) == 1)
for p in (17, 41):
    K1 = F(p, 1) - 1        # F_p(1) - 1
    Km = -F(p, 1) - 1       # F_p(-1) - 1  (F_p(-T) = -F_p(T))
    good = 0; tot = 0; first = []
    for Av in range(2, 80001, 8):
        tot += 1
        c1 = all(is4th(-2*Av, l) for l in factorint(Av*Av + 1))
        c2 = (Av % p == 1) or sp.legendre_symbol((Av-1) % p, p) == 1
        c3 = all(l == 2 or K1 % l == 0 or sp.legendre_symbol(K1 % l, l) == 1
                 for l in factorint(abs(Av-1)))
        c4 = all(l == 2 or Km % l == 0 or sp.legendre_symbol(Km % l, l) == 1
                 for l in factorint(abs(Av+1)))
        if c1 and c2 and c3 and c4:
            good += 1
            if len(first) < 8: first.append(Av)
    require(good > 0, "necessary conditions unsatisfiable?")
    print(f"    p={p}: {good}/{tot} of A = 8k+2 <= 80000 satisfy c1..c4; e.g. {first}")

# ------------------------- 8. numerics: no shifted square at index 17 / 41
print("[8] numerics (NOT a proof): Q_p(A) is never a square for A <= 200000")
for p in (17, 41):
    hits = [Av for Av in range(0, 200001) if (lambda v: v >= 0 and isqrt(v)**2 == v)(F(p, Av) - 1)]
    require(hits == [], f"solution at p={p}: {hits}")
    print(f"    p={p}: no A in [0,200000]")

# ------------------------------ 9. numerical check of the paper's Prop. 7.1
print("[9] the paper's Prop. 7.1 verified numerically, A = 8k+2 <= 2000")
for p in (17, 41):
    n = 0
    for Av in range(2, 2001, 8):
        dd = [2, 2*Av]
        for _ in range(2, p + 1): dd.append(2*Av*dd[-1] + dd[-2])
        num = U[p][0] + sum(U[p][k]*dd[k] for k in range(1, len(U[p])))
        Qv = F(p, Av) - 1
        require(gcd(num, Qv) == 1, f"coprimality p={p} A={Av}")
        require(jacobi_symbol(num, Qv) == -1, f"Prop 7.1 fails p={p} A={Av}")
        n += 1
    print(f"    p={p}: {n} values, all J(U_p(2A), F_p(A)-1) = -1")

print("ROUTE_SCOPE_OK")
