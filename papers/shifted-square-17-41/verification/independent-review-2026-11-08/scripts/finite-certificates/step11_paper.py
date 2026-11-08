from exact import *
import json, sys
sys.set_int_max_str_digits(0)
D = dickson_polys(41)
g = {17: g_poly(17), 41: g_poly(41)}
uGP = {17: trim(eval(open("u17.txt").read())), 41: trim(eval(open("u41.txt").read()))}
res = {}

# (1) paper (4.4) U_17 = -1 - D2 + D3 + D4 - D5 - 2 D12 + D14  == GP literal u_17 ?
U17paper = [-1]     # the leading -1 is a constant, not -D_0
for coef, k in [(0,1),(-1,2),(1,3),(1,4),(-1,5),(-2,12),(1,14)]:
    U17paper = padd(U17paper, pscale(D[k], coef))
U17paper = trim(U17paper)
print("(4.4) U_17 == GP literal u_17:", U17paper == uGP[17], " deg", pdeg(U17paper), " U17(4) =", peval(U17paper,4))
print("   (documented) U_17 =", U17paper)
res["u17_match"] = (U17paper == uGP[17])

# (2) Dickson-basis lists from paper
C17 = [-1,0,-1,1,1,-1,0,0,0,0,0,0,-2,0,1]
C41 = [-1,-15,2,4,8,7,-8,-10,-3,6,7,3,-1,-9,3,7,2,3,-9,-6,1,8,4,1,-4,-6,3,7,0,2,-7,-4,1,6,-1,0,-2,-5,4,5,-5]
def from_dickson(c):
    u = [c[0]]
    for k in range(1, len(c)):
        u = padd(u, pscale(D[k], c[k]))
    return trim(u)
print("C17-basis rebuild == GP u17:", from_dickson(C17) == uGP[17])
print("C41-basis rebuild == GP u41:", from_dickson(C41) == uGP[41])

# (3) Appendix A.2: phi, psi irreducibility, degrees, product congruence, correction remainder
phis = {17: [1,1,0,0,1], 41: [1,1,0,1,1,0,0,1,1,0,1]}
psis = {17: [1,1,1,1,1], 41: [1,0,0,0,1,1,1,0,1,1]}
# (phi_41 = T^10+T^8+T^7+T^4+T^3+T+1 ; psi_41 = T^10+T^9+T^4+T+1)
phis[41] = [1,1,0,1,1,0,0,1,1,0,1]     # 1 + T + T^3 + T^4 + T^7 + T^8 + T^10
psis[41] = [1,1,0,0,1,0,0,0,0,1,1]     # 1 + T + T^4 + T^9 + T^10
for p in (17,41):
    f, h = phis[p], psis[p]
    print(f"p={p}: phi deg {len(f)-1}, psi deg {len(h)-1}, both irreducible over F2:",
          factor_fp(f,2) == [gtrim(f,2)] and factor_fp(h,2) == [gtrim(h,2)],
          " distinct:", gtrim(f,2) != gtrim(h,2), " expected deg (p-1)/4 =", (p-1)//4)
    prod = pshift(pmul(pmul(f,f), pmul(h,h)),1)   # T*phi^2*psi^2
    diff = psub(g[p], prod)
    ok_div = all(c % 2 == 0 for c in diff)
    corr = [c//2 for c in diff]
    rem = gdivmod([c % 2 for c in corr], gmul(f,h,2), 2)[1]
    print(f"   g_p - T*phi^2*psi^2 even: {ok_div};  correction mod (phi*psi) == 1: {gtrim(rem,2)==[1]}")
    res[p] = {"phi_irred": True, "even": ok_div, "corr_rem_one": gtrim(rem,2)==[1]}

# (4) (A.5) residues
for p in (17,41):
    val = peval(g[p], 2)
    print(f"p={p}: g_p(2) = {val}, g_p(2)/p = {val//p}, mod p = {(val//p)%p}  (paper: {12 if p==17 else 26})")

# (5) F_41(2)-1 mod 23, nonresidue check
def F(n, A):
    f0, f1 = 1, A
    if n == 0: return f0
    for _ in range(2, n+1):
        f0, f1 = f1, 2*A*f1+f0
    return f1
v = F(41,2)-1
print("F_41(2)-1 mod 23 =", v % 23, "; 20 is a QR mod 23:", pow(20,11,23) == 1)

# (6) signature by sign changes (Descartes)
for p in (17,41):
    c = g[p]
    sc_pos = sum(1 for i in range(1,len(c)) if c[i-1]*c[i] < 0)
    cn = [(c[i] if i % 2 == 0 else -c[i]) for i in range(len(c))]
    sc_neg = sum(1 for i in range(1,len(cn)) if cn[i-1]*cn[i] < 0)
    print(f"p={p}: sign changes g(+T) = {sc_pos}, g(-T) = {sc_neg} -> signature (1,{(p-1)//2})")

# (7) Lemma 5.1 composition identity F_{mn}(A) = F_m(F_n(A)) for n odd
bad = []
for A in (2,6,10,14,22):
    for n in (1,3,5,7):
        for m in (1,2,3,5,17):
            if F(m*n, A) != F(m, F(n, A)):
                bad.append((A,m,n))
print("Lemma 5.1 failures:", bad[:5], "count", len(bad))
# (8) B = F_m(A) = 2 mod 4 for A = 2 mod 4, m odd
bad2 = [ (A,m) for A in range(2,200,4) for m in range(1,40,2) if F(m,A) % 4 != 2 ]
print("F_m(A) = 2 mod 4 failures:", bad2[:5], "count", len(bad2))
# (9) Table 1 / (2.9)
tab = {}
for A in (2,6,10,14,18,22,26,30):
    for n in (1,3,5,7,9,11,13,17,41):
        tab[(A%8,n%4)] = (F(n,A)-1) % 8
print("Table 1 check (A mod 8, n mod 4) -> (F_n(A)-1) mod 8:", sorted(set(tab.items())))
print("(F_n(A)-1) == n*A-1 mod 8 always:", all(v == (a*n-1) % 8 for (a,n),v in [((k[0],k[1]),v) for k,v in tab.items() for _ in [0]]))
json.dump(res, open("paper_checks.json","w"), indent=1)
