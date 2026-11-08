"""Independent recomputation of every finite datum in the Hilbert route of
papers/shifted-square-17-41 (Theorem 3.2 hypotheses 1-5 at p=17,41).
Run:  python3 work/certificate_check.py     (from .ultramath/smw70l62n/m3)"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from defs import *
from sympy import Poly, factor_list, factorint, legendre_symbol, resultant, discriminant

def dedekind_index_one(G, ell):
    """Dedekind's index criterion: True iff ell does NOT divide [O_L:Z[theta]].
    Validated below on Z[sqrt5] (index 2 at 2 -> False), Z[sqrt-3] (index 2 at 2 -> False),
    Z[sqrt2] (index 1 -> True)."""
    Gx = Poly(G.as_expr(), T)
    facs = factor_list(Gx, modulus=ell)[1]
    prod = Poly(1, T)
    for h, e in facs:
        prod = prod * Poly(h.as_expr(), T)**e
    q = Poly((Gx.as_expr() - prod.as_expr())/ell, T, modulus=ell)
    for h, e in facs:
        if e == 1: continue
        if q.rem(Poly(h.as_expr(), T, modulus=ell)).is_zero:
            return False
    return True

print("== sanity checks of the Dedekind routine ==")
print("  Z[sqrt5]  at 2 (expect False, index 2):", dedekind_index_one(Poly(T**2-5, T), 2))
print("  Z[sqrt-3] at 2 (expect False, index 2):", dedekind_index_one(Poly(T**2+3, T), 2))
print("  Z[sqrt2]  at 2 (expect True):          ", dedekind_index_one(Poly(T**2-2, T), 2))
print()
for p in (17, 41):
    G = g(p); U = U17() if p == 17 else U41()
    print(f"===== p = {p} =====")
    print("  g_p degree", G.degree(), " g_p(0) =", G.eval(0), " (=> N(theta) = 2, odd degree)")
    print("  irreducible over Q:", Poly(G.as_expr(), T).is_irreducible)
    print("  disc(g_p) =", factorint(discriminant(G.as_expr(), T)))
    print("  Dedekind at 2:", dedekind_index_one(G, 2), " at p:", dedekind_index_one(G, p),
          " (disc has no other prime divisors => index 1)")
    print("  Res(g_p,U_p) =", resultant(G.as_expr(), U.as_expr(), T), " (=> U_p(theta) a unit)")
    gf = factor_list(Poly(G.as_expr(), T), modulus=2)[1]
    print("  g_p mod 2 factor degrees/multiplicities:", [(Poly(h.as_expr(),T).degree(), e) for h, e in gf],
          " => dyadic types (e,f) = (1,1),(2,%d),(2,%d)" % ((p-1)//4, (p-1)//4))
    G4 = G.eval(4); H = G4//2; u4 = int(U.eval(4))
    print("  g_p(4) =", G4, " H_p = g_p(4)/2 =", H, "=", factorint(H))
    print("  U_p(4) =", u4)
    print("  Table A1 (ell, v, Legendre(4U_p(4)/ell)):",
          [(l, e, legendre_symbol(4*u4, l)) for l, e in factorint(H).items()])
    print("  J(U_p(4),H_p) =", int(J(u4, H)))
    phi = Poly(T**4+T+1, T) if p == 17 else Poly(T**10+T**8+T**7+T**4+T**3+T+1, T)
    psi = Poly(T**4+T**3+T**2+T+1, T) if p == 17 else Poly(T**10+T**9+T**4+T+1, T)
    ok3 = Poly(G.as_expr(), T, modulus=2) == Poly((T*phi.as_expr()**2*psi.as_expr()**2), T, modulus=2)
    print("  (A.3) g_p = T*phi^2*psi^2 mod 2:", ok3, "; phi,psi irreducible distinct mod 2:",
          Poly(phi.as_expr(),T,modulus=2).is_irreducible and Poly(psi.as_expr(),T,modulus=2).is_irreducible)
    H2 = Poly((G.as_expr() - T*phi.as_expr()**2*psi.as_expr()**2)/2, T)
    print("  (A.2) remainder of H_{p,2} mod phi*psi:", Poly(H2.as_expr(),T,modulus=2).rem(Poly(phi.as_expr()*psi.as_expr(),T,modulus=2)))
    print("  (A.5) g_p(2)/p mod p =", (G.eval(2)//p) % p)
    print()
