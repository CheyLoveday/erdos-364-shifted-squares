"""Exact checks for route_scope.md, Propositions 3.1 and 4.1.

Prop. 3.1:  Res(Phi_{2p}(T), T^2 - 2AT - 1) = V_p(4A^2),  where D_p(x) = x*V_p(x^2)
            and F_p(A) = A*V_p(4A^2);  i.e. F_p(A) = A*N_{Q(zeta_2p)/Q}(2A - zeta + zeta^-1).
Prop. 4.1:  w_p(A) = coefficient of sqrt(A^2+1) in (A + sqrt(A^2+1))^p satisfies
            w_p(A) = p (mod A^2+1) for p = 1 (mod 4).

Run: python3 route_scope_checks.py     (prints ROUTE_SCOPE_CHECKS_OK)
"""
import sympy as sp
from dickson import Dpoly, Dval, F

T, A = sp.Symbol('T'), sp.Symbol('A')

def V_of_p(p):
    """V_p with D_p(x) = x*V_p(x^2), as a Polynomial in A."""
    c = Dpoly(p)
    return sum(c[i] * A**((i - 1)//2) for i in range(1, len(c), 2))

def Fpoly(p):
    a, b = sp.Poly(1, A), sp.Poly(A, A)
    for _ in range(2, p + 1): a, b = b, sp.Poly(2*A, A)*b + a
    return b

print("[Prop 3.1] resultant identity over the 2p-th cyclotomic field")
for p in (3, 5, 7, 17, 41):
    phi = sp.cyclotomic_poly(2*p, T)
    res = sp.expand(sp.resultant(phi, T**2 - 2*A*T - 1, T))
    V = sp.expand(V_of_p(p).subs(A, 4*A**2))
    assert sp.simplify(res - V) == 0, f"resultant identity fails at p={p}"
    # and F_p(A) = A * V_p(4A^2)
    assert sp.expand(A*V - Fpoly(p).as_expr()) == 0, f"F_p mismatch at p={p}"
    print("   p=%2d: Res(Phi_2p, T^2-2AT-1) = V_p(4A^2) and F_p = A*V_p(4A^2)  ok" % p)

print("[Prop 4.1] w_p(A) = p (mod A^2+1)")
def w(p, a):
    """(F_p, w_p) with (A+sqrt(A^2+1))^p = F_p + w_p*sqrt(A^2+1)."""
    f, g = 1, 0
    for _ in range(p):
        f, g = a*f + (a*a + 1)*g, f + a*g
    return f, g
for p in (5, 13, 17, 41):
    for a in (2, 6, 10, 14, 42, 882, 1234, 8*10**5 + 2):
        f, g = w(p, a)
        assert f == F(p, a), "F_p via ring power"
        assert (g - p) % (a*a + 1) == 0, f"w_p mod K fails at p={p}, A={a}"
    print("   p=%2d: w_p = %d (mod A^2+1) for all tested A, and F_p^2-(A^2+1)w_p^2=-1" % (p,p))
    for a in (2, 6, 42):
        f, g = w(p, a)
        assert f*f - (a*a+1)*g*g == -1, "norm equation"
print("ROUTE_SCOPE_CHECKS_OK")
