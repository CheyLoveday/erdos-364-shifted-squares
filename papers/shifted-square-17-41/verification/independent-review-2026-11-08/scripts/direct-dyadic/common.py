import sys
sys.path.insert(0,'work')
from defs import *
from sympy import factorint, jacobi_symbol as J, Poly, symbols, prod

def dedekind_ok(G, ell):
    """Dedekind index criterion: True iff ell does not divide [O_L : Z[theta]]."""
    Gx = Poly(G.as_expr(), T)
    fl = factor_list(Gx, modulus=ell)
    facs = fl[1]
    if not facs: return True
    prod_poly = Poly(1, T)
    for h, e in facs:
        prod_poly = prod_poly * Poly(h, T)**e
    diff = Poly(Gx.as_expr() - prod_poly.as_expr(), T)
    q = Poly(diff.as_expr()/ell, T, modulus=ell)
    ok = True
    for h, e in facs:
        if e == 1: continue
        hbar = Poly(h, T, modulus=ell)
        if q.rem(hbar).is_zero:
            ok = False
    return ok

def jac(a,b):
    return int(J(int(a), int(b)))
