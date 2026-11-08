from sympy import Poly, Symbol, I, expand
from dickson import Dpoly, Dval, F
T=Symbol('T')
print("D_p(T) == T^p mod p, D_p(x)/x at x=2i equals i^(p-1):")
for p in (3,5,7,11,13,17,19,41):
    c=Dpoly(p)
    diff=[co % p for co in c]
    tgt=[0]*p+[1]
    ok1 = all((diff[i]-(tgt[i] if i<len(tgt) else 0))%p==0 for i in range(max(len(diff),len(tgt))))
    # V_p(-4) = D_p(2i)/(2i)
    # evaluate D_p at x=2i exactly: use complex ints
    z=2*I; val=sum(co*z**i for i,co in enumerate(c))
    V=expand(val/z)
    ok2 = (V - I**(p-1))==0
    ok3 = all((F(p,A) - A*(sum(co*(4*A*A)**i for i,co in enumerate(c[1::2]) if False)) )==0 or True for A in [0])
    print(f"  p={p:3d}  D_p == T^p mod p: {ok1}   V_p(-4) = i^(p-1): {ok2}  (V_p(-4)={V})")
# also confirm p=3,7,11 give -A mod (A^2+1)
A=Symbol('A')
for p in (3,5,7,11,13,17,41):
    c=Dpoly(p)
    # F_p(A) = A * V_p(4A^2), V_p coefficients from odd part of D_p
    V=[c[i] for i in range(1,len(c),2)]
    Fp=expand(A*sum(v*(4*A*A)**j for j,v in enumerate(V)))
    r=expand(Fp - A*sum(v*(-4)**j for j,v in enumerate(V)))
    # reduce mod A^2+1:  F_p(A) mod (A^2+1) = A * V_p(-4)
    from sympy import rem, Poly
    rr=rem(Poly(Fp,A),Poly(A*A+1,A)).as_expr()
    print(f"  p={p:3d}  F_p(A) mod (A^2+1) = {rr}   (expect {'A' if p%4==1 else '-A'})")
