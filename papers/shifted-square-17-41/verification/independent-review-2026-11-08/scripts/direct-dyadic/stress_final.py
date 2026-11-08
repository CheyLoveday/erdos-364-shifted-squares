import sys; sys.path.insert(0,'work')
from defs import *
from sympy import Poly, jacobi_symbol as J
import math
def run(p,K,phase):
    PU = Poly((U17() if p==17 else U41()).as_expr(), T); PF = Poly(F(p), A)
    res = { -1:0, 1:0, 0:0 }; gcf = 0
    for k in range(K):
        A0 = phase(k); Q = int(PF.eval(A0))-1; u = int(PU.eval(2*A0))
        g = math.gcd(abs(u),Q)
        if g != 1: gcf += 1; res[0]+=1; continue
        res[int(J(u,Q))] += 1
    return res, gcf
for p,K in ((17,5000),(41,500)):
    print('p=',p,'A=8k+2,k<',K,':', run(p,K,lambda k:8*k+2))
for p,K in ((17,5000),(41,500)):
    print('p=',p,'A=8k+6,k<',K,':', run(p,K,lambda k:8*k+6))
