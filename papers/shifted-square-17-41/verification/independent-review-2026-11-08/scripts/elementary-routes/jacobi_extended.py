"""Extended stress test of the paper's Proposition 7.1:
   J(U_p(2A), F_p(A)-1) = -1 and gcd = 1 for all A = 8k+2 up to 20000,
   plus random large A = 2 (mod 8)."""
import random
from math import gcd
from sympy import jacobi_symbol
from dickson import F
U = {17: [-1,0,-1,1,1,-1,0,0,0,0,0,0,-2,0,1],
     41: [-1,-15,2,4,8,7,-8,-10,-3,6,7,3,-1,-9,3,7,2,3,-9,-6,1,8,4,1,-4,-6,3,7,0,2,-7,-4,1,6,-1,0,-2,-5,4,5,-5]}
def Uval(p, x):
    d=[2,x]
    for _ in range(2,p+1): d.append(x*d[-1]+d[-2])
    return U[p][0] + sum(U[p][k]*d[k] for k in range(1,len(U[p])))
random.seed(7)
for p in (17,41):
    n=0
    for A in range(2,20001,8):
        num=Uval(p,2*A); Q=F(p,A)-1
        assert gcd(num,Q)==1, ("gcd",p,A)
        assert jacobi_symbol(num,Q)==-1, ("jacobi",p,A)
        n+=1
    print(f"p={p}: {n} values A=8k+2 <= 20000 ok")
    big=[8*random.randrange(10**5,10**7)+2 for _ in range(8)]+[2+8*10**9, 2+8*10**12]
    for A in big:
        num=Uval(p,2*A); Q=F(p,A)-1
        assert gcd(num,Q)==1, ("gcd big",p,A)
        j=jacobi_symbol(num,Q)
        assert j==-1, ("jacobi big",p,A,j)
    print(f"p={p}: random large A ok: {big}")
print("JACOBI_EXTENDED_OK")
