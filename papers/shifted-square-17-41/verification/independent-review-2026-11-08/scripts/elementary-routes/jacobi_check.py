from math import isqrt, gcd
from sympy import jacobi_symbol, isprime
from dickson import Dpoly, Dval, F

C17=[-1,0,-1,1,1,-1,0,0,0,0,0,0,-2,0,1]
C41=[-1,-15,2,4,8,7,-8,-10,-3,6,7,3,-1,-9,3,7,2,3,-9,-6,1,8,4,1,-4,-6,3,7,0,2,-7,-4,1,6,-1,0,-2,-5,4,5,-5]

def Uval(p,x):
    c=C17 if p==17 else C41
    d=[2,x]
    for _ in range(2,p+1): d.append(x*d[-1]+d[-2])
    s=c[0]
    for k in range(1,len(c)): s+=c[k]*d[k]
    return s

for p in (17,41):
    bad=[];n=0;gcd_bad=[]
    for A in range(2,4001,8):
        Q=F(p,A)-1
        num=Uval(p,2*A)
        if gcd(num,Q)!=1: gcd_bad.append(A);continue
        j=jacobi_symbol(num,Q)
        n+=1
        if j!=-1: bad.append((A,j))
    print("p=",p,"A=8k+2<=4000: tested",n,"violations of J(U_p(2A),F_p(A)-1)=-1:",bad[:5],
          "gcd failures:",gcd_bad[:5])
