from sympy import factorint, legendre_symbol
from dickson import F

def is4thpow(v,l):
    v%=l
    if v==0: return True
    if l%4!=1: return False
    return pow(v,(l-1)//4,l)==1

def check_conditions(p,A):
    Kp1=F(p,1)-1          # F_p(1)-1
    Kpm1=-F(p,1)-1        # F_p(-1)-1  (F_p(-T) = -F_p(T))
    c1=all(is4thpow(-2*A,l) for l in factorint(A*A+1))
    c2=(A%p==1) or legendre_symbol((A-1)%p,p)==1
    c3=True
    for l in factorint(abs(A-1)):
        if l==2: continue
        if Kp1%l!=0 and legendre_symbol(Kp1%l,l)!=1: c3=False;break
    c4=True
    for l in factorint(abs(A+1)):
        if l==2: continue
        if Kpm1%l!=0 and legendre_symbol(Kpm1%l,l)!=1: c4=False;break
    return c1 and c2 and c3 and c4,(c1,c2,c3,c4)

for p in (17,41):
    good=[];counts=[0,0,0,0]
    for A in range(2,80001,8):
        ok,det=check_conditions(p,A)
        for i,d in enumerate(det):
            if d: counts[i]+=1
        if ok: good.append(A)
    print("p=",p,"A=8k+2 in [2,80000]: per-condition counts",counts,"all four:",len(good),good[:10])
