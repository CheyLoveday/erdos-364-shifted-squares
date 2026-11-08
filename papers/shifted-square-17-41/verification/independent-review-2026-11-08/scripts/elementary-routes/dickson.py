from math import isqrt

def Dpoly(p):
    # coefficients list, index = power; D_0=2, D_1=T, D_{n+2}=T D_{n+1}+D_n
    D0=[2]; D1=[0,1]
    if p==0: return D0
    if p==1: return D1
    a,b=D0,D1
    for n in range(2,p+1):
        c=[0]*(len(b)+1)
        for i,co in enumerate(b): c[i+1]+=co
        if len(c)<len(a): c=c+[0]*(len(a)-len(c))
        for i,co in enumerate(a):
            if i>=len(c): c=c+[0]*(i+1-len(c))
            c[i]+=co
        a,b=b,c
    return b

def Dval(coeffs,x):
    s=0
    for co in reversed(coeffs): s=s*x+co
    return s

def F(p,A):
    # F_0=1,F_1=A
    a,b=1,A
    if p==0: return a
    if p==1: return b
    for _ in range(2,p+1):
        a,b=b,2*A*b+a
    return b

if __name__=="__main__":
    for p in (5,13,17,41):
        c=Dpoly(p)
        print(p, c[-1]==1, len(c)-1==p, [Dval(c,0),Dval(c,2),Dval(c,4)])
    # verify g_p/2 = F_p(A) - 1 at x=2A
    for p in (5,13,17,41):
        c=Dpoly(p)
        ok=all((Dval(c,2*A)-2)//2 == F(p,A)-1 for A in range(0,8))
        print("g/2 == F_p(A)-1:",p,ok)
