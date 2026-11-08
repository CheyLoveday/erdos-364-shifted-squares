from math import isqrt
from dickson import F

def sols(p,Amax):
    out=[]
    for A in range(0,Amax+1):
        v=F(p,A)-1
        if v<0: continue
        r=isqrt(v)
        if r*r==v: out.append(A)
    return out

if __name__=="__main__":
    for p in (3,5,7,11,13,17,19,41):
        s=sols(p,200000)
        print("p=",p,"A in [0,200000] with F_p(A)-1 square:",s)
