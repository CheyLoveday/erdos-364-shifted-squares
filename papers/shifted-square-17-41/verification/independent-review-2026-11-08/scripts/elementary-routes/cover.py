from math import isqrt
from dickson import Dpoly, Dval, F

def primes_upto(n):
    sieve=bytearray([1])*(n+1); sieve[0:2]=b'\x00\x00'
    for i in range(2,isqrt(n)+1):
        if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
    return [i for i in range(n+1) if sieve[i]]

def nonpoint_primes(p,B):
    c=Dpoly(p); bad=[]
    for l in primes_upto(B):
        if l==2: continue
        inv2=pow(2,-1,l)
        hit=False
        for x in range(l):
            v=(Dval(c,x)-2)*inv2 % l
            if v==0: hit=True;break
            if pow(v,(l-1)//2,l)==1: hit=True;break
        if not hit: bad.append(l)
    return bad

def squares_solutions(p,Amax):
    sols=[]
    for A in range(0,Amax+1):
        v=F(p,A)-1
        if v>=0:
            r=isqrt(v)
            if r*r==v: sols.append((A,))
    return sols

if __name__=="__main__":
    for p in (5,13,17,41):
        print("p",p,"primes with NO point on y^2=(D_p(x)-2)/2, l<=3000:", nonpoint_primes(p,3000))
