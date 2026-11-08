from math import isqrt, gcd
from sympy import symbols, Poly, expand, rem, ZZ, primitive
from dickson import Dpoly, Dval, F

def primes_upto(n):
    sieve=bytearray([1])*(n+1); sieve[0:2]=b'\x00\x00'
    for i in range(2,isqrt(n)+1):
        if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
    return [i for i in range(n+1) if sieve[i]]

A = symbols('A')
def Fpoly(p):
    a=Poly(1,A); b=Poly(A,A)
    if p==0: return a
    if p==1: return b
    for _ in range(2,p+1):
        a,b = b, Poly(2*A,A)*b + a
    return b

print("=== (1) exact polynomial identities: F_p(A) = A*W_p(A^2); F_p mod (A^2+1) ===")
for p in (17,41):
    Fp=Fpoly(p)
    # extract odd part: Fp(A) = A * G(A^2)
    coeffs=Fp.all_coeffs()[::-1]  # index=power
    oddpart=[coeffs[i] for i in range(len(coeffs)) if i%2==1]
    evenpart=[coeffs[i] for i in range(len(coeffs)) if i%2==0]
    W=[oddpart[i] for i in range(len(oddpart))]  # G(y)=sum oddpart[i]*y^i with y=A^2
    # verify Fp(A) == A * sum oddpart[i]*A^(2i)
    G=sum(c*A**(2*i) for i,c in enumerate(W))
    assert expand(Fp.as_expr()-A*G)==0
    print(" p=",p,"even coefficients all zero:",all(c==0 for c in evenpart),
          " G(-1)=",sum(c*(-1)**i for i,c in enumerate(W)))
    # F_p(A) mod (A^2+1)
    r=rem(Poly(Fp.as_expr(),A), Poly(A**2+1,A))
    print("   F_p(A) mod (A^2+1) =",r.as_expr())

print()
print("=== (2) mod-p congruence: F_p(A)-1 = (A-1)^p mod p ===")
for p in (17,41):
    Fp=Fpoly(p)
    for Av in (2,6,10,42,882,1234):
        lhs=(int(Fp.eval(Av))-1) % p
        rhs=pow((Av-1)%p,p,p)
        assert lhs==rhs,(p,Av,lhs,rhs)
    print(" p=",p,"checked: F_p(A)-1 == (A-1)^p (mod p) for sample A")

print()
print("=== (3) per-prime existence of a 'passing' residue; no single-prime covering ===")
B=5000
P=primes_upto(B)
for p in (5,13,17,41):
    c=Dpoly(p)
    worst=None; nopoint=[]
    for l in P:
        if l==2: continue
        inv2=pow(2,-1,l)
        good=0
        for x in range(l):
            v=(Dval(c,x)-2)*inv2 % l
            if v==0 or pow(v,(l-1)//2,l)==1: good+=1
        if good==0: nopoint.append(l)
        frac=good/l
        if worst is None or frac<worst[1]: worst=(l,frac,good)
    print(f" p={p}: primes<= {B} with NO passing residue: {nopoint}; "
          f"min density of passing residues = {worst[2]}/{worst[0]} = {worst[1]:.3f}")

print()
print("=== (4) explicit CRT witness: x=4 mod 16 with f(x) a square mod M ===")
from functools import reduce
def crt(res, mods):
    from sympy.ntheory.modular import crt as s_crt
    m,r=mods,[x[0] for x in res]
    sol=s_crt(m,r)[0]
    return int(sol)
for p in (17,41):
    c=Dpoly(p); inv2cache={}
    S=[3,5,7,11,13]
    for extra in range(0,6):
        pass
    mods=[16]+S
    # choose passing residue for each odd prime
    residues=[[4,16]]
    chosen=[]
    for l in S:
        inv2=pow(2,-1,l)
        pick=None
        for x in range(1,l):
            v=(Dval(c,x)-2)*inv2 % l
            if v!=0 and pow(v,(l-1)//2,l)==1: pick=x;break
        chosen.append((l,pick))
        residues.append([pick,l])
    x=crt(residues,mods)
    f=lambda t:(Dval(c,t)-2)//2
    ok=all((f(x) % l in [0] or pow(f(x)%l,(l-1)//2,l)==1) for l in S)
    print(f" p={p}: S={S}, passing residues {chosen}, CRT x={x}, x mod 16={x%16}, "
          f"f(x) square mod every l in S: {ok}")
    # find the least odd prime witness for this x
    w=None
    for l in primes_upto(20000):
        if l==2: continue
        v=f(x)%l
        if v!=0 and pow(v,(l-1)//2,l)==l-1: w=l;break
    print(f"        least odd prime witness for this x: {w}")
