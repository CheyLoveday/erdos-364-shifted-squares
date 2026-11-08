import cmath
from dickson import Dpoly, Dval, F
# identity: F_p(A) = A * prod_{j odd mod 2p} (2A - (zeta^j - zeta^-j))  with zeta = exp(2 pi i/(2p))
for p in (3,5,7,17,41):
    z=cmath.exp(2j*cmath.pi/(2*p))
    for A in (2,6,10,14):
        prod=1+0j
        for j in range(1,2*p,2):
            c=z**j - z**(-j)
            prod*= (2*A - c)
        val=A*prod
        print(f"p={p:3d} A={A:3d}  A*prod={val.real:18.6f}{val.imag:+.1e}   F_p(A)={F(p,A)}")
