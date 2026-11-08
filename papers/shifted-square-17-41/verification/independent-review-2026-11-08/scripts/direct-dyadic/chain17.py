"""Arithmetic audit of the Lean pseudo-remainder chain R0..R14 used in
Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean.
Run from .ultramath/smw70l62n/m3:  python3 work/chain17.py
It (i) extracts the 14 polynomials from the Lean source, (ii) verifies the 14
polynomial identities and the identifications R0 = F_17(A)-1, R1 = U_17(2A),
(iii) prints the consecutive resultants, (iv) exhibits a specialised common
factor inside the hard phase A = 2 mod 8."""
import re, math, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from defs import *
from sympy import Poly, expand, factorint, resultant

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LEAN = os.path.join(REPO, 'Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean')
src = open(LEAN).read()
defs = {}
for m in re.finditer(r'private def (outer17R\d+) \(A : Int\) : Int :=\s*(.*?)\n\n', src, re.S):
    defs[m.group(1)] = ' '.join(m.group(2).split()).replace('^', '**')
R = {k: eval(defs[f'outer17R{k}'], {'A': A}) for k in range(15)}
P = {k: Poly(v, A) for k, v in R.items()}

identities = [
    R[0] - ((4*A**3 + 5*A)*R[1] + R[2]),
    3*R[1] - (2*A*R[2] - R[3]),
    R[2] - (4*A*R[3] + R[4]),
    R[3] - ((6*A + 6)*R[4] + R[5]),
    242*R[4] - ((22*A - 21)*R[5] + R[6]),
    R[5] - ((22*A - 507)*R[6] + 726*R[7]),
    4225*R[6] - ((260*A + 6048)*R[7] - R[8]),
    98*R[7] - ((455*A + 401)*R[8] + 4225*R[9]),
    2*R[8] - ((28*A + 3)*R[9] + 49*R[10]),
    4*R[9] - ((8*A - 9)*R[10] - R[11]),
    25*R[10] - ((40*A - 13)*R[11] + 8*R[12]),
    961*R[11] - ((155*A + 26)*R[12] - 25*R[13]),
    5476*R[12] - ((4588*A - 131)*R[13] + 961*R[14]),
    25*R[13] - ((740*A + 267)*R[14] + 5476),
]
print("all 14 polynomial identities of outer17_pseudo_remainders hold:",
      all(expand(e) == 0 for e in identities))
print("R0 = F_17(A)-1 :", Poly(R[0], A) == Poly(F(17), A) - 1)
print("R1 = U_17(2A)  :", Poly(R[1], A) == Poly(U17().as_expr().subs(T, 2*A), A))
print("\nconsecutive resultants:")
for i in range(14):
    print(f"  Res(R{i},R{i+1}) =", factorint(resultant(R[i], R[i+1], A)))
print("\nspecialised common factors inside the hard phase A = 2 mod 8:")
for A0 in (2, 10, 18, 26, 34, 42):
    g = math.gcd(abs(int(P[2].eval(A0))), abs(int(P[3].eval(A0))))
    print(f"  A={A0:3d} (A mod 8 = {A0 % 8}): R2 mod 3 = {int(P[2].eval(A0)) % 3},"
          f" R3 mod 3 = {int(P[3].eval(A0)) % 3}, gcd(R2,R3) = {g}")
