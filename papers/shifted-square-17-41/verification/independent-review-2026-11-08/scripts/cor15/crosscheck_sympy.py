"""Cross-check of the hand-rolled audit against SymPy (a second, independent
implementation).  Only a small number of instances: the point is provenance,
not coverage.

Run: python3 audit/crosscheck_sympy.py
"""
import sys
from math import gcd

import sympy as sp
from sympy.ntheory.continued_fraction import continued_fraction_periodic

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from cor15_audit import pell_solutions, is_squarefree   # noqa: E402


def cf_period_sympy(D):
    cf = continued_fraction_periodic(0, 1, D)
    return cf[0], list(cf[1])


def fund_sympy(D):
    """Fundamental minus and plus solutions, recomputed from SymPy's period."""
    a0, period = cf_period_sympy(D)
    minus = plus = None
    pm2, pm1, qm2, qm1 = 0, 1, 1, 0
    for a in [a0] + period:
        p = a * pm1 + pm2
        q = a * qm1 + qm2
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q
        if minus is None and p * p - D * q * q == -1:
            minus = (p, q)
        if plus is None and p * p - D * q * q == 1:
            plus = (p, q)
    return minus, plus


def main():
    print(f"SymPy {sp.__version__}")
    cases = [5, 2, 13, 17, 37, 41, 50, 82, 109, 149, 373, 1009, 17341]
    for D in cases:
        a0, period = cf_period_sympy(D)
        mine_neg, mine_pos, L = pell_solutions(D)
        sneg, spos = fund_sympy(D)
        assert (mine_neg is None) == (sneg is None), D
        if mine_neg is not None:
            assert tuple(mine_neg) == tuple(sneg), (D, mine_neg, sneg)
        assert all(e == 1 for e in sp.factorint(D).values()) == is_squarefree(D), D
        print(f"  D={D:6d}: period {period} (len {L}), fundamental minus "
              f"{(mine_neg, sneg)} agree")

    # Walker's own example, and the paper's family identity.
    K = 5
    eps = (2, 1)                       # 2 + sqrt 5, fundamental for -1
    a, b = 1, 0
    for _ in range(5):
        a, b = a * eps[0] + b * eps[1] * K, a * eps[1] + b * eps[0]
    print(f"  (2+sqrt5)^5 = {a} + {b} sqrt5;  sympy factor of a^2+1:",
          sp.factorint(a * a + 1))
    assert (a, b) == (682, 305)
    assert a * a + 1 == K ** 3 * 61 ** 2
    print(f"  682^2+1 = 5^3 * 61^2 = {sp.Integer(5)**3*61**2}")

    # Instance of the scope data point: K = 5, N = 85 (17 | N), X = 2 mod 8.
    a, b = 1, 0
    for _ in range(85):
        a, b = a * eps[0] + b * eps[1] * K, a * eps[1] + b * eps[0]
    assert a * a + 1 == K ** 3 * (b // K) ** 2
    assert a % 8 == 2 and gcd(85, 17) == 17
    print(f"  K=5, N=85: X = {a}  ({len(str(a))} digits),  X mod 8 = {a % 8},")
    print(f"     X^2+1 = 5^3 * (b/5)^2 with b/5 having {len(str(b // 5))} "
          f"digits; 17 | N.  SymPy check X^2+1 = 5^3 V^2:",
          a * a + 1 == 5 ** 3 * (b // 5) ** 2)
    print("CROSSCHECK_OK")


if __name__ == "__main__":
    main()
