"""Independent verification of the Dickson composition law cited as [16].

Definition used (Lidl-Mullen-Turnwald convention): D_0 = 2, D_1 = T,
D_{n+2} = T D_{n+1} - a D_n.  Claim: D_m(D_n(T,a), a^n) = D_{mn}(T,a).

The paper's polynomial (2.1) is the case a = -1, and its Lemma 5.1 (F_{mn}(A) =
F_m(F_n(A)) for n odd) is D_m(D_n(T,-1), -1) = D_{mn}(T,-1) with a^n = -1 for odd n.

Verified here as exact polynomial identities for a in {-1,2,3,5} and m,n <= 8.
Note: the monograph [16] was not consulted (not available online); this checks the
*statement* the paper uses, not the book's numbering.
"""
import sympy as sp

T = sp.Symbol("T")


def dickson(n, a):
    if n == 0:
        return sp.Integer(2)
    prev, cur = sp.Integer(2), T
    for _ in range(n - 1):
        prev, cur = cur, sp.expand(T * cur - a * prev)
    return cur


if __name__ == "__main__":
    bad = []
    for a in (-1, 2, 3, 5):
        for m in range(1, 9):
            for n in range(1, 9):
                lhs = sp.expand(dickson(m, a).subs(T, dickson(n, a)) * 0
                                + _lhs) if False else None
                # substitute T -> D_n in D_m, then replace the parameter a^n
                dm = dickson(m, sp.Symbol("a"))
                inner = dickson(n, a)
                lhs = sp.expand(dm.subs(sp.Symbol("a"), a ** n).subs(T, inner))
                rhs = dickson(m * n, a)
                if sp.expand(lhs - rhs) != 0:
                    bad.append((a, m, n))
    print("Dickson composition D_m(D_n(T,a),a^n)=D_mn(T,a): mismatches", bad)
    # the paper's specialisation: a = -1, n odd  =>  F_mn(A) = F_m(F_n(A))
    A = sp.Symbol("A")
    F = lambda k: sp.expand(dickson(k, -1).subs(T, 2 * A) / 2)
    print("F_3(F_5(A)) == F_15(A):", sp.expand(F(3).subs(A, F(5)) - F(15)) == 0)
    print("F_2(F_2(A)) == F_4(A)?", sp.expand(F(2).subs(A, F(2)) - F(4)) == 0,
          "(n even: guard fails, as the paper says)")
