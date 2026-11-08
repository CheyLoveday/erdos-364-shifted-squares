# Scope of the elementary routes to the fixed indices $p=17,41$

Swarm `smw70l62n`, member m7, direction d5. **Revised after review**: everything in
this file is either a theorem with an explicit statement, or a *route diagnosis*
(marked as such) — a statement about what a particular mechanism computes, not an
impossibility claim about all proofs of that family.

Notation: $F_n$ as in the paper, $D_n$ the Dickson polynomials with
$D_n(2A)=2F_n(A)$, $Q_p(A)=F_p(A)-1=g_p(2A)/2$, and $A\equiv 2\pmod 8$ (the hard phase
of Theorem 4.2), $p\in\{17,41\}$. "(W1) witness" at $A$ means a prime $\ell$ at which
$Q_p(A)$ is not a square in $\mathbb Q_\ell$ (see `theorem_no_finite_modulus.md` §0.1).

---

## 1. What the impossibility result covers — and what it does not [proof]

**Proved** (`theorem_no_finite_modulus.md`, Theorem 1 and Corollary 2): for every
finite set $S$ of odd primes, every choice of $\alpha\ge1$ and exponents $e_\ell\ge1$
there are infinitely many $A\equiv2\pmod 8$ with $Q_p(A)$ a quadratic residue modulo
$2^{\alpha}\prod_{\ell\in S}\ell^{e_\ell}$; in particular $Q_p(A)$ is a square in
$\mathbb Q_2$ and in $\mathbb Q_\ell$ for every $\ell\in S$ (and positive, hence a
square at the real place).

**Equivalent formulation.** No proof of the following shape can work: "for each
$A\equiv2\pmod8$, test $Q_p(A)$ modulo a *fixed* finite set of primes and reject $A$
when one of them is a (W1) witness". In particular: no fixed-modulus covering
congruence certificate exists. And if a proof of Theorem 4.2 proceeds by producing
(W1) witnesses, they cannot be confined to any fixed finite set of primes.

**Not asserted.** (i) Nothing here says that the manuscript's argument is
"non-elementary" or that no elementary proof exists: the manuscript's Jacobi argument
*is* elementary arithmetic (quadratic reciprocity and explicit integer certificates),
its data are simply $A$-dependent — numerator $U_p(2A)$, denominator $Q_p(A)$. (ii)
Nothing here constrains global arguments — height bounds, integral points on
$y^2=Q_p(A)$, Thue/hyperelliptic methods, linear forms in logarithms — which need not
exhibit local witnesses at all. (iii) Nothing here constrains (W2) witnesses
(prime divisor of odd valuation plus detector character); Proposition 7.1 of the
manuscript supplies those uniformly, and Theorem 1 only says the primes occurring
cannot be confined to a finite set.

---

## 2. Pell / continued fraction / Euclidean descent: route diagnosis, not a theorem

What the Pell structure of $\mathbb Q(\sqrt{A^2+1})$ supplies is norm and valuation
parity data. With $\alpha=A+\sqrt{A^2+1}$ of norm $-1$,
$$F_p(A)^2-(A^2+1)w_p(A)^2=-1,\qquad
F_p(A)=y^2+1\ \Longrightarrow\ (y^2+1)^2+1=(A^2+1)\,w_p(A)^2 .$$
Every element that this structure produces has norm equal, up to the fixed unit $-1$,
to a square times $A^2+1$; and squares have even valuations at every prime. So the
valuation data obtained from the fundamental unit are *necessarily consistent* with
the hypothetical solution, which is exactly why §3.3 of the manuscript, which
extracts this parity information in its degree-$p$ field, obtains no contradiction
from it and must pass to a local symbol computation.

**Diagnosis.** A proof built on this structure would need an additional input of
character (quadratic-residue) type; I did not find one, and the cheap $A$-dependent
congruences I could derive are weak (§5). This is a statement about what the
continued-fraction arithmetic of $\sqrt{A^2+1}$ makes visible, not a theorem that no
Pell-type argument can succeed.

---

## 3. Resultant / cyclotomic route: one new exact identity; still not enough

**Proposition 3.1.** Let $p$ be odd and $c=\zeta_{2p}-\zeta_{2p}^{-1}$ for a primitive
$2p$-th root of unity $\zeta_{2p}$. Then the algebraic norm of $2A-c$ from
$K_p:=\mathbb Q(\zeta_{2p})$ to $\mathbb Q$ equals $V_p(4A^2)=F_p(A)/A$, i.e.
$$F_p(A)\;=\;A\;N_{K_p/\mathbb Q}\bigl(2A-\zeta_{2p}+\zeta_{2p}^{-1}\bigr). \tag{3.1}$$
Equivalently, $\operatorname{Res}(\Phi_{2p}(T),\,T^2-2AT-1)=V_p(4A^2)$.

*Proof.* The Galois conjugates of $c$ are $c_j=\zeta_{2p}^j-\zeta_{2p}^{-j}$ for $j$ odd,
$1\le j<2p$; the Galois group is $(\mathbb Z/2p)^\times$, of order $\varphi(2p)=p-1$,
and $j\equiv p$ is the only odd residue $<2p$ that is not a unit mod $2p$. For odd
$j\ne p$ the numbers $4A^2-c_j^2$ pair up under $j\mapsto 2p-j$ (since
$c_{2p-j}=-c_j$), and $c_j^2=\zeta_{2p}^{2j}-2+\zeta_{2p}^{-2j}$, where $2j$ runs over
the units modulo $p$ up to sign. So $4A^2-c_j^2=4A^2+2-\zeta_p^k-\zeta_p^{-k}$ with
$k=1,\dots,m$ running over the $m=(p-1)/2$ conjugates of $\zeta_p+\zeta_p^{-1}$, and
$$\prod_{j\ne p}\bigl(2A-c_j\bigr)=\prod_{k=1}^{m}\bigl(4A^2+2-\zeta_p^k-\zeta_p^{-k}\bigr)=V_p(4A^2),$$
the last step being the classical factorization
$\sinh(pu)/\sinh(u)=\prod_{k=1}^{m}\bigl(4\sinh^2u+4\sin^2(\pi k/p)\bigr)$ together with
$4\sin^2(\pi k/p)=2-\zeta_p^k-\zeta_p^{-k}$ and $4\sinh^2u=4A^2$. This product over
$j\ne p$ is exactly $N_{K_p/\mathbb Q}(2A-c)$. (Including the excluded term $j=p$,
where $c_p=\zeta_{2p}^p-\zeta_{2p}^{-p}=-1+1=0$, multiplies by $2A$, giving
$\prod_{j\ \mathrm{odd}}(2A-c_j)=2A\,V_p(4A^2)=2F_p(A)$.) $\square$ **[proof]**, and
the resultant identity is confirmed exactly for $p=3,5,7,17,41$ **[cert]**
(`route_scope_checks.py`).

**Why this identity alone does not close the problem** (a statement about this
identity, not about all cyclotomic arguments). The mechanism of the manuscript's
§3.3 needs an element whose norm is *exactly* $Q_p(A)$: a hypothetical solution then
produces an element of square norm, hence even valuations everywhere, and the local
symbols conflict. In the cyclotomic model (3.1) the exact norm identity is for $F_p$,
not for $Q_p$: the shifted value is $Q_p=A\,N(\cdot)-1$, and "$-1$" is invisible to
ideal valuations. So this identity supplies no support control for $Q_p$.

**Where a cyclotomic proof would have to live** (structural observation). The roots of
$D_p(T)=2$ are $\theta_k=\eta\zeta_p^k-\eta^{-1}\zeta_p^{-k}$ with $\eta^p=1+\sqrt2$
(real $p$-th root), because $2\sinh(pu)=2$ has $e^{pu}=\zeta_p^k(1+\sqrt2)$; hence
$$\mathbb Q(\theta_p)\;\subseteq\;K_p':=\mathbb Q\bigl(\zeta_p,\ (1+\sqrt2)^{1/p}\bigr),$$
a Kummer extension of $\mathbb Q(\zeta_p)$ by the unit $1+\sqrt2$. Carrying out a
proof there requires the $S$-arithmetic of $K_p'$ (unit group and class group at the
primes above $2$ and above $1+\sqrt2$); I did not attempt it and make no claim about
its length or feasibility. Note that (3.1) and the manuscript's
$N_{L_p/\mathbb Q}(x-\theta_p)=g_p(x)$ are different identities: different fields
($p-1$ versus $p$), different elements.

---

## 4. Lucas rank of apparition: exact statement, and why it is unavailable here [proof]

Walker's property-Q rank (manuscript Corollary 1.5, §6.3) controls *indices* at which
a coefficient is divisible by $K$. In the recurrence family at index $p$,
$$\alpha^p=F_p(A)+w_p(A)\sqrt{K},\qquad K=A^2+1,\qquad
F_p(A)^2-K\,w_p(A)^2=-1 .$$

**Proposition 4.1.** For every integer $A$ and every prime $p\equiv1\pmod 4$,
$$w_p(A)\;\equiv\;p \pmod{A^{2}+1}. \tag{4.1}$$

*Proof.* Expand $(A+\sqrt K)^p$ binomially; the coefficient of $\sqrt K$ is
$w_p=\sum_{j}\binom{p}{2j+1}A^{p-2j-1}K^{j}$. Modulo $K$ only $j=0$ survives:
$w_p\equiv pA^{p-1}=p(A^2)^{(p-1)/2}\equiv p(-1)^{(p-1)/2}=p\pmod K$. $\square$
**[proof]**, confirmed numerically (`route_scope_checks.py`).

**Corollary 4.2.** $K\mid w_p(A)$ holds **iff** $A^2+1\in\{1,p\}$, i.e. iff $A^2+1=p$.
This does happen in general — whenever $A^2+1$ is prime, e.g. $(p,A)=(5,2),(37,6),
(101,10)$, and also $(17,4)$. In the phase considered in this article
($p\in\{17,41\}$, $A\equiv2\pmod 8$) it never happens: $A^2+1=17$ forces $A=4\not\equiv
2\pmod 8$, and $A^2+1=41$ has no integer solution. So throughout the hard phase
$K\nmid w_p$, and the divisibility $K\mid w_p$ — which is what the rank statement
$R=K/\gcd(K,v)\mid N$ of Corollary 1.5 would amount to at this index, with $v=1$ —
never holds. A rank-of-apparition argument therefore cannot by itself produce the
fixed-index exclusion; it is a complementary mechanism, which is how the manuscript
uses it (the rank statement there lives in the powerful normal form
$X^2+1=K^3V^2$, where the second coefficient is $KV$ by construction, and that normal
form is absent at index $p$).

---

## 5. Covering congruences: impossible within their own class [proof]

See `theorem_no_finite_modulus.md`. No fixed finite set of primes works; the set of
(W1) witnesses must depend on $A$. This is the only impossibility statement in this
file.

---

## 6. Summary

| Route | Verdict | Reason / status |
|---|---|---|
| fixed-modulus covering congruence | **impossible** | Theorem 1, Corollary 2 (proof) |
| refinements at 2 ($2^k$, 2-adic squareclasses) | impossible | $Q_p(A)\equiv1\pmod8$ for all $A\equiv2\pmod8$ (Lemma 1, proof) |
| Pell / continued fraction / descent | route diagnosis | the data produced are valuation parity, necessarily consistent with squares (§2) |
| cheap $A$-dependent congruences ($A^2+1$, $A\pm1$, mod $p$) | insufficient as a route | $2\%$ of $A$ satisfy all of them, e.g. $A=2$ (§5) |
| Lucas rank of apparition | unavailable at index $p$ | $w_p\equiv p\pmod{A^2+1}$, and $A^2+1=p$ has no solution in the hard phase (Cor. 4.2) |
| cyclotomic/Kummer resultant | new identity (3.1); does not feed §3.3 | exact norm identity is for $F_p$, not $Q_p$ (§3) |
| the manuscript's own route; global/height/curve/LFT arguments | untouched by this work | not in the scope of Theorem 1 (§1) |

**A precise constructive question that remains.** Is there a (W1)-witness
construction of lower complexity than the manuscript's (W2) certificate — e.g. a
polynomial $U$ of degree $<p$ with $J(U(2A),Q_p(A))=-1$ for all $A\equiv2\pmod 8$, or
a description of a (W1) witness prime from the factorisation of $A^2+1$ and $A\pm1$?
Corollary 2 shows the answer cannot be a function of $A\bmod M$ alone. I did not find
such a construction; this is an open question in the sense that I have neither a
construction nor a theorem excluding one, and I have not surveyed the literature for
it.

## 7. Reproduce

```
cd .ultramath/smw70l62n/m7
python3 route_scope_checks.py     # Prop. 3.1 (resultant) and Prop. 4.1 (w_p mod K)
python3 verify_route_scope.py     # all other finite data, prints ROUTE_SCOPE_OK
```
