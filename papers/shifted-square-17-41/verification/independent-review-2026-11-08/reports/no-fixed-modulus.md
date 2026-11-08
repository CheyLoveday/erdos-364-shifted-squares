# No fixed-modulus covering certificate for the 17/41 shifted-square obstruction

Swarm `smw70l62n`, member m7, direction d5 (elementary / constructive routes).
Status labels: **[proof]** = ordinary proof written out here; **[cert]** = exact
finite computation, reproduced by `verify_route_scope.py`; **[lit]** = published
theorem; **[num]** = numerical experiment, no proof value.

**Revision note.** This file was revised after review. Two things were tightened:
the two inequivalent notions of "witness" are now separated (§0.1), and all broad
claims are cut back to the proved scope (§3.1). The mathematical content (Lemma 1,
Lemma 2, Theorem 1) is unchanged.

## 0. Setting and target

The paper's notation: $F_0(A)=1$, $F_1(A)=A$, $F_{n+2}(A)=2AF_{n+1}(A)+F_n(A)$;
$D_0=2$, $D_1=T$, $D_{n+2}=TD_{n+1}+D_n$; $D_n(2A)=2F_n(A)$; $g_p=D_p-2$.

Throughout, $p\in\{17,41\}$ and
$$Q_p(A) \;:=\; F_p(A)-1 \;=\; \frac{g_p(2A)}{2}\qquad(A\in\mathbb Z),$$
an integer, so that the excluded equation is $Q_p(A)=y^2$ (the paper's Theorem 4.2,
the $A\equiv 2 \pmod 8$ phase of Theorem 1.2).

### 0.1 Two different notions of "witness"

* **(W1) local non-square witness.** A prime $\ell$ such that $Q_p(A)$ is not a square
  in $\mathbb Q_\ell$; equivalently $\chi_\ell(Q_p(A))=-1$ if $\ell\nmid Q_p(A)$, and
  $v_\ell(Q_p(A))$ odd with a non-residue unit part if $\ell\mid Q_p(A)$. A single
  (W1) witness at any prime $\ell$ proves that $Q_p(A)$ is not an integer square.
  Divisibility of $Q_p(A)$ by $\ell$ is *not* required. Conversely, if $Q_p(A)>0$ is
  not a square, then by Hasse's principle for $x^2=Q_p(A)$ (or directly from
  valuations) some (W1) witness exists.
* **(W2) factor witness** (the shape used in §7.2 of the manuscript). A prime
  $\ell\mid Q_p(A)$ with $v_\ell(Q_p(A))$ odd and with the *detector character*
  $\left(\frac{U_p(2A)}{\ell}\right)=-1$; equivalently a non-residue residue
  $U_p(2A)$ at a prime of odd valuation. A (W2) witness is (W1) plus extra structure;
  the paper's Proposition 7.1 asserts the existence of a (W2) witness for every $A$,
  uniformly in a fixed numerator polynomial.

The two notions are genuinely different: the first is a statement about
$Q_p(A)\bmod\ell$, the second factors the Jacobi symbol of the paper's certificate.
Both occur at the manuscript's own reference point $A=2$: for $p=41$ one has
$F_{41}(2)-1\equiv 20\pmod{23}$ with $\left(\frac{20}{23}\right)=-1$, a (W1) witness;
and $F_{41}(2)-1=79\cdot1373\cdot115471\cdot1506563\cdot1344905911$ gives (W2) data.
**[cert]** (`verify_route_scope.py`, section [6b]).

### 0.2 What is proved here

A "covering-congruence certificate" for Theorem 4.2 would be: a modulus $M$ and, for
every class $a\bmod M$ with $a\equiv 2\pmod 8$, a prime $\ell\mid M$ such that
$Q_p(a)$ is a non-square modulo $\ell^{v_\ell(M)}$ (in particular $\ell$ is a (W1)
witness for every $A\equiv a$). Such a certificate would prove Theorem 4.2 outright,
since a square is a square modulo every modulus; it is one natural attempt at an
elementary proof (the paper's own argument is *also* elementary arithmetic, but with
$A$-dependent data: a fixed polynomial numerator and the $A$-dependent denominator
$Q_p(A)$).

**Result [proof].** No covering-congruence certificate exists, for either prime:
for every finite set $S$ of primes and every $M$ there are infinitely many
$A\equiv 2\pmod 8$ for which *no* prime of $S$ is a (W1) witness, i.e. $Q_p(A)$ is a
square in $\mathbb Q_\ell$ for every $\ell\in S$ and in $\mathbb Q_2$. This says
nothing against any other proof strategy — see §3.1 for the exact scope.

---

## 1. Lemma 1 (2-adic phase). [proof]

**Lemma 1.** Let $A\equiv 2 \pmod 4$ and $n\ge 0$.

1. $F_n(A)\equiv 1 \pmod 8$ if $n$ is even;
2. $F_n(A)\equiv A \pmod 8$ if $n\equiv 1 \pmod 4$;
3. $F_n(A)\equiv A+4 \pmod 8$ if $n\equiv 3 \pmod 4$.

*Proof.* Put $u_n=F_n(A)\bmod 8$. Since $A\equiv 2\pmod 4$ we have $2A\equiv 4\pmod 8$,
hence from the recursion
$$u_{n+2}\equiv 4u_{n+1}+u_n \pmod 8. \tag{1.1}$$
The initial values are $u_0=1$, $u_1=A$, and, because
$A^2\equiv 4 \pmod{16}$ for $A\equiv 2\pmod 4$, $u_2=2A^2+1\equiv 1\pmod 8$, and
$u_3\equiv 4u_2+u_1\equiv A+4\pmod 8$.

We show $u_{n+4}\equiv u_n$. Two applications of (1.1) give
$u_{n+4}\equiv 4u_{n+3}+u_{n+2}\equiv 4(4u_{n+2}+u_{n+1})+u_{n+2}
=17u_{n+2}+4u_{n+1}\equiv u_{n+2}+4u_{n+1}\pmod 8$,
and (1.1) gives $4u_{n+1}\equiv u_{n+2}-u_n\pmod 8$; hence
$u_{n+4}\equiv 2u_{n+2}-u_n \pmod 8$. Also (1.1) gives $u_{n+2}\equiv u_n\pmod 4$,
say $u_{n+2}=u_n+4k$, so $2u_{n+2}-u_n=u_n+8k\equiv u_n\pmod 8$. Thus $u$ is
4-periodic modulo $8$ and the four classes are $1,\,A,\,1,\,A+4$. $\square$

This is an independent, self-contained proof of the paper's (2.8) and hence, with
the standard odd 2-adic square criterion ($m$ odd is a square in $\mathbb Z_2$ iff
$m\equiv 1\pmod 8$), of the paper's Proposition 2.1 — one of the results the paper
lists as human-only. **[proof]**

**Corollary 1.1.** For $p\in\{17,41\}$ (so $p\equiv 1\bmod 4$) and $A\equiv 2\pmod 8$
one has $Q_p(A)\equiv A-1\equiv 1\pmod 8$, and $Q_p(A)$ is a square in
$\mathbb Z_2$; in particular $Q_p(A)$ is a square modulo $2^{\alpha}$ for every
$\alpha\ge 1$. **[proof]**

So the prime $2$ is never a (W1) witness in the hard phase; this is the paper's §2.4
point.

---

## 2. Lemma 2 (every odd prime admits a compatible residue). [cert] + [lit]

**Lemma 2.** For $p\in\{17,41\}$ and every odd prime $\ell$ there is $c\in\mathbb Z$
with $Q_p(c)\not\equiv 0\pmod\ell$ and $Q_p(c)$ a square modulo $\ell$.

*Proof.* Two cases.

(i) $\ell\le 5000$: direct verification over all residues, for all $668$ odd primes
below $5000$ and both primes $p$; the minimum proportion of admissible residues
encountered is $1/3$ (at $\ell=3$, $p=17$) and $0.229$ (at $\ell=83$, $p=41$). **[cert]**

(ii) $\ell>p^{2}$: let $f$ be the reduction of $Q_p$ modulo $\ell$, a polynomial of
degree $p$ over $\mathbb F_\ell$. Since $\operatorname{disc}(g_p)=2^{3(p-1)/2}p^{p}$
has only the prime divisors $2$ and $p$, and $Q_p(A)=g_p(2A)/2$, the reduction $f$ is
squarefree. Let $\chi$ be the quadratic character of $\mathbb F_\ell$ (with
$\chi(0)=0$) and suppose $\chi(f(c))\ne 1$ for all $c$. Then
$\sum_c \chi(f(c)) = -(\ell-r)$ where $r=\#\{c: f(c)=0\}\le p$. Weil's bound for
quadratic character sums gives $|\sum_c\chi(f(c))|\le (p-1)\sqrt\ell$, so
$\ell-p\le(p-1)\sqrt\ell$. Writing $t=\sqrt\ell$ this is $t^{2}-(p-1)t-p\le 0$, i.e.
$t\le \tfrac12\bigl(p-1+\sqrt{(p-1)^2+4p}\bigr)=p$, so $\ell\le p^{2}$, a
contradiction. **[lit]**

Since $p^2<5000$ for both primes, (i) and (ii) cover every odd prime. $\square$

---

## 3. Theorem (no finite witness set). [proof]

**Theorem 1.** Let $p\in\{17,41\}$, let $S$ be a finite set of odd primes, and let
$e_\ell\ge1$ $(\ell\in S)$, $\alpha\ge1$ be integers. Then there are infinitely many
integers $A\equiv 2\pmod 8$ such that
$$Q_p(A)\equiv t^{2}\pmod{2^{\alpha}\prod_{\ell\in S}\ell^{e_\ell}}\quad
\text{for some } t\in\mathbb Z .$$
In particular $Q_p(A)$ is a square in $\mathbb Q_2$ and in $\mathbb Q_\ell$ for every
$\ell\in S$.

*Proof.* For each $\ell\in S$ choose $c_\ell$ as in Lemma 2; a unit of
$\mathbb Z_{\ell}$ whose residue class modulo $\ell$ is a square is a square in
$\mathbb Z_{\ell}$, so $Q_p(c_\ell)$ is a square modulo $\ell^{e_\ell}$; fix $t_\ell$
with $t_\ell^2\equiv Q_p(c_\ell)\pmod{\ell^{e_\ell}}$. By Corollary 1.1, $Q_p(2)$ is a
square in $\mathbb Z_2$, hence a square modulo $2^{\alpha}$; fix $t_0$ with
$t_0^2\equiv Q_p(2)\pmod{2^{\alpha}}$.

By the Chinese remainder theorem the simultaneous conditions
$$A\equiv 2 \!\!\pmod{2^{\max(\alpha,3)}},\qquad
A\equiv c_\ell \!\!\pmod{\ell^{e_\ell}}\ \ (\ell\in S)$$
define a residue class $A\equiv A_0 \pmod{M'}$ with
$M'=2^{\max(\alpha,3)}\prod_{\ell\in S}\ell^{e_\ell}$; every such $A$ satisfies
$A\equiv 2\pmod 8$, $Q_p(A)\equiv Q_p(2)$ modulo $2^{\max(\alpha,3)}$ and
$Q_p(A)\equiv Q_p(c_\ell)$ modulo $\ell^{e_\ell}$. Applying the Chinese remainder
theorem to the $t_0,t_\ell$ produces $t$ with
$t^{2}\equiv Q_p(A)\pmod{2^{\alpha}\prod_{\ell\in S}\ell^{e_\ell}}$. Since moreover
$Q_p(A)\not\equiv0\pmod{\ell}$ by construction, $Q_p(A)$ is a square in
$\mathbb Q_{\ell}$; and $Q_p(A)\equiv1\pmod 8$ gives a square in $\mathbb Q_2$. The
class $A_0 \bmod M'$ has infinitely many representatives. $\square$

**Corollary 2 (no covering certificate; precise form).** Fix $p\in\{17,41\}$ and a
finite set $S$ of odd primes. Then there are infinitely many $A\equiv2\pmod 8$ for
which no prime of $S\cup\{2\}$ is a (W1) witness. Consequently there is no modulus $M$
such that testing $Q_p$ modulo $\ell^{v_\ell(M)}$ for the primes $\ell\mid M$
excludes every admissible class: for each candidate modulus the set $S$ of its prime
divisors is finite, and the infinitely many $A$ above pass every one of those tests.
$\square$

### 3.1 Exact scope of Theorem 1 and Corollary 2

**What is proved.** Every proof strategy of the following shape fails: "for each
$A\equiv2\pmod 8$, verify local squareness of $Q_p(A)$ at the primes of a *fixed
finite* set $S$, and reject $A$ when some $\ell\in S$ is a (W1) witness." In
particular no fixed-modulus covering congruence certificate exists. Equivalently:
for every finite set $S$ of primes there are infinitely many admissible $A$ such that
$S$ contains no (W1) witness for $A$ — so a (W1)-based proof cannot work with a fixed
finite list of primes.

**What is not proved, and is not true as a general statement.**

* Nothing is asserted about *which* strategies can prove Theorem 4.2. In particular
  the manuscript's own route is elementary arithmetic (Jacobi symbols, quadratic
  reciprocity, explicit integer certificates) — it is elementary, just not of
  fixed-modulus type: its numerator $U_p(2A)$ and denominator $Q_p(A)$ both depend on
  $A$.
* Global arguments are untouched: a proof by height bounds, by integral points on a
  curve $y^2=Q_p(A)$, by hyperelliptic/Thue methods, or by linear forms in
  logarithms need not exhibit any (W1) witness at all, and nothing here bears on such
  arguments.
* (W2) witnesses are not excluded either; on the contrary, the paper's Proposition 7.1
  supplies one for every $A$, and such a witness is necessarily $A$-dependent by
  Corollary 2 only in the following weak sense: for each finite $S$ there are
  admissible $A$ all of whose (W2) witnesses lie outside $S$.

**Where the (W1) statement does bite.** Since a positive non-square integer is a
non-square in $\mathbb Q_\ell$ for some $\ell$, and since Corollary 2 shows that this
$\ell$ cannot be confined to a fixed finite set, any argument that produces (W1)
witnesses must produce them as a function of $A$. That is the whole content and it is
a statement about the family, not about the existence of alternative proof methods.

### 3.2 Explicit data [cert]

* $p=17$, $A=13436280461778872715068835665689687346047342031343196025682332048755323382446365162$:
  $A\equiv2\pmod 8$, $Q_{17}(A)$ is a square in $\mathbb Q_2$ and in $\mathbb Q_\ell$
  for every prime $\ell\le200$, and $Q_{17}(A)$ is a non-square in $\mathbb Q_{211}$
  — so $211$ is a (W1) witness. Also no prime $\ell\le200$ divides $Q_{17}(A)$, so
  every (W2) witness of this $A$ exceeds $200$; I have not computed one ($Q_{17}(A)$
  has about $1400$ digits).
* $p=41$: the analogous value is
  $A=22805347438890107579041398021068316865585543438038802371828994845480719532417275042$,
  with $227$ as the first (W1) witness, likewise not a divisor of $Q_{41}(A)$.
* $p=17$, $A=72708208931635202$: $A\equiv2\pmod8$ and
  $t^2\equiv Q_{17}(A)\pmod M$ with $M=2^{20}3^25^27^211^213^223^2=125056496723558400$,
  $t=84837427159578031$. For $p=41$: $A=58627620392140802$, same $M$,
  $t=76419143705971351$.
* $A=2$ (reference point): $F_{17}(2)-1=13\cdot1751444197$ and
  $F_{41}(2)-1=79\cdot1373\cdot115471\cdot1506563\cdot1344905911$ — matching Table A1 —
  and $F_{41}(2)-1\equiv20\pmod{23}$, $\left(\frac{20}{23}\right)=-1$: a (W1) witness
  of the shape used for the Lean endpoint argument.

---

## 4. Reproduce

```
cd .ultramath/smw70l62n/m7
python3 verify_route_scope.py      # prints ROUTE_SCOPE_OK; sections [1]-[9]
```
Section [2b] is Lemma 1; [4] is Lemma 2(i); [5], [6], [6b] are the data of §3.2.
The Weil-bound half of Lemma 2 is not computable and is proved above.

## 5. Honest scope (summary)

* Theorem 1 and Corollary 2 are proofs, not experiments. Their only external input is
  the standard Weil bound for quadratic character sums, and one finite computation
  (668 primes, both fields).
* They rule out fixed-modulus covering certificates and nothing else. They are
  consistent with, and explain, the manuscript's structure (fixed numerator,
  $A$-dependent denominator), but they do not make any other strategy impossible.
* They do not bear on the correctness of the paper's proofs, the Lean development, or
  the human-only steps; those are audited elsewhere.
