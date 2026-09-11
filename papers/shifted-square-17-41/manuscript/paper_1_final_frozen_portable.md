---
title: "Shifted-square obstructions at indices divisible by 17 or 41 in a family of Lucas sequences"
author: "Chey G. A. Loveday"
affiliation: "Overdog.ai Ltd, Colchester, England"
date: "10 September 2026"
lang: en-GB
---

## Abstract

Let $F_0(A)=1$, $F_1(A)=A$, and $F_{n+2}(A)=2AF_{n+1}(A)+F_n(A)$. For nonnegative integers $A\equiv2\pmod4$, we prove that $F_N(A)-1$ is not a square whenever $N>0$ is divisible by $17$ or $41$. Every positive even index is excluded independently by the exact identity $v_2(F_N(A)-1)=2v_2(N)+1$. At the fixed indices $p=17,41$, the remaining parameter class $A\equiv2\pmod8$ gives shifted values that are squares in $\mathbb Z_2$. We exclude integer squares in this class using explicit units in number fields of degrees $17$ and $41$. A common Hilbert-reciprocity criterion turns the associated finite arithmetic into an obstruction valid for every parameter. The same construction yields the uniform Jacobi identity $J(U_p(2A),F_p(A)-1)=-1$ for explicit polynomials $U_p$. Composition with an odd inner index then gives the index-divisibility theorem. We deduce a restriction on the exact Pell exponent in a square-middle powerful-number family. Complete proofs and finite certificate data are included, together with an exact-arithmetic verifier; the corresponding integer-Jacobi formalisation is described separately.

<a id="introduction"></a>

## 1. Introduction and main results

<a id="problem"></a>

### 1.1. The equation and its normalisation

Perfect powers in recurrence sequences can be studied by fixing the sequence and varying the index, or by fixing an index and varying the recurrence parameters. We consider a parameter family of companion Lucas sequences. For $A,n\in\mathbb Z_{\ge0}$, define

$$
\begin{gathered}
F_0(A)=1,\qquad F_1(A)=A,\\
F_{n+2}(A)=2AF_{n+1}(A)+F_n(A).
\end{gathered}
\qquad \text{(1.1)}
$$

In the usual Lucas notation, $2F_n(A)=V_n(2A,-1)$, where

$$
\begin{gathered}
V_0(P,Q)=2,\qquad V_1(P,Q)=P,\\
V_{n+2}(P,Q)=PV_{n+1}(P,Q)-QV_n(P,Q).
\end{gathered}
$$

The factor of two is part of our normalisation. The problem is to exclude

$$
F_N(A)=y^2+1.
\qquad \text{(1.2)}
$$

Thus it is the shifted value $F_N(A)-1$, not the recurrence term itself, that is required to be a square. We work with $A\equiv2\pmod4$. At $A=2$ the sequence begins $1,2,9,38,161,682,\ldots$; the solution at $N=1$ shows that an unrestricted exclusion in the index would be false.

The fixed-index results are uniform over the stated parameter progression. Their purpose is not to extend a numerical search in one sequence, but to exclude an entire family of shifted values. The field construction controls every admissible $A$ at once. Composition then turns an odd iterate into a new parameter, extending the fixed-index exclusions to infinitely many indices.

The application comes from the conjecture that no three consecutive positive integers are powerful [4]. In the square-middle case the triple has the form $(X^2-1,X^2,X^2+1)$. If the upper neighbour is powerful, its squarefree-cube decomposition gives

$$
X^2+1=K^3V^2,
\qquad X^2-K(KV)^2=-1.
$$

The second equation is a negative Pell equation. In the family where $X-1=y^2$, its first coordinate must also be one more than a square. Repeated multiplication of a norm-minus-one unit produces exactly the recurrence (1.1). The recurrence theorem is therefore the primary result; the powerful-number consequence follows by identifying its parameter and exponent precisely.

<h3 id="main-results">1.2. Main results</h3>

<a id="thm-main"></a>
**Theorem 1.1 (Index-divisibility obstruction).** Let $A\in\mathbb Z_{\ge0}$ satisfy $A\equiv2\pmod4$, and let $N$ be a positive integer. If $17\mid N$ or $41\mid N$, then

$$
F_N(A)\ne y^2+1
\qquad(y\in\mathbb Z).
\qquad \text{(1.3)}
$$

The proof separates two mechanisms: a reciprocity obstruction at the fixed odd indices and an elementary valuation argument at every positive even index.

<a id="thm-fixed"></a>
**Theorem 1.2 (Fixed indices).** For $A\in\mathbb Z_{\ge0}$ with $A\equiv2\pmod4$,

$$
\begin{gathered}
F_{17}(A)\ne y^2+1,\\
F_{41}(A)\ne y^2+1
\qquad(y\in\mathbb Z).
\end{gathered}
\qquad \text{(1.4)}
$$

These are two explicit instances, with different unit certificates. No uniform theorem in the prime index is assumed.

<a id="thm-even"></a>
**Theorem 1.3 (Exact even-index valuation).** For $A\in\mathbb Z_{\ge0}$ with $A\equiv2\pmod4$, and every positive even $N$,

$$
v_2\bigl(F_N(A)-1\bigr)=2v_2(N)+1.
\qquad \text{(1.5)}
$$

In particular, every positive even index is excluded, without a condition involving $17$ or $41$.

We use $v_\ell(m)$ for the exponent of the rational prime $\ell$ in a nonzero integer $m$. All values in (1.5) are positive. The right side is odd, whereas a square has even valuation.

The recurrence is also the coefficient sequence of a norm-minus-one quadratic unit.

<a id="cor-pell"></a>
**Corollary 1.4 (Negative-Pell formulation).** Let $K,u,v\in\mathbb Z_{\ge0}$ satisfy

$$
u^2+1=Kv^2,\qquad u\equiv2\pmod4.
\qquad \text{(1.6)}
$$

Write $(u+v\sqrt K)^N=X_N+Y_N\sqrt K$ in $\mathbb Z[\sqrt K]$. If $N>0$ and at least one of $2\mid N$, $17\mid N$, $41\mid N$ holds, then $X_N-1$ is not a square.

Here $X_N$ is the coefficient of $1$, not the value of the entire unit at a real embedding. Neither squarefreeness of $K$ nor fundamentality of the unit is a hypothesis of this corollary.

For the powerful-number application, the normal form and its divisibility conditions can be stated without implementation-specific terminology. A positive integer is *powerful* if every prime appearing in it has exponent at least two.

<a id="cor-source"></a>
**Corollary 1.5 (Exponent restriction in the lower-square family).** Suppose $X\ge2$, $X\equiv2\pmod8$, $X-1$ is a square, and $X^2+1$ is powerful. Write uniquely

$$
\begin{gathered}
X^2+1=K^3V^2,\\
K\text{ squarefree},\quad K,V>0.
\end{gathered}
\qquad \text{(1.7)}
$$

Let $\varepsilon=u+v\sqrt K$ be the least unit greater than $1$ in $\mathbb Z[\sqrt K]$, under the embedding $\sqrt K>0$. Then $N(\varepsilon)=-1$, and there is a unique positive odd $N$ such that

$$
X+KV\sqrt K=\varepsilon^N.
\qquad \text{(1.8)}
$$

Set $R=K/\gcd(K,v)$. Then $R\mid N$; writing $N=RE$, both $R$ and $E$ are positive and odd, and

$$
\gcd(N,17\cdot41)=1.
\qquad \text{(1.9)}
$$

In particular, the conditions $17\mid E$, $41\mid E$, and $41\mid R$ each exclude such an $X$.

Section 6 proves the existence of this normal form as well as the exponent restriction. Here $X$ is the square root of the middle term, not the middle term itself. The result applies, in particular, to any powerful triple $(X^2-1,X^2,X^2+1)$ in the displayed lower-square class. It does not require the lower neighbour $X^2-1$ to be powerful, and therefore gives a necessary condition before that additional requirement is imposed.

<a id="strategy"></a>

### 1.3. The arithmetic mechanism

At the fixed indices $p=17,41$, reduction modulo $8$ excludes $A\equiv6\pmod8$. In the remaining phase $A\equiv2\pmod8$, every value $F_p(A)-1$ is a square in $\mathbb Z_2$. The distinction supplied by the proof is therefore not a finer congruence modulo a power of $2$.

The argument uses the monic polynomial $g_p(T)=D_p(T,-1)-2$ and a root $\theta_p$ in a degree-$p$ field. A hypothetical square produces the element $(2A-\theta_p)/\theta_p$ of square norm. Control of its ideal support forces even valuations at odd primes. Pairing it with a carefully chosen element $b_p=\theta_pU_p(\theta_p)$ gives Hilbert symbol $+1$ at every odd and infinite place. The dyadic product, however, is $-1$ throughout the parameter class. These signs belong to the same pair of global elements, so Hilbert reciprocity makes their simultaneous occurrence impossible.

The same construction has a particularly concrete integer consequence, proved as Proposition 7.1:

$$
\begin{gathered}
\boxed{J\left(U_p(2A),F_p(A)-1\right)=-1}\\
(A\equiv2\pmod8).
\end{gathered}
\qquad \text{(1.10)}
$$

Here $J$ is the Jacobi symbol with positive odd denominator, and the polynomials $U_p$ are specified in Section 4. The identity is unconditional in $A$, and the two arguments are coprime; a square denominator would therefore give $+1$. It forces an odd-prime obstruction at every parameter, although the obstructing prime may vary with $A$. The number-field proof provides a uniform certificate without first locating or factoring that obstruction for each parameter.

**Why $17$ and $41$?** The common criterion requires explicit field data and a unit with a prescribed nontrivial dyadic character. The units displayed below meet that requirement in these two fields. Degree, signature and the existence of a unit of norm $-1$ do not alone determine the character. The construction supplies two instances of one criterion, not a uniform formula for detecting units at all prime indices. The two primes serve here as recurrence indices and field degrees; they are not asserted to be the local primes detecting every nonsquare.

<a id="related-work"></a>

### 1.4. Related work and organisation

Bremner and Tzanakis [1] determine the parameter pairs for which the ninth or twelfth term of a Lucas $U$-sequence is a square. Their fixed-index, varying-parameter viewpoint is close to ours, but the present problem concerns shifted values of a normalised companion sequence. Bennett, Dahmen, Mignotte and Siksek [2] study shifted powers using Frey curves over totally real fields. Bennett, Patel and Siksek [3] develop a broader shifted Lucas–Lehmer framework combining linear forms in logarithms with modular methods. Here the fixed-index exclusion is obtained from an explicit unit character and Hilbert reciprocity in a fixed number field, and is then transported by composition. The standard reciprocity laws and recurrence identities provide the framework; the explicit detecting units and the uniform exclusions are the content of the present construction.

The powerful-triple problem supplies the application rather than an additional assumption in the recurrence theorem. Chan [4] gives a Pell-based exclusion for a different, cube-centred family. She [12] treats another constrained cube-centred family, and Ma [13] extends related exclusions to further perfect-power middle terms. These results concern different families from the exact exponent restriction in the lower-square normal form (1.7)–(1.8).

Section 2 proves the recurrence identities and the local classification at $2$. Section 3 gives the common Hilbert criterion, and Section 4 supplies its two explicit instances. Section 5 assembles the main theorem. Section 6 proves the Pell and powerful-number consequences, including the divisibility-rank calculation. Section 7 proves the Jacobi identity and describes its formal realisation. Section 8 states the mathematical scope. The appendices give the reference arithmetic, a compact formal concordance and a self-contained exact-arithmetic verifier for the finite inputs.

<a id="recurrence"></a>

## 2. Recurrence identities and the local analysis at 2

<a id="dickson"></a>

### 2.1. Dickson normalisation

Write $D_n(T)=D_n(T,-1)$, where

$$
\begin{gathered}
D_0(T)=2,\qquad D_1(T)=T,\\
D_{n+2}(T)=TD_{n+1}(T)+D_n(T).
\end{gathered}
\qquad \text{(2.1)}
$$

Comparison with (1.1) proves, for every $n$, the polynomial identity

$$
D_n(2A)=2F_n(A).
\qquad \text{(2.2)}
$$

For odd $p$, set $g_p(T)=D_p(T)-2$. Thus

$$
F_p(A)=y^2+1
\quad\Longleftrightarrow\quad
g_p(2A)=2y^2.
\qquad \text{(2.3)}
$$

The change of variable $x=2A$ makes the left side a monic polynomial in $x$. The scalar $2$ on the right is retained in the norm calculation.

<a id="doubling"></a>

### 2.2. Conjugate powers and doubling

Put

$$
\begin{aligned}
\alpha&=A+\sqrt{A^2+1},\\
\beta&=A-\sqrt{A^2+1}.
\end{aligned}
$$

Both roots satisfy $Z^2=2AZ+1$, and $\alpha\beta=-1$. The initial values and recurrence therefore give

$$
\begin{gathered}
F_n(A)=\frac{\alpha^n+\beta^n}{2},\\
F_{2n}(A)=2F_n(A)^2-(-1)^n.
\end{gathered}
\qquad \text{(2.4)}
$$

In particular, the two doubling identities have different parity guards:

$$
F_{2n}(A)-1=2F_n(A)^2
\qquad(n\text{ odd}),
\qquad \text{(2.5)}
$$

and

$$
\begin{gathered}
\begin{aligned}
F_{2n}(A)-1
&=2(F_n(A)-1)\\
&\quad\cdot(F_n(A)+1)
\end{aligned}\\
(n\text{ even}).
\end{gathered}
\qquad \text{(2.6)}
$$

Throughout the remainder of this section, $A\equiv2\pmod4$. Reduction of (1.1) modulo $4$ gives

$$
F_n(A)\equiv
\begin{cases}
1\pmod4,&n\text{ even},\\
2\pmod4,&n\text{ odd}.
\end{cases}
\qquad \text{(2.7)}
$$

<a id="proof-even"></a>

### 2.3. Proof of Theorem 1.3

Write $N=2^s m$, with $s\ge1$ and $m$ odd. Equation (2.5) gives

$$
F_{2m}(A)-1=2F_m(A)^2.
$$

By (2.7), $v_2(F_m(A))=1$, so the initial valuation is $3$. At each later doubling the inner index $n$ is even. Equations (2.6) and (2.7) give

$$
\begin{aligned}
v_2(F_{2n}(A)-1)
&=1+v_2(F_n(A)-1)\\
&\quad+v_2(F_n(A)+1)\\
&=v_2(F_n(A)-1)+2.
\end{aligned}
$$

There are $s-1$ further doublings. Hence

$$
v_2(F_N(A)-1)=3+2(s-1)=2s+1.
$$

This proves Theorem 1.3. $\square$

For example, at $A=2$ the values $F_2(2)-1=8$, $F_4(2)-1=160$ and $F_8(2)-1=51840$ have valuations $3,5,7$. The doubling argument explains the pattern: the first odd-index step fixes the initial valuation, and each subsequent doubling adds exactly two.

<a id="odd-phases"></a>

### 2.4. The complete odd-index phase split

Reduction modulo $8$ shows that the even-index values are $1$, while the odd-index values alternate between $A$ and $A+4$. Explicitly, for odd $n$,

$$
F_n(A)\equiv
\begin{cases}
A\pmod8,&n\equiv1\pmod4,\\
A+4\pmod8,&n\equiv3\pmod4.
\end{cases}
\qquad \text{(2.8)}
$$

<a id="prop-two-adic"></a>
**Proposition 2.1 (Odd $2$-adic square criterion).** Let $A\equiv2\pmod4$ and $n>0$ be odd. Then

$$
\begin{gathered}
F_n(A)-1\in\mathbb Q_2^{\times2}\\
\Longleftrightarrow\\
(A\bmod8,n\bmod4)\in\{(2,1),(6,3)\}.
\end{gathered}
\qquad \text{(2.9)}
$$

**Proof.** The value is an odd integer by (2.7). An odd $2$-adic unit is a square exactly when it is $1$ modulo $8$. Necessity follows by reducing odd squares modulo $8$; sufficiency follows from strong Hensel applied at $1$ [7]. Equation (2.8) gives the four cases. $\square$

**Table 1.** Odd-index square conditions at the prime $2$.

| $A\bmod8$ | $n\bmod4$ | $(F_n(A)-1)\bmod8$ | Status over $\mathbb Z_2$ |
|:---:|:---:|:---:|:---|
| $2$ | $1$ | $1$ | Square |
| $2$ | $3$ | $5$ | Nonsquare |
| $6$ | $1$ | $5$ | Nonsquare |
| $6$ | $3$ | $1$ | Square |

No $17$- or $41$-divisibility condition enters this classification. In particular, the hard fixed-index phase is not eliminated by passing to larger powers of $2$. This says nothing about solubility at odd primes. For example,

$$
F_{41}(2)-1\equiv20\pmod{23},
$$

and $20$ is a quadratic nonresidue modulo $23$, despite this value lying in the first row of Table 1.

For $p=17,41$, both congruent to $1$ modulo $4$, the only remaining parameter class is $A\equiv2\pmod8$. The substitution already established in (2.3) becomes

$$
\begin{gathered}
x=2A\ge4,\qquad x\equiv4\pmod{16},\\
g_p(x)=2y^2.
\end{gathered}
\qquad \text{(2.10)}
$$

<a id="criterion"></a>

## 3. A common Hilbert-reciprocity criterion

<a id="local-global"></a>

### 3.1. Conventions and the product obstruction

For a finite prime $\mathfrak P$ of a number field $L$, valuations are normalised by $v_{\mathfrak P}(\mathfrak P)=1$; thus $v_{\mathfrak P}(2)=e(\mathfrak P/2)$ at a dyadic prime. We write $(a,b)_v$ for the quadratic Hilbert symbol. It depends only on the two local squareclasses, is bimultiplicative, and satisfies Hilbert reciprocity [5]:

$$
\prod_v(a,b)_v=1
\qquad(a,b\in L^\times).
\qquad \text{(3.1)}
$$

Here $L_v$ denotes the completion at the place $v$; a dyadic place lies above $2$. The notation $L_v^{\times2}$ means the subgroup of nonzero squares. The product is over all places, and all but finitely many factors equal $1$.

Reciprocity imposes compatibility among local signs: those attached to two global elements cannot be prescribed independently at different completions. The following proposition isolates this constraint. The argument excludes an incompatible arrangement of signs; it does not infer a global solution from local solubility.

<a id="prop-dyadic"></a>
**Proposition 3.1 (Dyadic obstruction).** Let $b,\delta_*\in L^\times$ satisfy

$$
\prod_{v\mid2}(\delta_*,b)_v=-1.
\qquad \text{(3.2)}
$$

There is no $\delta\in L^\times$ for which $(\delta,b)_v=1$ at every odd finite and every infinite place, while $\delta/\delta_*$ is a square at every dyadic completion.

**Proof.** Squareclass invariance makes the dyadic product for $\delta$ equal to that for $\delta_*$. Every other factor is $+1$. The resulting total product $-1$ contradicts (3.1). $\square$

The application must force all these conditions for the same global element. The reference $\delta_*$ need not arise from a solution: its role is to fix the dyadic squareclasses against which a hypothetical solution is compared.

<a id="monogenic-criterion"></a>

### 3.2. The fixed-field criterion

<a id="thm-criterion"></a>
**Theorem 3.2 (Monogenic fixed-field criterion).** Let $g\in\mathbb Z[T]$ be monic and irreducible of odd degree $d>1$, and put $L=\mathbb Q(\theta)$, where $g(\theta)=0$. Suppose:

1. $\mathcal O_L=\mathbb Z[\theta]$ and $N_{L/\mathbb Q}(\theta)=2$;
2. $L$ has exactly one real embedding and $0<\theta_{\mathbb R}<4$;
3. an integral element $b$ satisfies $(b)=(\theta)$;
4. for every $\mathfrak P\mid2$, with $e_{\mathfrak P}=v_{\mathfrak P}(2)$ and $d_{\mathfrak P}=v_{\mathfrak P}(4-\theta)$, one has $4e_{\mathfrak P}-d_{\mathfrak P}>2e_{\mathfrak P}$;
5. for $\delta_4=(4-\theta)/\theta$, one has $\prod_{\mathfrak P\mid2}(\delta_4,b)_{\mathfrak P}=-1$.

Then there are no integers $x,Y$ satisfying

$$
\begin{gathered}
x\ge4,\qquad x\equiv4\pmod{16},\\
g(x)=2Y^2.
\end{gathered}
\qquad \text{(3.3)}
$$

The notation $(b)=(\theta)$ denotes equality of principal ideals. Equivalently, $b=\theta u$ for a unit $u\in\mathcal O_L^\times$. Thus the detector may change the local squareclass without adding any odd-prime ideal support.

We prove the theorem in three steps: control of odd-prime support, neutrality away from $2$, and stability at $2$. The polynomial equation is used only to force the norm to be a square. The positivity and dyadic-stability arguments will also apply to nonsquare values, which is why the same construction later proves an unconditional Jacobi identity.

<a id="valuation-transfer"></a>

### 3.3. Norm and supporting primes

Suppose (3.3) holds. Irreducibility gives $g(x)\ne0$, so $Y\ne0$. Set

$$
\delta_x=\frac{x-\theta}{\theta}\in L^\times.
$$

Since $g$ is the monic minimal polynomial of $\theta$,

$$
\begin{aligned}
N(x-\theta)&=g(x),\\
N(\delta_x)&=\frac{g(x)}2=Y^2.
\end{aligned}
\qquad \text{(3.4)}
$$

Dividing by $\theta$ removes exactly the scalar $2$ in the polynomial equation. The orientation matters: in odd degree, $N(\theta-x)=-g(x)$.

A square global norm alone does not force even valuation at every prime ideal: the norm adds contributions from different primes above the same rational prime. Here monogenicity identifies the support before parity is transferred. Indeed,

$$
\begin{aligned}
\mathcal O_L/(x-\theta)
&\cong\mathbb Z[T]/(g(T),T-x)\\
&\cong\mathbb Z/(g(x)).
\end{aligned}
\qquad \text{(3.5)}
$$

For each rational prime $\ell\mid g(x)$, the right side has exactly one prime above $\ell$, with residue field $\mathbb F_\ell$. Consequently, exactly one prime ideal $\mathfrak P\mid\ell$ divides $x-\theta$, and its residue degree is one. Other primes above $\ell$ may exist, but do not divide this element. In concrete terms, the reduction $\theta\mapsto x\bmod\ell$ selects a single prime at which the norm valuation is concentrated. The argument also applies at ramified primes.

Because $\theta$ is integral of norm $2$, it is a unit at every odd prime. At an odd supporting prime, the ideal-norm formula becomes

$$
\begin{aligned}
v_\ell(N\delta_x)
&=\sum_{\mathfrak Q\mid\ell}
 f(\mathfrak Q/\ell)v_{\mathfrak Q}(\delta_x)\\
&=v_{\mathfrak P}(\delta_x).
\end{aligned}
\qquad \text{(3.6)}
$$

The left side is even by (3.4). Outside the support the valuation is zero. Thus every odd-prime valuation of $\delta_x$ is even. This is weaker than asserting that $\delta_x$ is a local square, and is exactly what the next step requires.

<a id="neutrality"></a>

### 3.4. The symbols away from 2

At a non-dyadic local field with residue field of cardinality $q$, write $a=\pi^r a_0$ and $c=\pi^s c_0$, with unit parts $a_0,c_0$. The standard formula [6] is

$$
(a,c)=(-1)^{rs(q-1)/2}
\chi(\overline{a_0})^s\chi(\overline{c_0})^r,
\qquad \text{(3.7)}
$$

where $\chi$ is the quadratic character of the residue field. Here $(b)=(\theta)$ makes $b$ a unit at every odd prime. With $a=\delta_x$, we have $s=0$ and $r$ even, giving $(\delta_x,b)_{\mathfrak P}=+1$.

At the real place,

$$
\delta_{x,\mathbb R}
=\frac{x-\theta_{\mathbb R}}{\theta_{\mathbb R}}>0.
$$

The real symbol is therefore $+1$, irrespective of the sign of $b$. Every complex symbol is $+1$ [5].

<a id="hensel"></a>

### 3.5. Stability of the dyadic squareclass

Compare $x$ with the reference $4$:

$$
\frac{\delta_x}{\delta_4}
=1+\frac{x-4}{4-\theta}.
\qquad \text{(3.8)}
$$

For $x=4$ this ratio is $1$. Otherwise, abbreviate $e=e_{\mathfrak P}$ and $d=d_{\mathfrak P}$. Since $16\mid x-4$,

$$
v_{\mathfrak P}\left(\frac{x-4}{4-\theta}\right)
\ge4e-d>2e.
\qquad \text{(3.9)}
$$

To see exactly where the threshold comes from, apply strong Hensel to $f(Z)=Z^2-(1+t)$ at $Z=1$. We have $f(1)=-t$ and $f'(1)=2$. The condition $v(f(1))>2v(f'(1))$ is therefore precisely $v(t)>2v(2)$ [7]. Thus $\delta_x/\delta_4$ is a square in every dyadic completion, and

$$
(\delta_x,b)_{\mathfrak P}
=(\delta_4,b)_{\mathfrak P}
\qquad(\mathfrak P\mid2).
\qquad \text{(3.10)}
$$

Strictness is indispensable. In $\mathbb Q_2$, the value $5=1+4$ meets equality $v_2(4)=2v_2(2)$ but is not a square. Hypothesis 4 places the perturbation beyond this boundary.

All conditions of Proposition 3.1 now hold, proving Theorem 3.2. $\square$

**Table 2.** Sign accounting under a hypothetical global solution of (3.3).

| Places | Forced sign | Argument |
|:---|:---:|:---|
| Odd finite | $+1$ at each place | Supporting-prime parity and unitness of $b$ |
| Real | $+1$ | Positivity of $\delta_x$ |
| Complex | $+1$ | Complex Hilbert pairing |
| Dyadic | Product $-1$ | Reference certificate and (3.10) |
| All places | Product must be $+1$ | Hilbert reciprocity |

The odd-place row is conditional on the global square hypothesis; it is not a claim that the original equation has local points at every odd prime. The quantified step from one reference calculation to the entire progression is (3.8)–(3.10).

<a id="fixed-fields"></a>

## 4. The two fixed-field certificates

<a id="field-data"></a>

### 4.1. Shared field data

For $p\in\{17,41\}$, set $g_p=D_p-2$ and $L_p=\mathbb Q(\theta_p)$. The exact finite inputs are as follows; Appendix C gives a standalone verifier.

**Table 3.** Polynomial and number-field data.

| Datum | Degree $17$ | Degree $41$ |
|:---|:---:|:---:|
| Irreducibility witness modulo | $67$ | $163$ |
| Polynomial and field discriminant | $2^{24}17^{17}$ | $2^{60}41^{41}$ |
| $[\mathcal O_{L_p}:\mathbb Z[\theta_p]]$ | $1$ | $1$ |
| Signature | $(1,8)$ | $(1,20)$ |

The auxiliary-prime reductions prove irreducibility over $\mathbb Q$. Appendix A.2 proves the power-order index one by Dedekind's index criterion, using two short polynomial congruences. The polynomial and field discriminants therefore coincide. These are certificates for the specified generator, not an inference that any generator of the field has index one.

For odd $p$, $D_p$ is monic and odd. Hence the constant term of $g_p$ is $-2$, giving $N(\theta_p)=2$. The real-root condition has an exact verification. Substituting $T=2\sinh t$ in (2.1) gives

$$
D_p(T)=2\sinh\left(p \operatorname{arsinh}(T/2)\right).
$$

This is strictly increasing for real $T$. Its unique value with $D_p(T)=2$ is

$$
\theta_{p,\mathbb R}
=2\sinh\left(\frac{\operatorname{arsinh}(1)}p\right)
\in(0,2).
\qquad \text{(4.1)}
$$

Thus the real positivity in Theorem 3.2 needs no numerical root approximation.

<a id="bare-detector"></a>

### 4.2. Why a unit is needed

Taking $b=\theta$ would give the desired odd-place unitness, but not the detecting sign.

<a id="prop-bare-theta"></a>
**Proposition 4.1 (The untwisted reference product).** In either fixed field,

$$
\prod_{\mathfrak P\mid2}
\left(\frac{4-\theta_p}{\theta_p},\theta_p\right)_{\mathfrak P}
=+1.
\qquad \text{(4.2)}
$$

**Proof.** At an odd prime supporting $\delta_4$, reduction gives $\theta_p\equiv4$. This is a nonzero square residue. Since $\theta_p$ is a unit there, (3.7) gives symbol $+1$, irrespective of the valuation of $\delta_4$. At other odd places both arguments are units, again giving $+1$. Real positivity and the complex evaluations give $+1$ at infinity. Hilbert reciprocity then proves (4.2). $\square$

If $u_p$ is a unit and $b_p=\theta_pu_p$, then $(b_p)=(\theta_p)$, while bimultiplicativity and (4.2) give

$$
\prod_{\mathfrak P\mid2}(\delta_4,b_p)_{\mathfrak P}
= \prod_{\mathfrak P\mid2}(\delta_4,u_p)_{\mathfrak P}.
\qquad \text{(4.3)}
$$

The unit changes the character without changing the odd-prime ideal support. This is the property to be achieved by the following explicit choices.

<a id="detector17"></a>

### 4.3. The degree-17 unit

Define

$$
\begin{aligned}
U_{17}(T)={}&-1-D_2(T)+D_3(T)+D_4(T)\\
&-D_5(T)-2D_{12}(T)+D_{14}(T).
\end{aligned}
\qquad \text{(4.4)}
$$

Exact polynomial arithmetic gives

$$
\operatorname{Res}(g_{17},U_{17})=-1.
\qquad \text{(4.5)}
$$

This resultant is the norm of the algebraic integer $u_{17}=U_{17}(\theta_{17})$, so $u_{17}$ is a unit. Set $b_{17}=\theta_{17}u_{17}$. The reference evaluations are

$$
\begin{aligned}
H_{17}:=g_{17}(4)/2&=13\cdot1751444197,\\
U_{17}(4)&=532303029.
\end{aligned}
\qquad \text{(4.6)}
$$

Their reference character is $J(U_{17}(4),H_{17})=-1$; the individual prime characters are recorded in Appendix A.

<a id="detector41"></a>

### 4.4. The degree-41 unit

Define

$$
U_{41}(T)=c_0+\sum_{k=1}^{40}c_kD_k(T),
\qquad \text{(4.7)}
$$

with coefficients in increasing order:

$$
\begin{aligned}
(c_0,\ldots,c_{40})=(&-1,-15,2,4,8,7,-8,\\
&-10,-3,6,7,3,-1,-9,\\
&3,7,2,3,-9,-6,1,\\
&8,4,1,-4,-6,3,7,\\
&0,2,-7,-4,1,6,-1,\\
&0,-2,-5,4,5,-5).
\end{aligned}
\qquad \text{(4.8)}
$$

The coefficient $c_0$ multiplies $1$, not $D_0=2$. The exact resultant is

$$
\operatorname{Res}(g_{41},U_{41})=-1.
\qquad \text{(4.9)}
$$

Thus $u_{41}=U_{41}(\theta_{41})$ is a unit; set $b_{41}=\theta_{41}u_{41}$. At the reference,

$$
\begin{gathered}
\begin{aligned}
H_{41}:=g_{41}(4)/2
&=79\cdot1373\cdot115471\\
&\quad\cdot1506563\cdot1344905911,
\end{aligned}\\[0.4em]
U_{41}(4)\\
=-43956715453803235217163523.
\end{gathered}
\qquad \text{(4.10)}
$$

Again $J(U_{41}(4),H_{41})=-1$, with the factors and signs given in Appendix A. In both fields,

$$
\begin{gathered}
N(u_p)=-1,\qquad N(b_p)=-2,\\
(b_p)=(\theta_p).
\end{gathered}
\qquad \text{(4.11)}
$$

The norm $-1$ proves unitness here; it is not the detecting condition by itself. The unit $-1$, for example, also has norm $-1$ in an odd-degree field, but $J(-1,H_p)=+1$ because $H_p\equiv1\pmod8$.

<a id="dyadic-data"></a>

### 4.5. Dyadic primes and the hard-phase theorem

At a prime $\mathfrak P\mid2$, put

$$
\begin{gathered}
e=v_{\mathfrak P}(2),\quad
f=f(\mathfrak P/2),\\
t=v_{\mathfrak P}(\theta_p),\quad
d=v_{\mathfrak P}(4-\theta_p),\quad
s=v_{\mathfrak P}(b_p).
\end{gathered}
$$

There are three dyadic primes in each field. Put $h=4$ for $p=17$ and $h=10$ for $p=41$. The fixed-field calculations give the following rows. Appendix A independently derives their valuation data and the product of their Hilbert signs:

**Table 4.** Dyadic certificate rows, with $\delta_4=(4-\theta_p)/\theta_p$.

| $e$ | $f$ | $(t,d,s)$ | $(\delta_4,b_p)_{\mathfrak P}$ | $4e-d>2e$ |
|:---:|:---:|:---:|:---:|:---:|
| $1$ | $1$ | $(1,1,1)$ | $+1$ | $3>2$ |
| $2$ | $h$ | $(0,0,0)$ | $-1$ | $8>4$ |
| $2$ | $h$ | $(0,0,0)$ | $+1$ | $8>4$ |

The sum $\sum ef=1+4h=p$ accounts for the whole degree. The equal-type primes are distinct, and the table specifies the multiset of rows, not a preferred ordering. In particular,

$$
\prod_{\mathfrak P\mid2}(\delta_4,b_p)_{\mathfrak P}=-1.
\qquad \text{(4.12)}
$$

The individual Hilbert signs are additional data from the number-field certificate [8], not deductions from the valuation columns. Theorem 3.2 requires only their product. Appendix A proves that product from the rational-prime reference characters and reciprocity; the verifier in Appendix C checks all the finite polynomial and integer data used in that proof.

<a id="thm-hard"></a>
**Theorem 4.2 (Hard fixed-index phase).** For $p\in\{17,41\}$ and $A\in\mathbb Z_{\ge0}$ with $A\equiv2\pmod8$,

$$
F_p(A)\ne y^2+1
\qquad(y\in\mathbb Z).
\qquad \text{(4.13)}
$$

**Proof.** Table 3, with the maximality proof in Appendix A.2, and (4.1) supply the field hypotheses of Theorem 3.2. The resultants and (4.11) supply its detector hypothesis. The dyadic valuation data in Table 4 give strict stability, and Appendix A.1 proves the negative reference product. Equation (2.10) then gives the conclusion. $\square$

This proof includes $A=2$: the reference ratio at $x=4$ is exactly $1$.

<a id="propagation"></a>

## 5. Phase strengthening and assembly

<a id="proof-fixed"></a>

### 5.1. Proof of Theorem 1.2

If $A\equiv2\pmod8$, Theorem 4.2 applies. If $A\equiv6\pmod8$, then for $p=17,41$, both $1$ modulo $4$, equation (2.8) gives $F_p(A)-1\equiv5\pmod8$. The two cases prove Theorem 1.2. $\square$

<a id="composition"></a>

### 5.2. Odd-inner-index composition

<a id="lem-composition"></a>
**Lemma 5.1.** For $A,m,n\in\mathbb Z_{\ge0}$ with $n$ odd,

$$
F_{mn}(A)=F_m(F_n(A)).
\qquad \text{(5.1)}
$$

**Proof.** With $\alpha,\beta$ from Section 2, the numbers $\alpha^n,\beta^n$ have sum $2F_n(A)$ and product $-1$. Their symmetric power sums therefore satisfy (1.1) with parameter $F_n(A)$. Formula (2.4) and the initial values prove (5.1). $\square$

For even $n$, their product is $+1$, giving a different recurrence. For example, $F_4(2)=161$, whereas $F_2(F_2(2))=163$. The parity guard in Lemma 5.1 is essential.

<a id="proof-main"></a>

### 5.3. Proof of Theorem 1.1

The even case follows from Theorem 1.3. Suppose $N$ is odd, and choose $p\in\{17,41\}$ dividing $N$. Write $N=pm$, so $m$ is odd. Put $B=F_m(A)$. Equation (2.7) gives $B\equiv2\pmod4$, while Lemma 5.1 gives

$$
F_N(A)=F_p(B).
\qquad \text{(5.2)}
$$

Theorem 1.2 applied to $B$ excludes a shifted square. $\square$

The residue split in this argument belongs to the new parameter $B$, not to the original $A$ alone. The complete dependency route is summarised below.

**Table 5.** Proof branches for Theorem 1.1, assuming $17\mid N$ or $41\mid N$.

| Branch | Reduction | Final obstruction |
|:---|:---|:---|
| $N$ positive and even | No composition | Theorem 1.3 |
| $N=pm$ odd | $B=F_m(A)$, $B\equiv2\pmod4$ | Split $B\bmod8$ |
| $B\equiv6\pmod8$ | $p\equiv1\pmod4$ | Nonsquare modulo $8$ |
| $B\equiv2\pmod8$ | $x=2B\equiv4\pmod{16}$ | Theorem 3.2 and the fixed certificate |

For example, $A=6$ and $N=51=17\cdot3$ are not rejected by the original modulo-$8$ test: $F_{51}(6)-1\equiv1\pmod8$. Composition instead gives

$$
F_{51}(6)=F_{17}(882),
\qquad 882=F_3(6)\equiv2\pmod8,
$$

so the composed parameter enters the hard fixed-$17$ theorem. Two fixed indices control infinitely many indices because the inner iterate remains in the same parameter family. The even branch is a separate valuation argument.

<a id="pell"></a>

## 6. Pell coordinates and the powerful-number application

<a id="pell-coordinate"></a>

### 6.1. Proof of Corollary 1.4

Let $\varepsilon=u+v\sqrt K$ satisfy (1.6). Its norm is $-1$, and

$$
\varepsilon^2=2u\varepsilon+1.
$$

Taking coefficients of $1$ in its powers gives $X_0=1$, $X_1=u$ and $X_{n+2}=2uX_{n+1}+X_n$. Therefore

$$
X_n=F_n(u).
\qquad \text{(6.1)}
$$

Theorems 1.1 and 1.3 prove Corollary 1.4. $\square$

The transfer uses an equality of coefficients. If a Diophantine construction also gives $X_n=y^2+1$, it must be the same coefficient of the same unit power that is identified with that square expression.

<a id="source-normal-form"></a>

### 6.2. The complete negative-Pell normal form

We now establish the normal form used in Corollary 1.5. Suppose its hypotheses on $X$ hold. Every powerful integer has a unique representation $K^3V^2$ with $K$ squarefree: put into $K$ exactly the primes whose exponents are odd, then absorb the remaining even exponents into $V^2$. No coprimality condition between $K$ and $V$ is imposed. Equation (1.7) follows. It has $K>1$, since $X^2+1$ is not an integer square for $X\ge1$.

Since $X\equiv2\pmod8$, both $K,V$ are odd and

$$
K\equiv K^3V^2=X^2+1\equiv5\pmod8.
\qquad \text{(6.2)}
$$

In particular, $K$ is nonsquare. The element

$$
\eta=X+KV\sqrt K
$$

is a unit of the order $\mathbb Z[\sqrt K]$, with norm $-1$.

We work in the order $\mathbb Z[\sqrt K]$, not in the maximal order of $\mathbb Q(\sqrt K)$. This choice retains the integral coefficients in the Pell equation; using a generator from a larger order could change the exponent being discussed.

For completeness, the positive real units of this order are generated by a least unit $\varepsilon>1$. Such a least unit exists: units in any bounded real interval $1<w\le M$ have bounded integral coefficients, because their conjugates are $\pm w^{-1}$. There are therefore only finitely many in that interval. For any positive unit $w>1$, choose an integer $n\ge0$ with

$$
1\le w\varepsilon^{-n}<\varepsilon.
$$

The quotient is still a unit of the order. Minimality forces it to equal $1$. Thus $w=\varepsilon^n$, uniquely. Because a norm-minus-one unit exists, $N(\varepsilon)$ must be $-1$; otherwise all its powers would have norm $+1$.

Write $\varepsilon=u+v\sqrt K$. Since its conjugate is $-\varepsilon^{-1}$,

$$
u=\frac{\varepsilon-\varepsilon^{-1}}2>0,
\qquad
v=\frac{\varepsilon+\varepsilon^{-1}}{2\sqrt K}>0.
$$

These are integers because $\varepsilon$ belongs to the order, and $u^2+1=Kv^2$. The unit $\eta$ is therefore a unique positive odd power $\varepsilon^N$, giving (1.8). Reduction modulo $8$ supplies the phase of the generator. If $v$ were even, $Kv^2-1$ would be $3$ or $7$ modulo $8$, not a square. Hence $v$ is odd, and

$$
\begin{gathered}
u^2\equiv K-1\equiv4\pmod8,\\
u\equiv2\pmod4.
\end{gathered}
\qquad \text{(6.3)}
$$

Finally, $X-1$ is a square, so $X=y^2+1$ for an integer $y$. Taking the coefficient of $1$ in (1.8), and using (6.1), gives the exact same-centre identity

$$
y^2+1=X=F_N(u).
\qquad \text{(6.4)}
$$

Theorem 1.1 now implies $17\nmid N$ and $41\nmid N$.

<a id="rank"></a>

### 6.3. The divisibility rank and the three sectors

It remains to justify $R\mid N$, rather than merely assume an exponent factorisation. Write

$$
\varepsilon^n=a_n+b_n\sqrt K.
$$

In the binomial expansion, every term contributing to $b_n$ beyond the first contains a factor $K$. Thus, for $n\ge1$,

$$
b_n\equiv n u^{n-1}v\pmod K.
\qquad \text{(6.5)}
$$

The norm equation implies $\gcd(u,K)=1$. Cancelling $u^{n-1}$ modulo $K$ and then cancelling the greatest common divisor gives

$$
\begin{aligned}
K\mid b_n
&\quad\Longleftrightarrow\quad K\mid nv\\
&\quad\Longleftrightarrow\quad
\frac{K}{\gcd(K,v)}\mid n.
\end{aligned}
\qquad \text{(6.6)}
$$

Therefore $R=K/\gcd(K,v)$ is precisely the least positive index at which the coefficient of $\sqrt K$ is divisible by $K$. In (1.8), $b_N=KV$, so $R\mid N$. As $R\mid K$ and $N$ is odd, both $R$ and $E=N/R$ are odd. Combined with (6.4), this proves every assertion of Corollary 1.5. $\square$

For comparison with the usual norm-one Pell rank, $\varepsilon^2$ is the least norm-one unit greater than $1$. Its second coefficient is $2uv$. Because $K$ is odd and $\gcd(u,K)=1$,

$$
\frac{K}{\gcd(K,2uv)}
=\frac{K}{\gcd(K,v)}=R.
\qquad \text{(6.7)}
$$

Thus the rank is the same in the norm-one normalisation. This also explains the relation $R\mid K$ without leaving the article.

The full exponent $N$ measures the number of fundamental-unit steps; $R$ is the first index at which the second coefficient is divisible by $K$; and $E=N/R$ is the remaining multiplier. These are distinct integers. The three stated exclusions concern the same full exponent:

$$
\begin{gathered}
17\mid E\Rightarrow17\mid N,\\
41\mid E\Rightarrow41\mid N,\\
41\mid R\Rightarrow41\mid N.
\end{gathered}
\qquad \text{(6.8)}
$$

In the terminology of the application, $E$ is the outer exponent. Thus the first condition excludes outer exponents divisible by $17$, while the next two exclude an outer exponent or a divisibility rank divisible by $41$. A divisor of $K$ need not divide $R$ or $E$; its membership in the rank is controlled by (6.6). No assertion that these sectors cover every possible exponent is used.

<a id="jacobi-formal"></a>

## 7. The integer-Jacobi certificate and formal realisation

<a id="jacobi"></a>

### 7.1. The uniform character identity

For a positive odd integer $q=\prod_\ell\ell^{a_\ell}$, we use

$$
\begin{gathered}
J(c,q)=\prod_{\ell\mid q}\left(\frac{c}{\ell}\right)^{a_\ell},\\
J(c,1)=1,
\end{gathered}
$$

where the factors are Legendre symbols. If $q$ is a square and $\gcd(c,q)=1$, every exponent is even and $J(c,q)=1$. Our construction gives the opposite sign for one fixed polynomial numerator throughout the parameter progression.

<a id="prop-jacobi"></a>
**Proposition 7.1 (Jacobi certificate).** For $p\in\{17,41\}$, let $U_p$ be given by (4.4) or (4.7)–(4.8). For every $A\in\mathbb Z_{\ge0}$ with $A\equiv2\pmod8$,

$$
J\left(U_p(2A),F_p(A)-1\right)=-1.
\qquad \text{(7.1)}
$$

The denominator is positive and odd, and is coprime to the numerator.

**Proof.** Put $x=2A$ and

$$
Q=\frac{g_p(x)}2=F_p(A)-1.
\qquad \text{(7.2)}
$$

Positivity follows from $A\ge2$ and the recurrence; oddness follows from (2.7). At an odd rational prime $\ell\mid Q$, equation (3.5) gives a unique supporting degree-one prime $\mathfrak P$. The norm calculation, now without a square assumption, gives

$$
v_{\mathfrak P}(\delta_x)=v_\ell(Q).
$$

Reduction modulo $\mathfrak P$ sends $\theta_p$ to $x$, so

$$
b_p=\theta_pU_p(\theta_p)
\equiv xU_p(x)\pmod{\mathfrak P}.
$$

As $b_p$ is a unit at every odd place, this residue is nonzero. Formula (3.7) gives

$$
\prod_{\substack{\mathfrak P\ \mathrm{finite}\\\mathfrak P\nmid2}}
(\delta_x,b_p)_{\mathfrak P}
=J(xU_p(x),Q).
\qquad \text{(7.3)}
$$

In particular, the character has a coprime numerator.

Write $x=4m$. The parameter class gives $m\equiv1\pmod4$. Since $g_p(0)=-2$,

$$
Q=\frac{g_p(4m)}2\equiv-1\pmod m.
$$

Thus $\gcd(m,Q)=1$. Quadratic reciprocity gives

$$
J(m,Q)=J(Q,m)=J(-1,m)=1.
$$

For $m=1$ use the convention $J(a,1)=1$. Since $J(4,Q)=1$, equation (7.3) becomes the exact bridge

$$
\boxed{
\prod_{\substack{\mathfrak P\ \mathrm{finite}\\\mathfrak P\nmid2}}
(\delta_x,b_p)_{\mathfrak P}
=J(U_p(x),Q).
}
\qquad \text{(7.4)}
$$

The real symbol is $+1$, and the dyadic product is $-1$ by (3.8)–(3.10) and (4.12). These arguments do not require $Q$ to be a square. Reciprocity therefore makes the odd product, and hence the right side of (7.4), equal to $-1$. $\square$

The hard-phase exclusion follows immediately: a positive square denominator coprime to the numerator has Jacobi symbol $+1$. Proposition 7.1 is the integer form of the obstruction, rather than a numerical check on it.

<a id="local-consequence"></a>

### 7.2. What the character says locally

Factoring the Jacobi symbol gives a useful interpretation without adding a local-solubility claim. If

$$
Q=\prod_{\ell\mid Q}\ell^{a_\ell},
$$

then Proposition 7.1 implies that at least one odd prime $\ell$ satisfies

$$
a_\ell\text{ odd},\qquad
\left(\frac{U_p(2A)}{\ell}\right)=-1.
\qquad \text{(7.5)}
$$

Consequently $Q$ is not a square in $\mathbb Q_\ell$, and the integer square equation fails modulo $\ell^{a_\ell+1}$. The obstructing prime need not be the same for different $A$. The uniform content is the fixed polynomial certificate (7.1), not the absence of local obstructions at individual specialisations.

At the reference for $p=17$, the factor $13$ in (4.6) already has odd valuation. At the reference for $p=41$, the modulo-$23$ check in Section 2 supplies another immediate obstruction. Neither observation replaces the argument for every parameter.

<a id="verification"></a>

### 7.3. Formal arithmetic and finite computation

A separate Lean development proves the recurrence exclusions by exact polynomial pseudo-remainder identities and Jacobi-symbol transfer [8]. Clearing denominators in polynomial division is only part of that argument: signs, specialised common factors and endpoint conditions are also tracked before the character identities are composed.

For degree $17$, the integer detector is $U_{17}(2A)$. For degree $41$, the main integer chain uses the positive orientation $-U_{41}(2A)$ on $A=8j+10$. This changes no character because $Q\equiv1\pmod8$ and hence $J(-1,Q)=1$. The endpoint $A=2$ is handled separately in that formal proof by $F_{41}(2)-1\equiv20\pmod{23}$. The Hilbert proof and Proposition 7.1 include the endpoint directly.

Proposition 7.1 is therefore an arithmetic consequence of the number-field proof; the uniform degree-$41$ statement and its formal endpoint argument have the distinct proof paths described above. The formalisation establishes the recurrence exclusions and their propagation, not global Hilbert reciprocity. Section 6 supplies the human proof of the Pell normal form and its divisibility rank. Appendix B records the precise correspondence with the formal development.

The standalone verifier in Appendix C checks the polynomial identities, maximality certificates, unit resultants and reference characters. The proofs in Appendix A then determine the dyadic prime types and the required symbol products, without a direct dyadic Hilbert-symbol routine. The common criterion is what turns this finite arithmetic into an exclusion for every admissible parameter. Replaying the calculation verifies fixed certificate data; it does not replace an unbounded theorem with a bounded search. The Hilbert and Jacobi proofs use the same source polynomials and detector coefficients, so their different architectures do not constitute independently discovered certificates.

<a id="conclusion"></a>

## 8. Mathematical scope

The fixed-field certificates exclude shifted squares at indices $17$ and $41$, uniformly for $A\equiv2\pmod4$. Odd-inner-index composition extends these exclusions to odd multiples, while the exact valuation excludes every positive even index independently. The same unit data produce the unconditional Jacobi certificate (7.1).

For the family in Corollary 1.5, the conclusion restricts the full Pell exponent and its divisibility rank. It excludes the stated exponent-divisibility cases but does not classify the remaining odd exponents. The result is a uniform obstruction within the specified square-middle family, not a construction of detecting units at every prime index or an exclusion of all consecutive powerful triples.

<a id="reference-arithmetic"></a>

## Appendix A. Reference arithmetic for the finite certificates

<a id="reference-characters"></a>

### A.1. Reference characters

The recurrences (2.1) and the complete detector definitions (4.4), (4.7)–(4.8) specify all polynomial coefficients exactly. Table 3 records the maximal-order inputs; Table 4 records the dyadic inputs. The following rational-prime data establish the reference product without a direct dyadic Hilbert-symbol calculation.

For each field let $H_p=g_p(4)/2$, and factor it as in (4.6) or (4.10). All factors displayed below are distinct primes. The unique supporting prime over each factor has residue degree one by (3.5), and valuation one on $\delta_4$. The local residue of $b_p$ is $4U_p(4)$.

**Table A1.** Exact odd-prime characters at the reference.

| $p$ | Prime factor $\ell$ of $H_p$ | $v_\ell(H_p)$ | $\left(\frac{4U_p(4)}{\ell}\right)$ |
|:---:|:---:|:---:|:---:|
| $17$ | $13$ | $1$ | $-1$ |
| $17$ | $1751444197$ | $1$ | $+1$ |
| $41$ | $79$ | $1$ | $+1$ |
| $41$ | $1373$ | $1$ | $-1$ |
| $41$ | $115471$ | $1$ | $-1$ |
| $41$ | $1506563$ | $1$ | $-1$ |
| $41$ | $1344905911$ | $1$ | $+1$ |

The odd product is $-1$ in either field. The real and complex factors are $+1$, so reciprocity recovers the dyadic product $-1$ independently of the ordering of the local rows. Individual dyadic signs are stronger finite data than this product calculation requires.

For complete reference values,

$$
\begin{aligned}
g_{17}(4)&=45537549122,\\
g_{41}(4)&=50755107359004694554823202.
\end{aligned}
\qquad \text{(A.1)}
$$

The finite-field irreducibility witnesses, polynomial discriminants, resultant identities, prime factorisations and character signs are exact integer or finite-field calculations. The next subsection reduces maximality and the dyadic valuation data to polynomial arithmetic as well.

<a id="index-certificate"></a>

### A.2. Maximality and dyadic prime structure

We give an explicit certificate that the generator in each field has index one. Let a monic irreducible polynomial $f$ factor modulo a prime $\ell$ as $\prod_i\bar f_i^{e_i}$. Choose monic integral lifts $f_i$ and write

$$
f=\prod_i f_i^{e_i}+\ell H.
$$

Dedekind's index criterion states that $\ell$ does not divide the power-order index exactly when no repeated factor $\bar f_i$ divides $\bar H$ [10, Theorem 1.1]. This tests maximality before any prime-ideal decomposition is inferred from reduction modulo $\ell$.

For our two polynomials, the discriminants in Table 3 show that only $2$ and $p$ can divide the index. At $2$, define

$$
\begin{aligned}
\phi_{17}(T)&=T^4+T+1,\\
\psi_{17}(T)&=T^4+T^3+T^2+T+1,\\
\phi_{41}(T)&=T^{10}+T^8+T^7+T^4\\
&\qquad{}+T^3+T+1,\\
\psi_{41}(T)&=T^{10}+T^9+T^4+T+1.
\end{aligned}
\qquad \text{(A.2)}
$$

Their reductions are distinct irreducible polynomials over $\mathbb F_2$, all with constant term $1$, and direct polynomial arithmetic gives

$$
g_p(T)\equiv T\phi_p(T)^2\psi_p(T)^2\pmod2.
\qquad \text{(A.3)}
$$

For the integral polynomial

$$
H_{p,2}(T)=\frac{g_p(T)-T\phi_p(T)^2\psi_p(T)^2}{2},
$$

the remainder of $\overline{H}_{p,2}$ on division by $\bar\phi_p\bar\psi_p$ is $1$ in both cases. Thus neither repeated factor divides the correction, and $2$ does not divide the index.

At the odd prime $p$, direct reduction gives

$$
g_p(T)\equiv(T-2)^p\pmod p.
\qquad \text{(A.4)}
$$

The correction $(g_p(T)-(T-2)^p)/p$ evaluated at $T=2$ has residues

$$
\frac{g_{17}(2)}{17}\equiv12\pmod{17},
\qquad
\frac{g_{41}(2)}{41}\equiv26\pmod{41}.
\qquad \text{(A.5)}
$$

Both are nonzero. Dedekind's criterion therefore excludes $p$ from the index. No other index prime is possible, so $\mathcal O_{L_p}=\mathbb Z[\theta_p]$.

Dedekind–Kummer now applies to (A.3) [11, Theorem 6.14]. With $h=(p-1)/4$, it yields the three dyadic prime types $(e,f)=(1,1),(2,h),(2,h)$. The prime corresponding to $T$ is the only dyadic prime dividing $\theta_p$. Its residue degree is one, and $N(\theta_p)=2$ forces $v_{\mathfrak P}(\theta_p)=1$ there. Since $v_{\mathfrak P}(4)=2$, it also has $v_{\mathfrak P}(4-\theta_p)=1$. At the other two primes, $\theta_p$ and $4-\theta_p$ are units. Finally $(b_p)=(\theta_p)$ supplies the last valuation column of Table 4.

This establishes the dyadic valuations and strict Hensel inequalities without computing local Hilbert symbols. Combined with Appendix A.1, it certifies every finite hypothesis of Theorem 3.2 using polynomial and rational-integer arithmetic.

<a id="verification-concordance"></a>

## Appendix B. Compact proof and verification concordance

**Table B1.** Mathematical results and their proof roles.

| Article result | Mathematical proof | Accompanying verification |
|:---|:---|:---|
| Theorem 1.3 | Doubling and valuation in Section 2 | Lean recurrence proof |
| Theorem 3.2 | Norm, support, local symbols and reciprocity | Human number-field proof |
| Theorem 4.2 | Theorem 3.2 with Tables 3–4 | Fixed-field exact arithmetic; separate integer proofs |
| Theorem 1.1 | Odd composition and the even theorem | Lean propagation proof |
| Corollary 1.4 | Coefficient identity (6.1) | Lean Pell-coordinate corollaries |
| Corollary 1.5 | Normal form, phase and rank in Section 6 | Source-theorem and rank concordance; human exposition here |
| Proposition 7.1 | Equation (7.4) and reciprocity | Jacobi chains with the degree-$41$ endpoint distinction |

The principal all-positive formal theorem is

```text
Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_index_factor
```

The exact valuation and free-even theorem are

```text
Erdos364.sm2LucasReal_sub_one_padicVal_two_of_positive_even
Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_even_index
```

The separate formal development [8] also contains the fixed-$17$ and fixed-$41$ declarations, the Pell corollaries and the application adapters. Its recorded axiom audit uses `propext`, `Classical.choice` and `Quot.sound`. No Lean formalisation of Theorem 3.2 or of the new exposition of Corollary 1.5 is asserted here. The finite verifier below is independent of that formal build and contains all the numerical inputs consumed by the human proof.

<a id="standalone-verifier"></a>

## Appendix C. A compact exact-arithmetic verifier

The following Python program reconstructs $g_p$ and $U_p$ from the recurrences and coefficients printed in the article. It checks the irreducibility witnesses, polynomial discriminants, unit resultants, both parts of the maximality certificate in Appendix A.2, and the reference factorisations and quadratic characters in Appendix A.1. Together with the arguments there, these are all the finite inputs required by the human proof. The individual dyadic Hilbert signs in Table 4 are corroborating data and are not recomputed by this program.

Save the listing as `verify_fixed_fields.py` and run `python verify_fixed_fields.py` in an environment with SymPy 1.14.0 [9]. A successful run ends with `FIXED_FIELDS_OK`; a failed check raises an exception and gives a nonzero process exit status. The program uses exact polynomial, integer and finite-field arithmetic. It neither constructs a class group or a unit-group basis nor searches through parameter values.

The listing is also supplied as a separate source file. It makes the proof-critical finite inputs reproducible independently of the separately released Lean archive [8]. The arithmetic software remains a computational dependency; the implications from its finite outputs to the quantified theorems are proved in the article.

```python
"""Exact finite certificate for the 17/41 paper.

Run: python verify_fixed_fields.py
Reference environment: Python 3.11+ and SymPy 1.14.0.
No bounded parameter search or number-field class-group routine is used.
"""
from __future__ import annotations

import sympy as sp

T = sp.Symbol("T")
C17 = [-1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, -2, 0, 1]
C41 = [
    -1, -15, 2, 4, 8, 7, -8, -10, -3, 6, 7, 3, -1, -9,
    3, 7, 2, 3, -9, -6, 1, 8, 4, 1, -4, -6, 3, 7, 0, 2,
    -7, -4, 1, 6, -1, 0, -2, -5, 4, 5, -5,
]
DATA = {
    17: (
        C17, 67, T**4 + T + 1,
        T**4 + T**3 + T**2 + T + 1,
        [13, 1751444197], [-1, 1], 532303029, 12,
    ),
    41: (
        C41, 163, T**10 + T**8 + T**7 + T**4 + T**3 + T + 1,
        T**10 + T**9 + T**4 + T + 1,
        [79, 1373, 115471, 1506563, 1344905911],
        [1, -1, -1, -1, 1], -43956715453803235217163523, 26,
    ),
}


def require(condition: object, label: str) -> None:
    if not bool(condition):
        raise ArithmeticError(label)


def modpoly(expr: object, prime: int) -> sp.Poly:
    return sp.Poly(expr, T, modulus=prime)


def verify(p: int) -> None:
    c, aux, phi, psi, factors, signs, u4, residue = DATA[p]
    d = [sp.Poly(2, T), sp.Poly(T, T)]
    for _ in range(2, p + 1):
        d.append(sp.Poly(T, T) * d[-1] + d[-2])
    g = d[p] - 2
    u = sp.Poly(c[0], T)  # c[0] multiplies 1, not D_0.
    for k in range(1, len(c)):
        u += c[k] * d[k]

    require(modpoly(g, aux).is_irreducible, "irreducibility")
    require(g.degree() == p and g.LC() == 1, "monic degree")
    require(g.eval(0) == -2, "constant term and theta norm")
    disc = 2 ** (3 * (p - 1) // 2) * p**p
    require(g.discriminant() == disc, "polynomial discriminant")
    require(sp.resultant(g, u) == -1, "unit resultant")

    # Dedekind's index criterion at 2.
    f2, h2 = modpoly(phi, 2), modpoly(psi, 2)
    require(f2.is_irreducible and h2.is_irreducible, "dyadic factors")
    require(f2 != h2, "distinct dyadic factors")
    require(f2.degree() == (p - 1) // 4, "first residue degree")
    require(h2.degree() == (p - 1) // 4, "second residue degree")
    lifted = sp.Poly(T * phi**2 * psi**2, T)
    difference = g - lifted
    require(all(a % 2 == 0 for a in difference.all_coeffs()), "mod 2")
    correction = sp.Poly(difference.as_expr() / 2, T, domain=sp.ZZ)
    remainder = modpoly(correction, 2).rem(f2 * h2)
    require(remainder == modpoly(1, 2), "2-maximality")

    # The only other possible index prime is p.
    difference = g - sp.Poly((T - 2)**p, T)
    require(all(a % p == 0 for a in difference.all_coeffs()), "mod p")
    value = int(g.eval(2))
    require(value % p == 0, "integral odd correction")
    require((value // p) % p == residue != 0, "p-maximality")

    # Rational-prime reference data recover the dyadic product.
    H = int(g.eval(4)) // 2
    require(int(g.eval(4)) % 2 == 0 and H % 8 == 1, "reference phase")
    require(len(set(factors)) == len(factors), "distinct factors")
    require(all(sp.isprime(q) for q in factors), "proven reference primes")
    require(sp.prod(factors) == H, "reference factorisation")
    require(u.eval(4) == u4, "unit reference value")
    actual = [int(sp.legendre_symbol(4 * u4, q)) for q in factors]
    require(actual == signs and sp.prod(signs) == -1, "reference signs")
    require(sp.jacobi_symbol(u4, H) == -1, "reference Jacobi symbol")
    print(f"p={p}: polynomial, index and reference checks passed")


if __name__ == "__main__":
    print(f"SymPy {sp.__version__}")
    for prime in (17, 41):
        verify(prime)
    print("FIXED_FIELDS_OK")
```

## Acknowledgements

AI assistants (Anthropic Claude and OpenAI ChatGPT/Codex) were used for drafting and editing prose, challenging arguments, writing and running verifiers, and repository engineering. All mathematical statements, proofs and publication decisions were reviewed by the author, who takes sole responsibility for them.

## References

<a id="ref-1"></a>
**[1]** A. Bremner and N. Tzanakis. *Lucas sequences whose 12th or 9th term is a square*. Journal of Number Theory **107** (2004), 215–227. [Author preprint, arXiv:math/0405306](https://arxiv.org/abs/math/0405306).

<a id="ref-2"></a>
**[2]** M. A. Bennett, S. R. Dahmen, M. Mignotte and S. Siksek. *Shifted powers in binary recurrence sequences*. Mathematical Proceedings of the Cambridge Philosophical Society **158** (2015), 305–329. [Published article](https://doi.org/10.1017/S0305004114000681).

<a id="ref-3"></a>
**[3]** M. A. Bennett, V. Patel and S. Siksek. *Shifted powers in Lucas–Lehmer sequences*. Research in Number Theory **5** (2019), Article 15. [Author preprint, arXiv:1811.10889](https://arxiv.org/abs/1811.10889).

<a id="ref-4"></a>
**[4]** T. H. Chan. *A note on three consecutive powerful numbers*. Integers **25** (2025), A7. [Published article](https://math.colgate.edu/~integers/z7/z7.pdf).

<a id="ref-5"></a>
**[5]** J. S. Milne. *Class Field Theory*, version 4.03 (2020). Chapter III, §4, for the Hilbert pairing; Chapter VIII, §5, item 5.10, for reciprocity. [Author's notes](https://www.jmilne.org/math/CourseNotes/CFT.pdf).

<a id="ref-6"></a>
**[6]** G. Oh. *Algebraic Number Theory*. Columbia University course notes, Spring 2024. Theorem 16.32, for the non-dyadic Hilbert-symbol formula. [Course notes](https://www.math.columbia.edu/~gyujinoh/Spring2024/ANT.pdf).

<a id="ref-7"></a>
**[7]** K. Conrad. *Hensel's Lemma*. Theorem 9.1, for strong Hensel over a complete nonarchimedean field. [Author's notes](https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf).

<a id="ref-8"></a>
**[8]** C. G. A. Loveday. *Fixed-field certificates and integer-Jacobi formal proofs for the 17/41 shifted-square obstruction*. Software, data and Lean development, version 1.0.0 (11 September 2026). Public release: <https://github.com/CheyLoveday/erdos-364-shifted-squares/releases/tag/v1.0.0>. Section 7 and Appendix B specify the mathematical statements and their formal correspondence.

<a id="ref-9"></a>
**[9]** A. Meurer et al. *SymPy: symbolic computing in Python*. PeerJ Computer Science **3** (2017), e103. [Published article](https://doi.org/10.7717/peerj-cs.103). The verifier uses SymPy 1.14.0.

<a id="ref-10"></a>
**[10]** X. Vidaux and C. R. Videla. *Dedekind's criterion for the monogenicity of a number field versus Uchida's and Lüneburg's*. arXiv:1809.04122 (2018), Theorem 1.1. [Author preprint](https://arxiv.org/abs/1809.04122).

<a id="ref-11"></a>
**[11]** A. V. Sutherland. *Ideal norms and the Dedekind–Kummer theorem*. MIT 18.785, Lecture 6 (2021), Theorem 6.14. [Course notes](https://math.mit.edu/classes/18.785/2021fa/LectureNotes6.pdf).

<a id="ref-12"></a>
**[12]** J. She. *Nonexistence of consecutive powerful triplets around cubes with prime-square factors*. arXiv:2507.16828v3 (2025). [Author preprint](https://arxiv.org/abs/2507.16828v3).

<a id="ref-13"></a>
**[13]** W. Ma. *An elementary note on three consecutive powerful numbers*. arXiv:2608.23418 (2026). [Author preprint](https://arxiv.org/abs/2608.23418).
