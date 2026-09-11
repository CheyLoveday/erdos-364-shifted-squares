---
title: "One candidate, several arithmetic constraints"
subtitle: "The 17/41 shifted-square obstruction, explained through the mathematics"
lang: en-GB
---

## The idea in one paragraph {#overview}

A possible solution has to be the **same integer in every description**. In the family studied here, one description says that an integer $X$ is one more than a square. Another says that it is a particular coefficient in a power of a quadratic unit. That coefficient is a term of a recurrence. Elementary arithmetic excludes some recurrence indices immediately. For two other sets of indices, an explicit algebraic construction forces a sign incompatible with the square requirement. The proof comes from making these descriptions meet, not from checking larger and larger integers. The human–AI workflow has a separate role: proposing arguments, recording their assumptions and making their checks reproducible.

This guide explains the published version 1.0.0 article, *Shifted-square obstructions at indices divisible by 17 or 41 in a family of Lucas sequences*, released 11 September 2026, with mathematical content frozen 10 September 2026. Article references below use that version's theorem numbers. It does not extend the mathematical scope or use the earlier infographic as a proof source. Worked examples illustrate the article; the final section describes the engineering strategy separately from the mathematics.

## 1. Start with three consecutive integers {#powerful}

An integer is **powerful** when every prime that divides it occurs at least twice in its prime factorisation. For example,

$$
25=5^2,
\qquad
27=3^3,
\qquad
72=2^3\cdot3^2
$$

are powerful. But $26=2\cdot13$ is not: both its prime factors occur only once. Thus $25,26,27$ illustrate two powerful numbers separated by a non-powerful middle, not a powerful triple.

The three-consecutive problem asks whether there can be an integer $M$ for which $M-1$, $M$ and $M+1$ are all powerful. This paper considers an application within the **square-middle** case,

$$
(X^2-1,\ X^2,\ X^2+1).
$$

Here $X$ is the square root of the middle integer. The middle integer is $X^2$, not $X$. Every prime exponent in $X^2$ is even, so the middle is automatically powerful. Both neighbours must still satisfy their own powerfulness conditions.

The particular family used in Paper I has the additional requirements

$$
X\ge2,\qquad X\equiv2\pmod8,
\qquad X-1=y^2
$$

for an integer $y$. The congruence means that $X$ leaves remainder $2$ on division by $8$. This family is a restricted part of the square-middle problem, not a description of every possible square-middle triple.

The square condition gives the first description of the candidate:

$$
\boxed{X=y^2+1.}
$$

The paper obtains a restriction even without assuming that the lower neighbour $X^2-1$ is powerful. That lower-neighbour requirement would impose a further constraint on an actual triple.

*Article: §1.1 and Corollary 1.5.*

## 2. The upper neighbour gives a second description {#upper-neighbour}

Every powerful positive integer can be written uniquely as

$$
K^3V^2,
$$

where $K$ is **squarefree**, meaning that no prime occurs more than once in $K$, and $V$ is a positive integer. Put into $K$ exactly the primes whose original exponents are odd. Each such exponent is at least three, so removing the cube leaves an even exponent for $V^2$.

There is no requirement that $K$ and $V$ be coprime. For instance, $32=2^3\cdot2^2$ has $K=V=2$.

If the upper neighbour is powerful, write

$$
X^2+1=K^3V^2.
$$

The same equality can be rearranged as

$$
X^2-K(KV)^2=-1.
$$

This is a **negative Pell equation**: an equation of the form $a^2-Kb^2=-1$ in integer coefficients $a,b$. Here its coefficients are exactly $a=X$ and $b=KV$.

Introduce

$$
\eta=X+KV\sqrt K.
$$

Its conjugate is $X-KV\sqrt K$, and their product is

$$
\operatorname{Norm}(\eta)
=(X+KV\sqrt K)(X-KV\sqrt K)=-1.
$$

The norm packages the Pell equation into multiplication. An element of norm $-1$ has an inverse with integer coefficients in the same quadratic arithmetic, so it is a **unit**.

Under the paper's hypotheses, $K>1$ and $K\equiv5\pmod8$. The paper proves that there is a least unit greater than $1$,

$$
\varepsilon=u+v\sqrt K,
\qquad
u^2+1=Kv^2,
$$

in the order $\mathbb Z[\sqrt K]$. That order is the set of all expressions $a+b\sqrt K$ with integer $a,b$. Its positive units are powers of $\varepsilon$. Consequently,

$$
\eta=\varepsilon^N
$$

for a unique positive odd integer $N$. Oddness follows because $\varepsilon$ and $\eta$ both have norm $-1$: an even power would have norm $+1$.

This choice of order matters. Using a generator from a larger ring could change the exponent. The proof retains the integer coefficients of the original Pell equation.

*Article: §6.2, especially equations (6.2)–(6.4).*

## 3. Multiplying a unit produces the recurrence {#recurrence}

Write the powers of the unit as

$$
\varepsilon^n=X_n+Y_n\sqrt K.
$$

The integers $X_n$ and $Y_n$ are its two coefficients. In particular, $X_n$ is **not** the real value of the whole expression $\varepsilon^n$.

The equation $u^2+1=Kv^2$ gives

$$
\varepsilon^2=2u\varepsilon+1.
$$

Multiplying by $\varepsilon^n$ and comparing the coefficients of $1$ produces

$$
X_{n+2}=2uX_{n+1}+X_n,
\qquad X_0=1,\quad X_1=u.
$$

This motivates the family of sequences

$$
\begin{gathered}
F_0(A)=1,\qquad F_1(A)=A,\\
F_{n+2}(A)=2AF_{n+1}(A)+F_n(A).
\end{gathered}
$$

Here $A$ chooses the sequence and $n$ chooses a term within it. The first terms are

$$
\begin{aligned}
F_0(A)&=1, & F_1(A)&=A,\\
F_2(A)&=2A^2+1, & F_3(A)&=4A^3+3A.
\end{aligned}
$$

For $A=2$, this gives $1,2,9,38,161,682,\ldots$. For the Pell unit, $A=u$ and $X_n=F_n(u)$.

The two descriptions of the candidate therefore meet in the exact identity

$$
\boxed{y^2+1=X=F_N(u).}
$$

This is the central intersection. The square witness, Pell coefficient and recurrence term all concern the same $X$.

A worked illustration shows why each condition matters. For $\varepsilon=2+\sqrt5$,

$$
\varepsilon^5=682+305\sqrt5,
\qquad
682^2+1=5^3\cdot61^2.
$$

So $X=682$ has a powerful upper neighbour and $X\equiv2\pmod8$. But $X-1=681$ is not a square: it lies strictly between $26^2=676$ and $27^2=729$. Satisfying the Pell-side condition is not enough; the square-side condition must hold for that very same candidate.

*Article: Corollary 1.4 and §§6.1–6.2. The numerical illustration is obtained by expanding the displayed unit power.*

## 4. What the recurrence theorem actually says {#main-result}

The main theorem is a statement about the whole recurrence family, before any powerful-number application is imposed:

::: {.theorem}
**Main result.** Let $A$ be a nonnegative integer with $A\equiv2\pmod4$, and let $N>0$. If $17\mid N$ or $41\mid N$, then

$$
F_N(A)-1\text{ is not an integer square}.
$$
:::

The notation $17\mid N$ means that $17$ divides $N$. The statement applies to every parameter $A=2,6,10,14,\ldots$, not merely the sequence at $A=2$.

A second theorem excludes **every positive even index**, whether or not it has a factor $17$ or $41$.

These are restrictions, not a classification of all remaining possibilities. For example, $F_1(2)-1=1$ is a square, so removing the index conditions would produce a false theorem.

The primes $17$ and $41$ have two linked roles: they are fixed recurrence indices and the degrees of two number fields used in the proof. They are not asserted to be the odd primes detecting every nonsquare locally.

*Article: Theorems 1.1–1.3.*

## 5. The first obstruction: count factors of two {#even-indices}

A square contains each prime an even number of times. The notation $v_2(m)$ counts the factors of $2$ in a nonzero integer $m$. For example, $40=2^3\cdot5$, so $v_2(40)=3$.

The even-index theorem gives an exact count:

$$
\boxed{v_2(F_N(A)-1)=2v_2(N)+1}
$$

when $A\equiv2\pmod4$ and $N>0$ is even. Its right side is odd, which is incompatible with an integer square.

The reason is a controlled doubling pattern. The recurrence has the identity

$$
F_{2n}(A)=2F_n(A)^2-(-1)^n.
$$

It follows by putting $\alpha=A+\sqrt{A^2+1}$ and $\beta=A-\sqrt{A^2+1}$, observing that $\alpha\beta=-1$, and using $F_n(A)=(\alpha^n+\beta^n)/2$.

For odd $n$, the doubling identity gives

$$
F_{2n}(A)-1=2F_n(A)^2.
$$

Since $F_n(A)\equiv2\pmod4$ at odd indices, its valuation is exactly one. The first doubling therefore gives valuation $1+2=3$.

For even $n$, it instead gives

$$
F_{2n}(A)-1
=2(F_n(A)-1)(F_n(A)+1).
$$

At even indices $F_n(A)\equiv1\pmod4$, so the final factor contributes exactly one further factor of $2$. Each subsequent doubling increases the valuation by two.

Writing $N=2^s m$ with $m$ odd gives one initial valuation of $3$ and $s-1$ further increments of $2$: $3+2(s-1)=2s+1$.

At $A=2$, the shifted terms at indices $2,4,8$ are $8,160,51840$, with valuations $3,5,7$. The proof explains that pattern at every height; it is not an extrapolation from those examples.

*Article: §2.2–§2.3 and Theorem 1.3.*

## 6. Odd indices: what survives at the prime two {#odd-indices}

For odd indices the shifted value is odd. Every odd integer square is $1$ modulo $8$, whereas $5$ modulo $8$ is impossible. Applying the recurrence modulo $8$ gives:

| $A\bmod8$ | $N\bmod4$ | $(F_N(A)-1)\bmod8$ | Outcome at $2$ |
|:---:|:---:|:---:|:---|
| $2$ | $1$ | $1$ | Survives |
| $2$ | $3$ | $5$ | Excluded |
| $6$ | $1$ | $5$ | Excluded |
| $6$ | $3$ | $1$ | Survives |

The surviving rows do more than pass one small test. An odd integer congruent to $1$ modulo $8$ is a square in $\mathbb Z_2$, the ring of $2$-adic integers. This means that its square roots can be chosen consistently through all powers of $2$. Going from modulus $8$ to $16$, $32$ or higher powers cannot eliminate it merely as a nonsquare at $2$.

That does **not** mean it is an integer square, or that it passes every odd-prime test. The article gives

$$
F_{41}(2)-1\equiv20\pmod{23},
$$

and $20$ is not a square residue modulo $23$.

Both fixed indices $17$ and $41$ are $1$ modulo $4$. Thus $A\equiv6\pmod8$ is elementary, while $A\equiv2\pmod8$ is the hard fixed-index phase. The next construction handles that entire parameter class uniformly.

*Article: Proposition 2.1 and §2.4. The complete $2$-adic square criterion uses strong Hensel; see Conrad, Theorem 9.1, also cited in the article.*

## 7. Turn a sequence term into a polynomial norm {#number-field}

The recurrence can be expressed through the Dickson polynomials

$$
\begin{gathered}
D_0(T)=2,\qquad D_1(T)=T,\\
D_{n+2}(T)=TD_{n+1}(T)+D_n(T).
\end{gathered}
$$

Here $T$ is a polynomial variable. Direct comparison gives $D_n(2A)=2F_n(A)$.

Fix $p\in\{17,41\}$ and define

$$
g_p(T)=D_p(T)-2,\qquad x=2A.
$$

Then the square equation becomes

$$
F_p(A)=y^2+1
\quad\Longleftrightarrow\quad
g_p(x)=2y^2.
$$

In the hard phase, $x\ge4$ and $x\equiv4\pmod{16}$.

The polynomial $g_p$ is monic, meaning that its leading coefficient is $1$, and is irreducible over the rationals. It has degree $p$ and constant term $-2$. Adjoin a root $\theta_p$ to the rational numbers to form

$$
L_p=\mathbb Q(\theta_p).
$$

This is a number field: arithmetic in which expressions involving the root are legitimate numbers. Every element can be expressed using rational coefficients and the basis $1,\theta_p,\ldots,\theta_p^{p-1}$.

The payoff is a norm identity. The field norm multiplies the images of an element under all embeddings of the field. If $\theta_1,\ldots,\theta_p$ are the roots of $g_p$, then

$$
\operatorname{Norm}(x-\theta_p)
=\prod_{j=1}^{p}(x-\theta_j)=g_p(x).
$$

The constant term gives $\operatorname{Norm}(\theta_p)=2$. Therefore

$$
\delta_x=\frac{x-\theta_p}{\theta_p}
\quad\Longrightarrow\quad
\operatorname{Norm}(\delta_x)=\frac{g_p(x)}2.
$$

Under a hypothetical solution, this norm is $y^2$. Dividing by $\theta_p$ removes exactly the unwanted factor of two.

The order of subtraction is deliberate. In odd degree, replacing $x-\theta_p$ by $\theta_p-x$ reverses the norm's sign. The proof keeps the orientation that produces the positive square.

*Article: §2.1, §3.3 and §4.1.*

## 8. Why a square norm is not enough {#support}

A product can be a square even when its individual factors are not: $3\cdot12=36$. Likewise, a square field norm does not automatically imply even valuation at every prime of the number field. Contributions from several primes above one rational prime could add up to an even number.

The proof prevents that ambiguity before transferring parity.

The exact field calculations establish

$$
\mathcal O_{L_p}=\mathbb Z[\theta_p],
$$

where $\mathcal O_{L_p}$ is the ring of algebraic integers in the field. In words, every algebraic integer is an integer polynomial in the specified root. The specified root generates the entire integer ring; no additional algebraic integers are missing from its power order.

Temporarily write $g=g_p$ and $\theta=\theta_p$. Imposing the relation $\theta=x$ gives

$$
\mathcal O_L/(x-\theta)
\cong\mathbb Z/(g(x)).
$$

The quotient notation means arithmetic after setting the element in parentheses equal to zero. Once $\theta=x$, its defining equation $g(\theta)=0$ becomes $g(x)=0$.

This identifies exactly one prime ideal $\mathfrak P$ above each rational prime $\ell$ that supports $x-\theta$. Its residue field is $\mathbb F_\ell$, so its residue degree is one. Other primes above $\ell$ may exist; they simply do not divide this particular element.

Since $\theta$ has norm $2$, it is a unit at all odd primes. The norm valuation is therefore concentrated at that single supporting prime:

$$
v_{\mathfrak P}(\delta_x)
=v_\ell(\operatorname{Norm}(\delta_x)).
$$

Here $v_{\mathfrak P}$ counts prime-ideal divisibility, while $v_\ell$ counts rational-prime divisibility. If the norm is $y^2$, the right side is even. At primes outside the support the valuation is zero.

The result is exactly what is needed: **every odd-prime valuation is even**. It is not the stronger, unwarranted assertion that $\delta_x$ is a square in every local field.

*Article: §3.3, equations (3.5)–(3.6).*

## 9. The detector changes a sign without changing the support {#detector}

A unit can be multiplied into an algebraic integer without introducing a new prime-ideal factor. The proof uses that freedom to change a quadratic character.

For each fixed field it supplies an explicit polynomial $U_p$ and forms

$$
u_p=U_p(\theta_p),\qquad b_p=\theta_pu_p.
$$

The subscripted $u_p$ is an algebraic unit in the degree-$p$ field. It is distinct from the integer Pell coefficient $u$ introduced earlier. Also, $U_p$ here names a detector polynomial, not a Lucas $U$-sequence.

Exact computation gives

$$
\operatorname{Res}(g_p,U_p)
=\operatorname{Norm}(u_p)=-1.
$$

The **resultant** is an exact polynomial calculation; for monic $g_p$ it is the product of $U_p$ evaluated at the roots of $g_p$. Norm $-1$ makes $u_p$ a unit. Consequently $b_p$ has the same principal ideal as $\theta_p$, and remains a unit at every odd prime.

For degree $17$, the choice has the compact form

$$
\begin{aligned}
U_{17}(T)={}&-1-D_2(T)+D_3(T)+D_4(T)\\
&-D_5(T)-2D_{12}(T)+D_{14}(T).
\end{aligned}
$$

The degree-$41$ choice has a longer exact coefficient list, printed in article equations (4.7)–(4.8). Its constant coefficient multiplies $1$, not $D_0=2$.

Why not use $b_p=\theta_p$ alone? Proposition 4.1 proves that its dyadic reference product is $+1$. The chosen unit changes that product to $-1$ while preserving odd-prime unitness. This is the specific job of the detector.

Norm $-1$ alone is not the detecting condition. The unit $-1$ also has norm $-1$ in an odd-degree field, but has trivial reference character here. The successful units supply a particular sign, not just a particular norm.

*Article: Proposition 4.1 and §§4.2–4.4.*

## 10. Hilbert reciprocity links the local signs {#reciprocity}

Ordinary real arithmetic is one way to examine a number. Arithmetic organised around divisibility by a prime gives another. A **completion** makes one such notion of closeness into a complete number system. In a number field, the different real, complex and prime-adic viewpoints are called its **places**. Places above $2$ are called **dyadic**.

A quadratic Hilbert symbol attaches a sign to a pair of nonzero numbers at one place:

$$
(a,b)_w\in\{+1,-1\}.
$$

We use $w$ for a place here, to distinguish it from the Pell coefficient $v$. The symbol is a local quadratic compatibility test. In its norm interpretation, $+1$ means that $a$ is a norm from the local quadratic extension obtained by adjoining $\sqrt b$; when $b$ is already a square, the symbol is automatically $+1$. It is not simply a test of whether $a$ itself is a square.

**Hilbert reciprocity** says that when $a,b$ belong to the original number field, all their local signs satisfy

$$
\prod_w(a,b)_w=+1.
$$

The product covers every place. Only finitely many factors differ from $+1$, so it is well-defined. This is a compatibility law for the same pair of global numbers, not a rule saying that locally soluble equations always have a global solution.

Apply the pairing to $(\delta_x,b_p)$. Under the square hypothesis, the odd-prime valuations of $\delta_x$ are even, and $b_p$ is a unit there. The standard odd-prime Hilbert formula then gives $+1$ at every odd finite place.

There is exactly one real embedding in each fixed field. Its distinguished root satisfies $0<\theta_{p,\mathbb R}<2$, while $x\ge4$. Hence

$$
\frac{x-\theta_{p,\mathbb R}}{\theta_{p,\mathbb R}}>0,
$$

which makes the real Hilbert symbol $+1$. Complex Hilbert symbols are automatically $+1$.

Thus a hypothetical square has already forced every non-dyadic sign to be positive. The remaining question is the product of the dyadic signs.

*Article: Proposition 3.1 and §§3.1–3.4. Classical background: Milne, Class Field Theory, Chapter III §4 and Chapter VIII §5.10.*

## 11. Why one reference calculation controls every parameter {#hensel}

A finite calculation at one integer would normally say little about infinitely many others. Here there is a theorem explaining exactly what stays unchanged.

Use the reference $x=4$ and put

$$
\delta_4=\frac{4-\theta_p}{\theta_p}.
$$

For any admissible $x$, direct division gives

$$
\frac{\delta_x}{\delta_4}
=1+\frac{x-4}{4-\theta_p}.
$$

At a dyadic prime $\mathfrak P$, define $e=v_{\mathfrak P}(2)$ and $d=v_{\mathfrak P}(4-\theta_p)$. The valuation is normalised to count one copy of the prime ideal as one. Since $16\mid x-4$,

$$
v_{\mathfrak P}\!\left(\frac{x-4}{4-\theta_p}\right)
\ge4e-d.
$$

The exact field data give $(e,d)=(1,1)$ at one dyadic prime and $(e,d)=(2,0)$ at the other two. Therefore the respective lower bounds are

$$
3>2,
\qquad
8>4,
$$

or, uniformly, $4e-d>2e$.

Strong Hensel's lemma implies that $1+t$ is a local square when $v_{\mathfrak P}(t)>2v_{\mathfrak P}(2)$. To see the threshold, apply the lemma to $f(Z)=Z^2-(1+t)$ at $Z=1$: its value is $-t$, and its derivative is $2$.

The strict inequality matters. In $\mathbb Q_2$, $5=1+4$ lies exactly on the excluded boundary and is not a square. The argument requires divisibility beyond that boundary, not equality with it.

Consequently $\delta_x/\delta_4$ is a square at every dyadic place. Two numbers whose quotient is a square have the same **squareclass**, and Hilbert symbols depend only on squareclasses. Thus

$$
(\delta_x,b_p)_{\mathfrak P}
=(\delta_4,b_p)_{\mathfrak P}
\qquad(\mathfrak P\mid2).
$$

The reference is allowed to be a nonsolution. Its role is to determine the dyadic character shared by the entire progression. When $x=4$ itself, the quotient is exactly $1$, so that endpoint is included too.

*Article: §3.5 and Table 4. Classical background: Conrad, Hensel's Lemma, Theorem 9.1.*

## 12. The finite arithmetic and the final contradiction {#certificate}

The fixed fields have the following certified structure. A signature $(r,s)$ means $r$ real embeddings and $s$ conjugate pairs of complex embeddings, accounting for degree $r+2s$.

| Input | $p=17$ | $p=41$ |
|:---|:---:|:---:|
| Irreducible reduction modulo | $67$ | $163$ |
| Polynomial and field discriminant | $2^{24}17^{17}$ | $2^{60}41^{41}$ |
| Specified power-order index | $1$ | $1$ |
| Signature | $(1,8)$ | $(1,20)$ |
| Dyadic $(e,f)$ types | $(1,1),(2,4),(2,4)$ | $(1,1),(2,10),(2,10)$ |
| Unit norm $\operatorname{Norm}(u_p)$ | $-1$ | $-1$ |
| Dyadic reference product | $-1$ | $-1$ |

The residue degree $f$ describes the size of the local residue field; over $2$ it has $2^f$ elements. The number $e$ is the ramification index, equal here to the valuation of $2$. The sum of the products $ef$ accounts for the field degree.

The **discriminant** is an exact integer associated with the polynomial or field. The square of the power-order index divides the polynomial discriminant, so only $2$ and $p$ could obstruct the assertion that $\mathbb Z[\theta_p]$ is the full ring of integers. Appendix A.2 checks both primes using Dedekind's index criterion. Its polynomial congruences prove index one, and then determine the dyadic prime types and valuations used above. No unsupported maximal-order assumption is hidden inside the argument.

The negative reference product can also be recovered without a direct dyadic-symbol routine. Set

$$
H_p=\frac{g_p(4)}2=\operatorname{Norm}(\delta_4).
$$

For degree $17$,

$$
H_{17}=13\cdot1751444197,
\qquad U_{17}(4)=532303029.
$$

The two odd-prime reference signs are $-1$ and $+1$, giving product $-1$. For degree $41$,

$$
\begin{aligned}
H_{41}={}&79\cdot1373\cdot115471\\
&\cdot1506563\cdot1344905911,
\end{aligned}
$$

and the five signs are $+1,-1,-1,-1,+1$, again with product $-1$. They are ordinary quadratic-residue calculations at the listed rational primes, using the residue $4U_p(4)$.

The reference has positive infinite signs. Reciprocity therefore requires its dyadic product to be $-1$ as well: the two negative products multiply to $+1$.

Now suppose an admissible square solution existed. Its odd product would have to be $+1$, by the square-norm argument. Its dyadic product would remain $-1$, by Hensel stability. Its infinite product would be $+1$.

| Element being considered | Odd product | Infinite product | Dyadic product | Total |
|:---|:---:|:---:|:---:|:---:|
| Reference $\delta_4$ | $-1$ | $+1$ | $-1$ | $+1$: consistent |
| Hypothetical square-norm $\delta_x$ | $+1$ | $+1$ | $-1$ | $-1$: impossible |

This explains why reciprocity can be used in both the reference calculation and the contradiction without circularity. The reference is not assumed to satisfy the square condition. A hypothetical solution would impose an additional condition that is incompatible with its inherited dyadic sign.

That proves the hard phase at both fixed indices. Combining it with the elementary $6\bmod8$ phase proves the fixed-$17$ and fixed-$41$ exclusions for all $A\equiv2\pmod4$.

*Article: Theorem 4.2, Appendix A and §5.1. The displayed field and character values are finite certificate inputs, not numerical estimates.*

## 13. The Jacobi identity is the arithmetic shadow {#jacobi}

The same obstruction can be written using ordinary integers. For a positive odd denominator

$$
Q=\prod_{\ell\mid Q}\ell^{a_\ell},
$$

the **Jacobi symbol** is

$$
J(c,Q)=\prod_{\ell\mid Q}
\left(\frac{c}{\ell}\right)^{a_\ell}.
$$

Here $\ell$ ranges over the prime factors of $Q$, $a_\ell$ is its exponent, and the Legendre symbol $(c/\ell)$ is $+1$ or $-1$ according to whether a nonzero residue $c$ is a square or nonsquare modulo $\ell$. If $\ell\mid c$, the symbol is zero; the detector construction proves coprimality and prevents that case.

If $Q$ is a square and $\gcd(c,Q)=1$, every $a_\ell$ is even. Every factor contributes $+1$, so $J(c,Q)=+1$. A positive Jacobi value is not a proof that the denominator is square; the argument uses the opposite implication, that a negative value rules it out.

The paper instead proves

$$
\boxed{J(U_p(2A),F_p(A)-1)=-1}
$$

for every nonnegative $A\equiv2\pmod8$ and $p\in\{17,41\}$. This identity does not assume that the denominator is a square. It is an unconditional certificate excluding that possibility.

The link to the number field is exact. Put $x=2A$ and $Q=g_p(x)/2$. At the unique odd supporting prime above $\ell$, the reduction $\theta_p\mapsto x$ turns the algebraic detector into $xU_p(x)$. The local Hilbert formula gives

$$
\prod_{\mathfrak P\nmid2}
(\delta_x,b_p)_{\mathfrak P}
=J(xU_p(x),Q),
$$

where the product is over odd finite places. The factor $x$ has Jacobi value $+1$ here. Indeed, write $x=4m$ with $m\equiv1\pmod4$; then $Q\equiv-1\pmod m$, and quadratic reciprocity gives

$$
J(m,Q)=J(Q,m)=J(-1,m)=1.
$$

The case $m=1$ uses $J(c,1)=1$. Thus the odd Hilbert product is exactly $J(U_p(x),Q)$. Its value is $-1$ because the dyadic product is $-1$ and the infinite product is $+1$.

This is why “arithmetic shadow” is useful language. It is **the same obstruction expressed in integers**, not a further independent vote against the candidate. Lean's integer-Jacobi argument provides a formal arithmetic route to the exclusions; a few numerical evaluations of the identity would only be checks.

The identity also clarifies the local story. A negative product forces at least one odd prime factor of $Q$ to occur to an odd exponent. That prime makes $Q$ a nonsquare locally. Its identity can vary with $A$.

At $p=17,A=2$, for example, $F_{17}(2)-1=13\cdot1751444197$ has exactly one factor of $13$. The specialised square equation already fails at $13$. The theorem's strength is a fixed certificate that works for **every parameter**, without first finding and factoring its individual obstruction.

*Article: Proposition 7.1 and §§7.1–7.2.*

## 14. Why two fixed indices exclude infinitely many indices {#composition}

The sequence has a composition identity:

$$
F_{mn}(A)=F_m(F_n(A))
\qquad\text{when }n\text{ is odd}.
$$

In words, taking an odd-index term first can produce the parameter of a new sequence. Taking the $m$-th term of that new sequence is the same as taking term $mn$ of the original.

The oddness condition preserves the product $-1$ of the two conjugate quantities used in the recurrence. At an even inner index that product becomes $+1$, and the identity no longer applies. For example,

$$
F_4(2)=161,
\qquad F_2(F_2(2))=163.
$$

Now take odd $N$ divisible by $p\in\{17,41\}$. Write $N=pm$, so $m$ is odd, and set

$$
B=F_m(A).
$$

Reduction modulo $4$ gives $B\equiv2\pmod4$. Thus

$$
F_N(A)=F_p(B)
$$

falls under the fixed-index theorem, with a new admissible parameter $B$.

This is not a claim that multiplying any excluded index automatically preserves every property. It works because the exact composition identity and the parameter congruence have both been proved.

The final residue split must use $B$, not the original $A$ alone. A useful example is

$$
F_{51}(6)=F_{17}(882),
\qquad882=F_3(6)\equiv2\pmod8.
$$

The original pair $(A,N)=(6,51)$ survives at $2$. Its composed parameter enters the hard fixed-$17$ theorem and is excluded there.

Positive even $N$ are handled by the valuation theorem, not by forcing composition beyond its parity restriction. Those two branches together prove the all-positive index-divisibility theorem.

*Article: Lemma 5.1 and §5.3.*

## 15. Return to the same square-middle candidate {#return}

For the selected powerful-number family, the normal form gave

$$
y^2+1=X=F_N(u),
\qquad u\equiv2\pmod4,
\qquad N>0\text{ odd}.
$$

The recurrence theorem therefore forces

$$
\gcd(N,17\cdot41)=1.
$$

Here $\gcd$ denotes the greatest common divisor. The conclusion says that neither $17$ nor $41$ may divide the full Pell exponent.

The upper powerfulness requirement imposes an additional divisibility condition on that exponent. Write

$$
\varepsilon^n=a_n+b_n\sqrt K.
$$

The coefficient $b_n$ has first binomial term $nu^{n-1}v$. Every later term contributing to the coefficient of $\sqrt K$ contains a factor $K$. Hence

$$
b_n\equiv nu^{n-1}v\pmod K.
$$

The norm equation implies $\gcd(u,K)=1$, so the power of $u$ can be cancelled modulo $K$. Therefore

$$
K\mid b_n
\quad\Longleftrightarrow\quad
\frac{K}{\gcd(K,v)}\mid n.
$$

Define the divisibility rank

$$
R=\frac{K}{\gcd(K,v)}.
$$

It is the first positive index at which the second coefficient is divisible by $K$. The original upper-powerful equation gives $b_N=KV$, so $R\mid N$. We can write

$$
N=RE,
\qquad R\mid K,
$$

where $E$ is the remaining multiplier, called the outer exponent in the application. Both $R$ and $E$ are odd.

Now $17\mid E$, $41\mid E$ or $41\mid R$ would force a forbidden divisor of the same full exponent $N$. These are the three named application consequences. Merely finding a prime in $K$ does not put it in $R$ or $E$: the greatest-common-divisor formula shows what must actually be checked.

The free even-index theorem is broader recurrence mathematics. This particular negative-Pell source already has odd $N$, so that theorem does not create an additional even-exponent sector inside it.

Nor does avoiding $17$ and $41$ construct a candidate. The surviving exponents still have to satisfy every square and powerfulness requirement. The result supplies necessary conditions, not sufficient conditions for a powerful triple.

*Article: Corollary 1.5 and §6.3.*

## 16. What the human proof and computers each contribute {#verification}

There are two different kinds of finite work here. Testing $A$ up to a chosen bound examines finitely many cases and leaves larger cases undecided. Verifying the coefficients, resultants, factorisations and characters of a fixed certificate establishes finite premises of a theorem whose parameter is unrestricted. The paper uses the second kind for its proof-critical finite input.

The common criterion is the step that turns those premises into the all-height conclusion. Neither a table of outputs nor an opaque assertion that a program succeeded replaces that implication.

| Component | What it establishes | What it does not establish by itself |
|:---|:---|:---|
| Human mathematical argument | Norm/support reasoning, reciprocity criterion, propagation and exact application | An independent formal check of every prose statement |
| Exact Python/SymPy verifier | Polynomial identities, maximality certificates, resultants and reference characters | A numerical search proving all parameter values |
| GP and documented Magma computations | Additional number-field corroboration and local data | A separate new obstruction or a replacement for missing provenance |
| Lean development | Formal recurrence/Jacobi exclusions and propagation, with stated assumptions | A formalisation of the human Hilbert-reciprocity proof |
| Versioned files and hashes | Which exact statements, programs and outputs are being cited | Mathematical truth merely because the files have identities |

There is one specific formal boundary worth keeping. The degree-$41$ integer-Jacobi chain uses the oriented polynomial $-U_{41}(2A)$ for $A=8j+10$, and the endpoint $A=2$ is handled separately modulo $23$. The human Hilbert proof and the displayed Jacobi identity include that endpoint directly. These are matching exclusions with a documented difference in proof path, not an excuse to claim that every line was formalised identically.

The integer-Jacobi and Hilbert routes also share the same detector coefficients. Different proof architectures and different software checks reduce some kinds of error; they do not constitute independently discovered certificates or independent human review.

*Article: §7.3 and Appendices B–C. The [proof and source record](../../PROOF_RECORD.md) separates mathematical proof, computation, formal verification and byte identity. This guide does not assert that every proposed release mechanism has been implemented.*

## 17. Human judgement, stateless sessions, stateful engineering {#engineering}

The research strategy has a similar insistence on keeping identities and assumptions attached to claims, but it belongs to the workflow, not to the proof of the theorem.

An AI session is a temporary workspace for exploring an argument. It can propose a reduction, suggest a useful identity, challenge a proof or help write a verifier. None of those outputs becomes a theorem merely because it is persuasive or repeated across sessions.

The durable research state lives in explicit records: the exact claim, its hypotheses, the proof or failed attempt, the calculation it depends on, and the checks that were actually run. A new session can be given that state without being treated as an infallible continuation of the previous conversation.

This is the operational meaning of **stateless AI, stateful engineering**. It is not a claim that an AI product can never retain context. It means that continuity and authority do not depend on trusting conversational memory.

A concrete example is the composition identity. The record must say

$$
F_{mn}(A)=F_m(F_n(A))
\quad\text{only for odd inner }n.
$$

It should also retain the counterexample $F_4(2)\ne F_2(F_2(2))$. A summary that merely says “composition is proved” loses a load-bearing hypothesis. A later session could then produce an invalid proof while appearing to reuse checked work.

Similarly, the record must distinguish “passes every power-of-two square test” from “passes every local test”; identify $17$ and $41$ as indices, not automatically local obstructing primes; and keep a successful finite certificate replay separate from an unbounded theorem or a formal proof.

Human judgement selects questions, evaluates proposed reductions, reviews whether formal statements match the intended mathematics, and decides what is ready to present. Engineering preserves the evidence and makes selected checks repeatable. Mathematics determines whether the inference is valid.

The value of the workflow is therefore a specific kind of continuity: a session can end, a proposed route can fail, or a representation can change without losing which results are established and exactly where they apply. This description is not a measured claim that the workflow is faster than another research method, nor an attribution of particular discoveries to a model without a supporting record.

*Workflow context: see the [source and verification notes](#sources). The article remains the basis for the mathematical claims.*

## 18. The whole argument, brought back together {#whole-argument}

The square condition says $X-1$ must really be an integer square. The upper-powerful condition puts the same $X$ into a negative-Pell orbit. That orbit gives the same coefficient as a recurrence term. The local analysis removes elementary cases; the explicit units and reciprocity exclude the hard fixed-index cases; composition transfers that exclusion to the full exponent.

Hilbert reciprocity and the Jacobi identity are two descriptions of the same obstruction. Pell theory supplies the exact connection to the original candidate. Composition transports the result. Formal and computational tools check specified parts of the argument; they are not extra mathematical conditions on $X$.

For a positive solution of the recurrence square equation with $A\equiv2\pmod4$, the combined results force

$$
\begin{gathered}
N\text{ odd},\qquad\gcd(N,17\cdot41)=1,\\
(A\bmod8,N\bmod4)\in\{(2,1),(6,3)\}.
\end{gathered}
$$

These are necessary restrictions, not a classification of the remaining solutions. In the selected square-middle family they become restrictions on the exact exponent of the same Pell unit. Other square-middle families and the full three-consecutive problem are not decided by this result.

**The mathematical strategy is to preserve one candidate across its representations until their required properties become incompatible. The engineering strategy is to preserve one precise claim across sessions, proofs and checks until its evidential status is unambiguous.**

## Source and verification notes {#sources}

**Mathematical basis.** Chey G. A. Loveday, *Shifted-square obstructions at indices divisible by 17 or 41 in a family of Lucas sequences*, version 1.0.0 of 11 September 2026 (mathematical content frozen 10 September 2026): [article Markdown](../candidate/paper_1_release_candidate.md), [PDF](../candidate/paper_1_release_candidate.pdf) and [HTML](../candidate/paper_1_release_candidate.html). All numbered article references above resolve to that version. The guide adds explanatory examples and rearranges the exposition; it does not modify the article.

**Classical background.** J. S. Milne, *Class Field Theory*, version 4.03, Chapter III §4 and Chapter VIII §5.10, for the Hilbert pairing and product law. Keith Conrad, *Hensel's Lemma*, Theorem 9.1, for the strict lifting criterion. Both are already cited in the article; their roles here are explanatory, not evidence of novelty.

**Workflow basis.** Section 17 describes the research workflow as an explanation of its intended roles. The [proof and source record](../../PROOF_RECORD.md) identifies the actual mathematical and formal correspondences; the [reproduction guide](../../verification/export-README.md) gives the executable checks and their limits. This workflow discussion is not an author-approved AI-use disclosure or a measured evaluation of the process; the author's AI-use statement is in the article's Acknowledgements.

**Checks on this guide.** The small recurrence, Pell-power, divisibility and reference-character examples were recomputed in exact arithmetic. No new Lean, GP or Magma run, public-release check or independent mathematical review is claimed by this explanatory document.

**Rendering and source.** This is a supplied illustrated HTML artifact. Its embedded Markdown contains the prose and all 462 mathematical expressions; the five SVG figures and their captions are retained separately within the HTML. The Markdown alone does not recreate those illustrations or their layout. A complete illustrated-guide build recipe has not been supplied. Mathematical glyphs retain the [MathJax attribution and licence](../../verification/notices/README.md).
