# Elementary congruence consequences of $F_p(A)-1=y^2$ and why they stop short

Swarm `smw70l62n`, member m7, direction d5. Companion to
`theorem_no_finite_modulus.md`. All statements below are proved, or verified by
`verify_route_scope.py` (sections [2], [2b], [3], [7]).

Notation as in the paper: $D_p(T,-1)$ with $D_0=2$, $D_1=T$, $D_{n+2}=TD_{n+1}+D_n$;
$F_n$ with $F_0=1$, $F_1=A$, $F_{n+2}=2AF_{n+1}+F_n$; $D_n(2A)=2F_n(A)$;
$Q_p(A)=F_p(A)-1$. Let $V_p\in\mathbb Z[y]$ be defined by $D_p(x)=x\,V_p(x^2)$
(possible since $p$ is odd; $\deg V_p=(p-1)/2$), so that
$$F_p(A)=A\,V_p(4A^2). \tag{0.1}$$

## 1. Modulo $p$

**Proposition 1.** Let $p$ be an odd prime. Then $D_p(T)\equiv T^{p}\pmod p$,
$g_p(T)\equiv (T-2)^{p}\pmod p$, and for every integer $A$
$$F_p(A)-1\;\equiv\;(A-1)^{p}\pmod p. \tag{1.1}$$

*Proof.* $D_n(T)=\sum_{j=0}^{\lfloor n/2\rfloor}\frac{n}{n-j}\binom{n-j}{j}T^{n-2j}$;
for $n=p$ the coefficient of $T^{p-2j}$, $1\le j\le (p-1)/2$, is
$$c_j=\frac{p}{p-j}\binom{p-j}{j}
=p\,\frac{\binom{p-j-1}{j}}{p-2j},$$
using $\binom{p-j}{j}/(p-j)=\binom{p-j-1}{j}/(p-2j)$. Since $0<p-2j<p$ is coprime
to $p$ and $c_j$ is an integer, $c_j(p-2j)=p\binom{p-j-1}{j}$ forces $p\mid c_j$. So
$D_p(T)\equiv T^p$, whence $g_p\equiv T^p-2\equiv (T-2)^p$ (as $2^p\equiv 2$), which
is the paper's (A.4) for *every* odd prime $p$ — the input to its Dedekind index
certificate at the prime $p$. Next $2F_p(A)=D_p(2A)\equiv 2^{p}A^{p}\equiv 2A^{p}$,
so $F_p(A)\equiv A^{p}\equiv (A-1)^{p}+1 \pmod p$. $\square$

**Corollary 1.1.** Let $p\equiv 1\pmod 4$ and suppose $F_p(A)-1=y^2$. Then
$(A-1)^{p}$ is a square modulo $p$; as $p\equiv1\pmod 4$ this means: **either
$p\mid A-1$, or $A-1$ is a quadratic residue modulo $p$.**

For $p=17$ the condition reads $\left(\frac{A-1}{17}\right)\in\{0,1\}$; it holds for
about half of all $A$, and is satisfied by $A=2$ ($A-1=1$). Verified for
$A\in\{0,\dots,199\}$ and spot values: section [3].

## 2. Modulo $A^2+1$

**Proposition 2.** For every odd prime $p$, with $V_p$ as in (0.1),
$$V_p(-4)=\frac{F_p(i)}{i}=i^{\,p-1}. \tag{2.1}$$
Hence
$$F_p(A)\equiv A \pmod{A^2+1}\quad (p\equiv 1 \bmod 4),\qquad
F_p(A)\equiv -A \pmod{A^2+1}\quad (p\equiv 3 \bmod 4). \tag{2.2}$$

*Proof.* Put $A=i$. Then $A^2+1=0$, so by (2.4) of the paper
$F_p(i)=\tfrac12(\alpha^p+\beta^p)$ with $\alpha=\beta=i$, i.e. $F_p(i)=i^p$.
By (0.1), $F_p(i)=i\,V_p(4i^2)=i\,V_p(-4)$, giving (2.1). Reducing (0.1) modulo
$A^2+1$ turns $4A^2$ into $-4$. $\square$

**Corollary 2.1.** Let $p\in\{17,41\}$ and suppose $F_p(A)=y^2+1$. Then
$$y^{2}\equiv A-1 \pmod{A^{2}+1},\qquad
y^{4}\equiv -2A \pmod{A^{2}+1}. \tag{2.3}$$
For $A\equiv 2\pmod 4$ the modulus $A^2+1$ is odd and every prime $\ell\mid A^2+1$
satisfies $\ell\equiv 1\pmod 4$; consequently, for each such $\ell$,
$A-1$ is a non-zero quadratic residue modulo $\ell$ and $-2A$ is a **fourth power**
modulo $\ell$ (and modulo $\ell^{v_\ell(A^2+1)}$).

*Proof.* The first congruence is (2.2) with $F_p(A)=y^2+1$; squaring and using
$A^2\equiv-1$ gives the second. As $A$ is even, $A^2+1\equiv 5\pmod 8$ is odd, and
if $\ell\mid A^2+1$ then $A^2\equiv-1 \pmod \ell$ forces $\ell\equiv1\pmod 4$ (and
$\ell\nmid A-1$, since $\ell\mid A-1$ would give $\ell\mid 2$). Finally
$(A-1)^2=A^2-2A+1\equiv-2A\pmod{\ell^{e}}$ for $e=v_\ell(A^2+1)$, so $-2A$ is the
square of the square $A-1$, i.e. a fourth power, modulo $\ell^e$; CRT gives a fourth
root modulo $A^2+1$ itself. $\square$

This is a genuinely new necessary condition relative to the manuscript (which uses
only the mod-$8$ split and the single check $F_{41}(2)-1\equiv20\pmod{23}$). It is a
"quartic-residue at the primes of $A^2+1$" condition, i.e. an $A$-dependent
splitting condition in $\mathbb Q(\sqrt{A-1})$ and $\mathbb Q(2^{1/4},\dots)$.

## 3. Shifting the evaluation point

For any integer $A_0$, $F_p(A)\equiv F_p(A_0)\pmod{A-A_0}$; so a solution
$F_p(A)=y^2+1$ forces
$$y^{2}\equiv F_p(A_0)-1 \pmod{A-A_0}\qquad(A\ne A_0). \tag{3.1}$$
For $A_0=1$ and $A_0=-1$ (using $F_p(-T)=-F_p(T)$ for odd $p$) this says that the
*fixed* integers $F_p(1)-1$ and $-F_p(1)-1$ must be quadratic residues modulo the
prime powers dividing $A-1$ resp. $A+1$. Again an $A$-dependent splitting condition.

## 4. These conditions are real but far from contradictory (data)

Write, for $A\equiv2\pmod 8$:

* $c_1$: $-2A$ is a fourth power modulo every $\ell\mid A^2+1$ (Cor. 2.1);
* $c_2$: $p\mid A-1$ or $A-1$ is a square modulo $p$ (Cor. 1.1);
* $c_3$: $F_p(1)-1$ is a square modulo every odd prime $\ell\mid A-1$ (not dividing it);
* $c_4$: $-F_p(1)-1$ is a square modulo every odd prime $\ell\mid A+1$ (not dividing it).

| $p$ | $A=8k+2\le 80000$ | $c_1$ | $c_2$ | $c_3$ | $c_4$ | $c_1\wedge c_2\wedge c_3\wedge c_4$ |
|---|---|---|---|---|---|---|
| 17 | 10000 | 3886 | 5296 | 3090 | 2637 | **205** (e.g. $2,26,226,282,490,530,770,1722$) |
| 41 | 10000 | 3886 | 5122 | 3211 | 2819 | **193** (e.g. $2,26,42,170,690,730,842,1106$) |

So all the cheap necessary conditions hold simultaneously for a positive proportion
(about $2\%$) of the hard phase, including $A=2$; they cannot exclude any class of
$A$ in the way a covering congruence would. Section [7] of the verifier.

## 5. Where these conditions stop, stated precisely

**Revised after review**: items 1–3 are proved statements, item 4 is the exact
residue of the classical hope. Nothing here excludes proof strategies other than the
ones named.

1. **No fixed modulus works** (Theorem 1, Corollary 2 of
   `theorem_no_finite_modulus.md`): for every finite set $S$ of odd primes there are
   infinitely many $A\equiv2\pmod 8$ with $Q_p(A)$ a square modulo $2^{\alpha}$ and
   modulo $\ell^{e_\ell}$ for every $\ell\in S$. So every condition of the form
   "$Q_p(A)$ must be a square modulo $M$", for fixed $M$, is satisfiable; no finite
   list of congruence conditions on $A$ alone can be contradictory.
2. **The prime 2 is transparent for $Q_p$** (Lemma 1 there; the paper's Proposition
   2.1): $Q_p(A)\equiv1\pmod 8$ for all $A\equiv2\pmod 8$, so the value is an honest
   $2$-adic square and no analysis at $2$ can show that *this* number is a non-square.
   (This says nothing against the manuscript's use of dyadic Hilbert symbols, which
   concern the squareclass of a different element $\delta_x$, not the squareness of
   $Q_p(A)$.)
3. **Valuation parity is transparent.** In the Pell picture ($K=A^2+1$, fundamental
   unit $A+\sqrt K$) the equation $F_p(A)=y^2+1$ makes the relevant norm data even
   everywhere (§3.3 of the manuscript extracts exactly this and obtains no
   contradiction). Since squares have even valuations, support/parity data cannot
   contradict squareness.
4. **Consequence for local-witness arguments.** If a proof of Theorem 4.2 is to
   proceed by exhibiting, for each admissible $A$, a prime $\ell$ at which $Q_p(A)$ is
   a *local* non-square ("(W1) witness" in the terminology of
   `theorem_no_finite_modulus.md` §0.1), then that prime must depend on $A$ — by item
   1. This does not say that every proof must be of that kind: the manuscript's
   argument produces instead a (W2) witness (a prime divisor of odd valuation with
   non-residue detector character), and global arguments (heights, integral points on
   $y^2=Q_p(A)$, linear forms in logarithms) need no local witness at all.

**What is genuinely open here.** Whether a (W1)-witness construction of lower
complexity exists than the manuscript's certificate (lower-degree numerator, or a
formula from the factorisation of $A^2+1$ and $A\pm1$). Corollary 2 says it cannot be
a function of $A\bmod M$ alone. I have neither such a construction nor a theorem
excluding one, and I have not surveyed the literature for it.

## 6. Reproduce

```
cd .ultramath/smw70l62n/m7
python3 verify_route_scope.py       # sections [2] Prop. 2, [2b] Lemma 1,
                                    # [3] Prop. 1, [7] the table above
```
