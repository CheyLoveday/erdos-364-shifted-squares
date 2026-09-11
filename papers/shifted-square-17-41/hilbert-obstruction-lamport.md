# A two-layer Hilbert obstruction for the fixed degrees 17 and 41

Issue: #120
Consumer: the conceptual human proof for Paper 1 (#118)
Threat tier: T0 trusted-local mathematical documentation

## Scope and claim ceiling

This note proves two results in dependency order:

1. the polynomial-free **Dyadic Hilbert Obstruction Lemma** (H1);
2. a conditional monogenic odd-degree criterion (H2) that discharges H1
   from exactly the data shared by the fixed degree-17 and degree-41
   certificates.

The finite instance data are isolated in
[fixed-field-obligation-table.md](fixed-field-obligation-table.md).  The
relation to the maintained integer-Jacobi proofs is isolated in
[hilbert-jacobi-crosswalk.md](hilbert-jacobi-crosswalk.md).

This is a complete human number-field argument conditional on the displayed
finite certificate inputs.  It is not a Hilbert-symbol Lean formalisation,
does not construct a detector for any other degree, and does not alter the
maintained terminal count or canonical mathematical status.

## Conventions and cited inputs

For a finite prime \(\mathfrak P\) of a number field,
\(v_{\mathfrak P}\) is normalized by

\[
v_{\mathfrak P}(\mathfrak P)=1.
\]

Thus \(v_{\mathfrak P}(2)=e(\mathfrak P/2)\) when
\(\mathfrak P\mid2\).  The quadratic Hilbert symbol is written
\((a,b)_v\).

Four standard results are used with precise locators.

- Hilbert reciprocity:
  \(\prod_v(a,b)_v=1\) over all places of a number field.  See J. S.
  Milne, *Class Field Theory*, version 4.03, Chapter VIII §5, item 5.10,
  p. 247 ([author PDF](https://www.jmilne.org/math/CourseNotes/CFT.pdf)).
  The squareclass pairing used below is described in Chapter III §4,
  Theorem 4.4, pp. 113–114; the real and complex evaluations are recorded
  immediately after Theorem 5.11, p. 248.
- At a non-dyadic local field with residue field of cardinality \(q\), write
  \(a=\pi^r a_0\) and \(c=\pi^s c_0\), with \(a_0,c_0\) units.  Then

  \[
  (a,c)=(-1)^{rs(q-1)/2}
        \chi(\bar a_0)^s\chi(\bar c_0)^r,                 \tag{1}
  \]

  where \(\chi\) is the quadratic character of the residue field.  This is
  the quadratic specialization of Gyujin Oh, *Algebraic Number Theory*,
  Theorem 16.32, p. 154
  ([official Columbia notes](https://www.math.columbia.edu/~gyujinoh/Spring2024/ANT.pdf)).
- The maximal-monogenic prime factorisation used below is the
  Dedekind–Kummer theorem.  See Andrew V. Sutherland, MIT 18.785 Lecture 6,
  Theorem 6.14, p. 8
  ([official MIT notes](https://math.mit.edu/classes/18.785/2021fa/LectureNotes6.pdf)).
  The norm identity

  \[
  v_\ell(N_{L/\mathbf Q}\alpha)
   =\sum_{\mathfrak P\mid\ell}
      f(\mathfrak P/\ell)v_{\mathfrak P}(\alpha)          \tag{2}
  \]

  follows by applying the ideal norm to the factorisation of
  \((\alpha)\); see Milne, *Algebraic Number Theory*, “Norms of ideals” and
  Proposition 4.1(c), pp. 69–70
  ([author PDF](https://www.jmilne.org/math/CourseNotes/ANT.pdf)).
- Strong Hensel: if \(F\) is integral over a complete nonarchimedean field
  and \(v(F(a))>2v(F'(a))\), then \(F\) has a root near \(a\).  See Keith
  Conrad, *Hensel’s Lemma*, Theorem 9.1, p. 18
  ([author PDF](https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf)).

The GP scripts cited in the companion table verify finite field and local
data only.  They do not prove any of these quantified results.

## H1: Dyadic Hilbert Obstruction Lemma

### Theorem H1

Let \(L\) be a number field, let \(b\in L^\times\), let \(I\) be an index
set, and let \(S\subseteq I\) be the set of admissible indices.  Fix a
reference \(x_0\in I\) and elements \(\delta_x\in L^\times\) for every
\(x\in I\).  Suppose that, for every \(x\in S\):

1. **odd finite neutrality:** \((\delta_x,b)_v=1\) at every finite
   \(v\nmid2\);
2. **archimedean neutrality:** \((\delta_x,b)_v=1\) at every
   archimedean \(v\);
3. **dyadic squareclass stability:**
   \(\delta_x/\delta_{x_0}\in L_v^{\times2}\) at every \(v\mid2\).

If

\[
\prod_{v\mid2}(\delta_{x_0},b)_v=-1,                     \tag{3}
\]

then \(S=\varnothing\).

### Proof

Assume \(x\in S\).  At a dyadic place, hypothesis 3 and squareclass
invariance give

\[
(\delta_x,b)_v=(\delta_{x_0},b)_v.
\]

The dyadic product is therefore \(-1\) by (3).  Every non-dyadic factor is
\(+1\) by hypotheses 1 and 2, including every complex factor.  Hence the
product over all places is \(-1\), contradicting Hilbert reciprocity.
Therefore no \(x\in S\) exists.  \(\square\)

The reference \(x_0\) is not required to be admissible or to solve the
Diophantine equation.

## H2: conditional monogenic odd-degree criterion

### Theorem H2

Let \(g\in\mathbf Z[T]\) be monic and irreducible of odd degree
\(d\ge3\).  Let \(g(\theta)=0\) and \(L=\mathbf Q(\theta)\).  Assume:

1. \(\mathcal O_L=\mathbf Z[\theta]\) and \(N_{L/\mathbf Q}(\theta)=2\);
2. for one odd prime \(p\), the field discriminant has support contained in
   \(\{2,p\}\);
3. there is exactly one prime \(\mathfrak p\mid p\), and it has
   \(f(\mathfrak p/p)=1\) (hence \(e(\mathfrak p/p)=d\));
4. \(L\) has signature \((1,(d-1)/2)\), and the image at its unique real
   embedding satisfies \(0<\theta_{\mathbf R}<4\);
5. there is an integral detector \(b\) satisfying

   \[
   (b)=(\theta).                                         \tag{4}
   \]

   In both fixed instances the certificate supplies the stronger exact
   metadata \(b=\theta u\), where \(u\in\mathcal O_L^\times\),
   \(N(u)=-1\), and \(N(b)=-2\);
6. for every \(\mathfrak P\mid2\), with

   \[
   e_{\mathfrak P}=v_{\mathfrak P}(2),\qquad
   d_{\mathfrak P}=v_{\mathfrak P}(4-\theta),
   \]

   one has the strict inequality

   \[
   4e_{\mathfrak P}-d_{\mathfrak P}>2e_{\mathfrak P};    \tag{5}
   \]
7. with \(\delta_4=(4-\theta)/\theta\), a direct finite certificate gives

   \[
   \prod_{\mathfrak P\mid2}(\delta_4,b)_{\mathfrak P}
   =-1.                                                   \tag{6}
   \]

Then there are no \(x,Y\in\mathbf Z\) satisfying

\[
x\ge4,\qquad x\equiv4\pmod {16},\qquad g(x)=2Y^2.         \tag{7}
\]

### Lemma H2.1: square-norm element and orientation

Under the hypotheses of H2, any putative solution of (7) has
\(Y\ne0\), and

\[
\delta_x=\frac{x-\theta}{\theta}\in L^\times,\qquad
N(\delta_x)=Y^2.                                         \tag{8}
\]

#### Proof

If \(Y=0\), then \(g(x)=0\), so \(T-x\) divides the irreducible polynomial
\(g\), contrary to \(d>1\).  This dispatch occurs before
\(\delta_x\) is treated as an element of \(L^\times\).

Because \(g\) is the monic minimal polynomial of \(\theta\),

\[
N(x-\theta)=\prod_\sigma(x-\sigma(\theta))=g(x).
\]

Thus \(N(\delta_x)=g(x)/N(\theta)=Y^2\).  The orientation is exact:
in odd degree \(N(\theta-x)=-g(x)\), so it cannot silently replace
\(x-\theta\).  \(\square\)

### Lemma H2.2: odd-place valuation parity

Let \(\mathfrak P\) be an odd finite prime of \(L\).  For a putative
solution of (7),

\[
v_{\mathfrak P}(\delta_x)\ \text{is even}.               \tag{9}
\]

#### Proof

Since \(N(\theta)=2\), \(\theta\) is a unit at every odd prime, so
\(v_{\mathfrak P}(\delta_x)=v_{\mathfrak P}(x-\theta)\).
If \(\mathfrak P\nmid(x-\theta)\), this valuation is zero.

Now let \(\mathfrak P\mid(x-\theta)\), above the rational prime \(\ell\).

**Unramified case \(\ell\ne p\).**  The discriminant hypothesis makes
\(\ell\) unramified.  Since \(\mathcal O_L=\mathbf Z[\theta]\),
Dedekind–Kummer identifies the primes above \(\ell\) with the distinct
irreducible factors of \(g\bmod\ell\).  Reduction modulo
\(\mathfrak P\) gives \(\theta=\bar x\), so the corresponding factor has a
root in \(\mathbf F_\ell\).  It is therefore the linear factor
\(T-\bar x\), with residue degree one.  Squarefreeness makes that factor
unique: no other prime above \(\ell\) divides \(x-\theta\).  Formula (2)
therefore reduces to

\[
v_{\mathfrak P}(\delta_x)=v_\ell(N\delta_x),
\]

which is even by (8).  The conclusion is uniqueness among the primes
dividing \(x-\theta\), not uniqueness of the entire prime decomposition of
\(\ell\).

**Ramified case \(\ell=p\).**  There is exactly one
\(\mathfrak p\mid p\), it has residue degree one, and \(\theta\) is a
\(\mathfrak p\)-unit.  Formula (2) again gives

\[
v_{\mathfrak p}(\delta_x)=v_p(N\delta_x),
\]

which is even.  No congruence \(g\equiv(T-2)^d\pmod p\) is needed once this
unique-\(f=1\) prime is certified.  \(\square\)

This lemma deliberately does not use the false general implication
“square global norm implies every local valuation is even.”

### Lemma H2.3: odd finite and archimedean neutrality

For a putative solution of (7),

\[
(\delta_x,b)_v=1
\]

at every non-dyadic finite place and every archimedean place.

#### Proof

Condition (4) and \(N(\theta)=2\) make \(b\) a unit at every odd finite
prime.  In (1), take \(r=v_{\mathfrak P}(\delta_x)\) and
\(s=v_{\mathfrak P}(b)=0\).  Lemma H2.2 makes \(r\) even, so every factor
in (1) is \(1\).

Complex Hilbert symbols are trivial.  At the unique real embedding,

\[
\delta_{x,\mathbf R}
 =\frac{x-\theta_{\mathbf R}}{\theta_{\mathbf R}}>0
\]

because \(x\ge4>\theta_{\mathbf R}>0\).  A positive real entry has Hilbert
symbol \(1\), independently of the sign of the real image of \(b\).
\(\square\)

### Lemma H2.4: dyadic Hensel squareclass

For every \(\mathfrak P\mid2\) and every
\(x\equiv4\pmod {16}\),

\[
\delta_x/\delta_4\in L_{\mathfrak P}^{\times2}.           \tag{10}
\]

#### Proof

If \(x=4\), the ratio is \(1\).  Otherwise,

\[
\frac{\delta_x}{\delta_4}
 =\frac{x-\theta}{4-\theta}
 =1+z,\qquad z=\frac{x-4}{4-\theta}.
\]

Because \(16\mid x-4\),

\[
v_{\mathfrak P}(z)
\ge4e_{\mathfrak P}-d_{\mathfrak P}
>2e_{\mathfrak P}
=2v_{\mathfrak P}(2).
\]

Apply strong Hensel to
\(F(S)=S^2-(1+z)\) at \(S=1\).  Here

\[
v_{\mathfrak P}(F(1))=v_{\mathfrak P}(z)
  >2v_{\mathfrak P}(F'(1)).
\]

Thus \(F\) has a root in \(L_{\mathfrak P}\), proving (10).
\(\square\)

Strictness is load-bearing: equality is insufficient, as
\(1+4=5\) is not a square in \(\mathbf Q_2\).

### Proof of H2

Assume (7).  Lemma H2.1 supplies \(\delta_x\in L^\times\).
Lemma H2.3 supplies the odd finite and archimedean hypotheses of H1.
Lemma H2.4 supplies dyadic squareclass stability relative to \(x_0=4\).
The direct reference input (6) supplies H1’s negative reference product.
H1 gives a contradiction.  \(\square\)

## Fixed-degree consequence

For \(p\in\{17,41\}\), define

\[
D_0=2,\qquad D_1=T,\qquad D_{n+2}=TD_{n+1}+D_n,\qquad
g_p=D_p-2.
\]

The companion obligation table records exact assertions discharging every
finite hypothesis of H2 for \(g_{17}\) and \(g_{41}\).  Therefore, for
each \(p\in\{17,41\}\), no integers \(x,Y\) satisfy

\[
x\ge4,\qquad x\equiv4\pmod {16},\qquad g_p(x)=2Y^2.
\]

With \(x=2A\), the exact Dickson–Lucas bridge gives the fixed-index
shifted-square conclusions for
\(A\ge2\) and \(A\equiv2\pmod8\).

## Lamport dependency and falsifier ledger

| Step | Depends on | Load-bearing boundary or falsifier |
|---|---|---|
| H1 | reciprocity; squareclass invariance | reference product \(+1\) gives no obstruction |
| H2.1 | irreducibility; monicity; norm orientation | \(Y=0\) must be dispatched first |
| H2.2 unramified | maximal monogenic order; unramifiedness | two split primes with odd valuations refute the naive norm inference |
| H2.2 ramified | unique prime over \(p\); \(f=1\) | multiple primes or \(f>1\) require new hypotheses |
| H2.3 | exact non-dyadic formula; unique positive real embedding | no sign assumption on \(b_{\mathbf R}\) is used |
| H2.4 | \(v_{\mathfrak P}(\mathfrak P)=1\); strict (5) | equality in strong Hensel is not enough |
| H2 | direct reference product | the GP input is finite data, not a quantified proof |

## Exact manuscript wording ceiling

The following is the strongest supported manuscript wording:

> For each of the fixed degrees \(17\) and \(41\), an exact PARI/GP
> certificate verifies the finite field, detector, dyadic, and reference
> inputs of one common conditional monogenic criterion.  The criterion,
> via the Dyadic Hilbert Obstruction Lemma, gives a conceptual human
> local–global proof of the fixed shifted-square exclusion.  The maintained
> Lean theorem follows a specialization-safe integer-Jacobi route.  The two
> routes share polynomial and certificate provenance.

It is not supported to say that the Hilbert argument is formalized in Lean,
that the two proof routes have independent certificate provenance, that a
uniform \(SS_p\) theorem has been proved, or that terminal/canonical status
has changed.
