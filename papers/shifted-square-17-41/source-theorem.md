# The all-positive-index Pell-unit theorem and exact source transfers

## Scope and authority

This note gives the source-independent theorem first and then reconstructs the
three Erdős-source consequences without changing any source record, packet
definition, branch router, or terminal proposition.

The historical #119 source inventory was audited at commit
`5466584a52e50f3e4ba4c8bd2c445e0ccb60691e`.  The superseding #139 theorem
surface is the current
[`ShiftedSquarePropagation.lean`](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean)
source; its final reviewed immutable SHA is deliberately bound only by the
post-review #122 evidence regeneration.  All recurrence variables and square
witnesses below are natural numbers.  The displayed quadratic-ring real
coordinate is an integer.

Nothing here changes canonical status, Ledger status, the
`sm2LowerSquare` leaf, or the maintained terminal count `1/4`.

## 1. Exact recurrence and quadratic-ring normalization

For \(A,n\in\mathbf N\), define

\[
F_0(A)=1,\qquad F_1(A)=A,\qquad
F_{n+2}(A)=2A F_{n+1}(A)+F_n(A).
\tag{1}
\]

This is exactly
`sm2LucasReal A n`, not a rescaled Lucas sequence.  The maintained
definition is
[here](../../Erdos364/SquareMiddle/Sm2LowerSquareGeneratorRank.lean#L34-L46).

For \(K,u,v\in\mathbf N\), write

\[
\varepsilon=u+v\sqrt K
\]

for the formal quadratic-ring element

\[
\langle u,v\rangle\in\mathbf Z[\sqrt K].
\]

This is the repository object `sm2UpperNegativeUnit K u v`
([definition](../../Erdos364/SquareMiddle/Sm2LowerSquareUpperNormOneOrbit.lean#L595-L602)).
No analytic `cosh`, arbitrary real square root, or alternative Pell
normalization is used.

If

\[
u^2+1=Kv^2,
\tag{2}
\]

then \(\operatorname{Norm}(\varepsilon)=-1\), and the exact maintained
coordinate theorem is

\[
\operatorname{Re}(\varepsilon^n)=F_n(u).
\tag{3}
\]

The full coordinate identity is

\[
\varepsilon^n
=F_n(u)+v\,C_n(u)\sqrt K,
\]

where \(C_n=\operatorname{sm2LucasCoeff}\).  The formal statements are
[here](../../Erdos364/SquareMiddle/Sm2LowerSquareGeneratorRank.lean#L768-L818).

## 2. All-positive-index norm-minus-one Pell-unit theorem

### Theorem P

Let \(K,u,v,N,y\in\mathbf N\).  Assume

\[
u^2-Kv^2=-1,\qquad u\equiv2\pmod4,\qquad N>0,
\]

and

\[
17\mid N\quad\text{or}\quad41\mid N.
\]

Then

\[
\boxed{\operatorname{Re}\bigl((u+v\sqrt K)^N\bigr)\ne y^2+1.}
\tag{4}
\]

The exact maintained Lean theorem is

```lean
Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor
    {K u v N : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2)
    (hNpos : 0 < N)
    (hfactor : 17 ∣ N ∨ 41 ∣ N)
    (y : Nat) :
    ((⟨u, v⟩ : ℤ√(K : Int)) ^ N).re ≠
      ((y ^ 2 + 1 : Nat) : Int)
```

Its formal source is the current
[`ShiftedSquarePropagation.lean`](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean).

The Lean statement does not separately assume \(K,u,v>0\).  Under its
equation and \(u\equiv2\pmod4\), those positivity conditions follow:
\(u\ge2\), while \(K=0\) or \(v=0\) would make the positive left side of
(2) equal to zero.  Thus the conventional positive Pell-unit wording loses
no formal cases.

### Proof

Equation (3) identifies the left side of (4) with \(F_N(u)\).  The phase,
positivity, and divisibility hypotheses are exactly those of

```lean
Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_index_factor
```

which proves

\[
F_N(u)\ne y^2+1.
\]

For odd \(N\), this is the retained composition consequence of the
phase-strengthened fixed indices \(17\) and \(41\).  For positive even
\(N\), the independent exact valuation theorem

\[
v_2(F_N(u)-1)=2v_2(N)+1
\]

has odd right-hand side and rules out a square.  The all-positive theorem
splits these cases and then substitution through (3) proves (4).  It neither
uses nor asserts unrestricted even-inner-index composition.  \(\square\)

### Free positive-even-index Pell corollary

The factor condition is unnecessary at positive even indices.  Precisely,

```lean
Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index
    {K u v N : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2)
    (hNpos : 0 < N)
    (hNeven : Even N)
    (y : Nat) :
    ((⟨u, v⟩ : ℤ√(K : Int)) ^ N).re ≠
      ((y ^ 2 + 1 : Nat) : Int)
```

This is a source-independent corollary of the exact valuation; it does not
enlarge any existing odd-exponent source-terminal exclusion.

## 3. Common source reconstruction

For one complete `sm2LowerSquare` allocation, the maintained upper-orbit
record retains natural numbers

\[
r=\texttt{rootX},\qquad s=\texttt{rootY},\qquad N=\texttt{index}
\]

with

\[
r^2+1=Ks^2,\qquad N\ \text{odd},
\tag{5}
\]

and the exact same-centre power identity

\[
\texttt{sourcePoint}(K,X,KV)=(r+s\sqrt K)^N.
\tag{6}
\]

The record is
[here](../../Erdos364/SquareMiddle/Sm2LowerSquareUpperNormOneOrbit.lean#L721-L761).
The allocation separately retains

\[
X=y^2+1
\tag{7}
\]

for its original witness \(y\)
([source](../../Erdos364/SquareMiddle/Sm2LowerSquareAllocation.lean#L16-L38)).

The rank-normalized generator records

\[
N=R(2t+1),\qquad
R=\operatorname{pellRank}(K),
\tag{8}
\]

together with a norm-minus-one intermediate point

\[
P+Q\sqrt K,\qquad P\equiv2\pmod8,
\]

whose \((2t+1)\)-st power is the same source point.  These are record fields,
not reconstructed guesses
([source](../../Erdos364/SquareMiddle/Sm2LowerSquareUpperSourceGenerator.lean#L873-L911)).

### Direct full-index propagation audit

The unchanged source records support the following clean human corollary.

> For a complete retained upper source orbit, if
> \(17\mid N\) or \(41\mid N\), then the source centre cannot equal
> \(y^2+1\).

Indeed, the source compiler proves \(r\equiv2\pmod8\), hence
\(r\equiv2\pmod4\).  Equations (5)--(7) identify

\[
\operatorname{Re}\bigl((r+s\sqrt K)^N\bigr)=X=y^2+1.
\]

Theorem P, applied to \(r,s,N\), contradicts this equality.  The retained
source record happens to require odd \(N\); the new free even theorem does
not change that source-side condition, add an adapter, or enlarge a terminal
exclusion.

This proves the requested propagated source form from unchanged data.  A new
Lean declaration is intentionally not added: the proof is a direct
composition of the public orbit fields,
`root_real_mod_eight`, and Theorem P, while the three maintained
source-facing consequence theorems below already expose the required paper
claims.  Packet wrappers around the full-index corollary would duplicate
those existing adapters.

## 4. Complete outer-17 source family

### Exact statement

```lean
Erdos364.noSm2OuterSeventeenBlocks :
  Erdos364.NoSm2OuterSeventeenBlocks
```

Here `NoSm2OuterSeventeenBlocks` universally quantifies over every retained
`data`, `allocation`, and `generator`, and negates its complete
`OuterSeventeenPacket`
([definition](../../Erdos364/SquareMiddle/Sm2LowerSquareGeneratorRank.lean#L4795-L4801)).

### Same-witness proof diagram

```text
complete OuterSeventeen source
  -> 17 | (2*outerIndex+1), with
       2*outerIndex+1 = m*17 and m odd
  -> the retained intermediate point is A+B*sqrt(K)
  -> A^2+1 = K*B^2 and A % 8 = 2
  -> the same source point is (A+B*sqrt(K))^17
  -> F_17(A) = allocation.y^2+1
  -> SS17 / Theorem P at n=17
  -> contradiction.
```

Every arrow is a field of the complete packet
([packet](../../Erdos364/SquareMiddle/Sm2LowerSquareGeneratorRank.lean#L4326-L4402))
or the direct maintained adapter
([proof](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L2052-L2063)).

The paper statement is:

> \(17\) divides the selected outer exponent.

It is not:

> the upper kernel equals \(17\).

In fact this packet records both \(17\nmid K\) and
\(17\nmid\operatorname{pellRank}(K)\).

## 5. Selected-41 outer-large sector

### Exact statement

```lean
Erdos364.no_outerLarge_selected_fortyOne
    (generator)
    (packet : generator.OuterLargePacket)
    (h41 : 41 ∣ 2 * generator.outerIndex + 1) :
    False
```

### Same-witness proof diagram

```text
complete OuterLarge source
+ explicit 41 | (2*outerIndex+1)
  -> write 2*outerIndex+1 = m*41, with m odd
  -> reconstruct A+B*sqrt(K) = generator.point^m
  -> A^2+1 = K*B^2 and A % 8 = 2
  -> the unchanged source point is (A+B*sqrt(K))^41
  -> F_41(A) = allocation.y^2+1
  -> SS41 / Theorem P at n=41
  -> contradiction.
```

The same-witness reconstruction is
[here](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13710-L13811);
the public adapter is
[here](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13938-L13951).

The explicit divisor \(41\) is not identified with the unrelated existential
prime stored in `OuterLargePacket`.  This is an outer-selected slice, not
the whole `NoSm2OuterLargeBlocks` terminal.

## 6. Selected-41 rank-defect sector

### Exact statement

```lean
Erdos364.no_rankDefect_selected_fortyOne
    (generator)
    (packet : generator.RankDefectPacket)
    (h41 : 41 ∣
      pellRank data.upperKernel allocation.upper_pellKernel) :
    False
```

### Same-witness proof diagram

```text
complete RankDefect source
+ explicit 41 | pellRank(K)
  -> write pellRank(K) = n*41, with n odd
  -> reconstruct A+B*sqrt(K) = rootUnit^n
  -> A^2+1 = K*B^2 and A % 8 = 2
  -> the unchanged source point is (A+B*sqrt(K))^41
  -> F_41(A) = allocation.y^2+1
  -> SS41 / Theorem P at n=41
  -> contradiction.
```

The same-witness reconstruction is
[here](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13813-L13936);
the public adapter is
[here](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13953-L13967).

This is a rank-selected slice, distinct from the outer-selected slice.  The
explicit divisor \(41\) is again not identified with the packet's
existential selected prime.

## 7. Allowed manuscript wording

The following source-independent statement matches Theorem P:

> Let \(\varepsilon=u+v\sqrt K\) be a positive norm-minus-one Pell unit with
> \(u\equiv2\pmod4\).  If \(N>0\) is divisible by \(17\) or \(41\),
> then the real coordinate of \(\varepsilon^N\) is not one more than a
> square.

The three source consequences must then be stated separately:

- the complete outer-17 family is excluded because \(17\) divides its exact
  outer exponent;
- the outer-selected 41 slice is excluded under the explicit hypothesis
  \(41\mid(2t+1)\);
- the rank-selected 41 slice is excluded under the explicit hypothesis
  \(41\mid\operatorname{pellRank}(K)\).

## 8. Forbidden strengthening

Do not write:

```text
we close OuterLarge
we close RankDefect
the upper kernel is 17 or 41
all admissible selected primes are covered
all positive indices are covered without the stated 17/41 divisor
packet count equals global coverage
```

The result is not a uniform \(\mathrm{SS}_p\) theorem.  It does not exclude
arbitrary positive indices, primes other than \(17\) and \(41\), the whole
`NoSm2OuterLargeBlocks` or `NoSm2RankDefectBlocks` terminals, the atomic
terminal, the complete leaf, or Erdős 364.  It does exclude every positive
even recurrence index in the stated \(2\bmod4\) phase, independently of a
prime divisor.
