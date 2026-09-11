# Theorem, formal-source, and prime-semantics crosswalk

## Scope

This is the paper-facing crosswalk for the fixed-\(17/41\), propagated, Pell,
and source-consequence theorems.  It separates ordinary mathematical
statements from repository implementation vocabulary while retaining exact
formal quantifiers and reconstruction maps in one appendix.

The historical #119 inventory was audited at immutable source commit
`5466584a52e50f3e4ba4c8bd2c445e0ccb60691e`.  The #139 declarations named
below are in the current
[`ShiftedSquarePropagation.lean`](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean)
surface.  Their reviewed immutable SHA is intentionally bound only by the
post-review #122 evidence regeneration.  This tranche changes no source
record, packet, branch router, or terminal proposition.

Current maintained status is exactly:

```text
NoSm2OuterSeventeenBlocks : proved
NoSm2OuterLargeBlocks     : open
NoSm2RankDefectBlocks     : open
NoSm2AtomicResiduals      : open
sm2LowerSquare leaf       : open
Erdős 364                 : open
```

The internal terminal count remains `1/4`; it is not a public coverage
percentage.

## 1. Recurrence and domain lock

Throughout,

\[
F_0(A)=1,\qquad F_1(A)=A,\qquad
F_{n+2}(A)=2A F_{n+1}(A)+F_n(A),
\]

and \(F_n(A)=\operatorname{sm2LucasReal}(A,n)\).

- \(A,n,y,K,u,v\) are natural numbers in the maintained theorem signatures.
- A quadratic-ring power has integer coordinates.
- A statement that excludes \(F_n(A)=y^2+1\) takes an arbitrary
  \(y:\mathbf N\); it is not a bounded search and not merely the negation of
  one selected existential witness.
- The #139 valuation declaration is only an \(F\)-form theorem.  Paper
  notation may use \(P=2A\) and \(V_N(P,-1)=2F_N(A)\), but this crosswalk
  does not assert an arbitrary-integer-\(P\) theorem.
- The paper may use conventional Pell notation only with the exact
  quadratic-ring coordinate map recorded in
  [source-theorem.md](source-theorem.md).

## 2. Theorem inventory

### SS17: pure fixed-index theorem

- **Plain theorem.**  For all \(A,y\in\mathbf N\),
  \(A\equiv2\pmod8\) implies \(F_{17}(A)\ne y^2+1\).
- **Lean theorem.**
  `Erdos364.no_sm2LucasReal_seventeen_square_of_mod_eight_two`
  ([source](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L2015-L2050)).
- **Source record consumed.**  None; this is source-independent.
- **Reconstruction map.**  \(A=8k+2\), followed by the exact degree-17
  polynomial/Jacobi chain.
- **Proof and certificate.**
  `Sm2LowerSquareOuterSeventeen.lean`,
  `outer-seventeen-certificate.md`, and
  `outer17_verify.gp`.
- **Allowed wording.**  “The fixed-index shifted-square obstruction at
  \(17\).”
- **Forbidden strengthening.**  No claim outside \(A\equiv2\pmod8\), no
  other prime, and no source terminal follows from this row alone.

### SS41: pure fixed-index theorem

- **Plain theorem.**  For all \(A,y\in\mathbf N\),
  \(A\equiv2\pmod8\) implies \(F_{41}(A)\ne y^2+1\).
- **Lean theorem.**  `Erdos364.ss41_shiftedSquare_impossible`
  ([source](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13685-L13708)).
- **Source record consumed.**  None; this is source-independent.
- **Reconstruction map.**  \(A=2\) is handled separately modulo \(23\);
  every other \(A\equiv2\pmod8\) is uniquely \(8j+10\) and enters the
  specialization-safe integer-Jacobi chain.
- **Proof and certificate.**
  `Sm2LowerSquareOuterFortyOne.lean`,
  `outer-forty-one-certificate.md`, the local/telescope certificates, and
  `outer41_verify.gp`.
- **Allowed wording.**  “The fixed-index shifted-square obstruction at
  \(41\), including the boundary \(A=2\).”
- **Forbidden strengthening.**  The main \(8j+10\) proof path must not be
  presented as covering \(A=2\); the public theorem covers it through a
  separate formal branch.

### Phase-strengthened SS17

- **Plain theorem.**  For all \(A,y\in\mathbf N\),
  \(A\equiv2\pmod4\) implies \(F_{17}(A)\ne y^2+1\).
- **Lean theorem.**
  `Erdos364.no_sm2LucasReal_seventeen_square_of_mod_four_two`
  ([source](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean#L119-L141)).
- **Source record consumed.**  None.
- **Reconstruction map.**  The \(2\bmod8\) branch uses SS17; the
  \(6\bmod8\) branch uses the exact recurrence modulo \(8\).
- **Proof and certificate.**  `ShiftedSquarePropagation.lean` and the
  deterministic propagation replay.
- **Allowed wording.**  “SS17 extends to the natural
  \(A\equiv2\pmod4\) phase.”
- **Forbidden strengthening.**  Not a theorem for arbitrary \(A\).

### Phase-strengthened SS41

- **Plain theorem.**  For all \(A,y\in\mathbf N\),
  \(A\equiv2\pmod4\) implies \(F_{41}(A)\ne y^2+1\).
- **Lean theorem.**
  `Erdos364.no_sm2LucasReal_fortyOne_square_of_mod_four_two`
  ([source](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean#L143-L163)).
- **Source record consumed.**  None.
- **Reconstruction map.**  The \(2\bmod8\) branch uses SS41, including its
  \(A=2\) dispatch; the \(6\bmod8\) branch is elementary recurrence
  arithmetic.
- **Proof and certificate.**  `ShiftedSquarePropagation.lean` and the
  deterministic propagation replay.
- **Allowed wording.**  “SS41 extends to the natural
  \(A\equiv2\pmod4\) phase.”
- **Forbidden strengthening.**  Not a theorem for arbitrary \(A\).

### Odd-index composition

- **Plain theorem.**  For \(A,m,n\in\mathbf N\) with \(n\) odd,
  \[
  F_{mn}(A)=F_m(F_n(A)).
  \]
- **Lean theorem.**  `Erdos364.sm2LucasReal_mul_of_odd_right`
  ([source](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean#L165-L202)).
- **Source record consumed.**  None.
- **Reconstruction map.**  Compare the real coordinates of
  \(\varepsilon^{mn}=(\varepsilon^n)^m\) using the same plus-sign
  norm-minus-one recurrence.
- **Proof and certificate.**  Kernel proof in
  `ShiftedSquarePropagation.lean`; deterministic replay includes a hostile
  even-inner-index counterexample.
- **Allowed wording.**  “Composition holds for an odd inner index in this
  recurrence convention.”
- **Forbidden strengthening.**  Unrestricted composition is false.

### Retained odd-index factor theorem

- **Plain theorem.**  For all \(A,n,y\in\mathbf N\),
  \[
  A\equiv2\pmod4,\quad n\text{ odd},\quad
  (17\mid n\ \text{or}\ 41\mid n)
  \Longrightarrow F_n(A)\ne y^2+1.
  \]
- **Lean theorem.**
  `Erdos364.no_sm2LucasReal_shiftedSquare_of_odd_index_factor`
  (the retained #119 declaration in
  [`ShiftedSquarePropagation.lean`](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean)).
- **Source record consumed.**  None.
- **Reconstruction map.**  Write \(n=pq\), prove \(q\) odd, transport the
  phase to \(F_q(A)\), compose, and apply the strengthened fixed-\(p\)
  theorem for \(p=17\) or \(41\).
- **Proof and certificate.**  `ShiftedSquarePropagation.lean`,
  `shifted-square-propagation-lamport.md`, and the deterministic replay.
- **Allowed wording.**  “The retained odd-index branch excludes indices
  divisible by \(17\) or \(41\) in the \(2\bmod4\) phase.”
- **Forbidden strengthening.**  It is not the all-positive theorem by
  itself, and it says nothing about another prime factor.

### Exact positive-even-index valuation

- **Plain theorem.**  For \(A,N\in\mathbf N\),
  \[
  A\equiv2\pmod4,\quad N>0,\quad N\text{ even}
  \Longrightarrow v_2(F_N(A)-1)=2v_2(N)+1.
  \]
- **Lean theorem.**
  `Erdos364.sm2LucasReal_sub_one_padicVal_two_of_positive_even`
  ([source](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean)).
- **Source record consumed.**  None.
- **Reconstruction map.**  Strong induction on \(N=2m\) uses the separate
  identities \(F_{2m}-1=2F_m^2\) for odd \(m\) and
  \(F_{2m}-1=2(F_m-1)(F_m+1)\) for even \(m\).
- **Proof and certificate.**  The focused Lean proof, the Lamport proof, and
  exact V/F replay rows for both \(P\bmod16\) phases.
- **Allowed wording.**  “Every positive even index has the stated exact
  two-adic valuation in the \(2\bmod4\) phase.”
- **Forbidden strengthening.**  Not an arbitrary-\(A\) or zero-index
  theorem, and not an unrestricted \(U_{N/2}\) identity.

### Free positive-even-index shifted-square theorem

- **Plain theorem.**  For all \(A,N,y\in\mathbf N\),
  \[
  A\equiv2\pmod4,\quad N>0,\quad N\text{ even}
  \Longrightarrow F_N(A)\ne y^2+1.
  \]
- **Lean theorem.**
  `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_even_index`
  ([source](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean)).
- **Source record consumed.**  None.
- **Reconstruction map.**  A natural square has even two-adic valuation,
  whereas the preceding valuation theorem is odd.
- **Allowed wording.**  “Every positive even recurrence index is excluded
  in the \(2\bmod4\) phase.”
- **Forbidden strengthening.**  This does not alter an odd-exponent source
  terminal or furnish a source packet adapter.

### All-positive-index factor theorem

- **Plain theorem.**  For all \(A,N,y\in\mathbf N\),
  \[
  A\equiv2\pmod4,\quad N>0,\quad
  (17\mid N\ \text{or}\ 41\mid N)
  \Longrightarrow F_N(A)\ne y^2+1.
  \]
- **Lean theorem.**
  `Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_index_factor`
  ([source](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean)).
- **Source record consumed.**  None.
- **Reconstruction map.**  Split \(N\) into its retained odd branch and its
  free positive-even branch; the divisor is only used in the odd branch.
- **Proof and certificate.**  `ShiftedSquarePropagation.lean`,
  `shifted-square-propagation-lamport.md`, and the deterministic replay.
- **Allowed wording.**  “All positive indices divisible by \(17\) or \(41\)
  are excluded in the \(2\bmod4\) phase.”
- **Forbidden strengthening.**  Not all positive indices and not a theorem
  for primes other than \(17\) and \(41\).

### Norm-minus-one Pell-unit corollaries

- **Free even Lean theorem.**
  `Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index`.
  Under the negative-Pell equation, \(u\equiv2\pmod4\), positive even
  \(N\), and arbitrary \(y\), its real coordinate is not \(y^2+1\).
- **All-positive Lean theorem.**
  `Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor`.
  Under the same equation and phase, positive \(N\) divisible by \(17\) or
  \(41\) has real coordinate not \(y^2+1\).
- **Source record consumed.**  Only the displayed negative-Pell equation;
  no packet, fundamentality, rank, or squarefreeness record.
- **Reconstruction map.**  The exact power-coordinate theorem identifies
  the integer real coordinate with \(F_N(u)\).
- **Proof and certificate.**  `ShiftedSquarePropagation.lean` and
  [source-theorem.md](source-theorem.md).
- **Allowed wording.**  The all-positive conventional theorem quoted in
  `source-theorem.md`, with the free even corollary stated separately.
- **Forbidden strengthening.**  No analytic or differently normalized Pell
  sequence may be substituted, and no source terminal follows without its
  own unchanged hypotheses.

### Complete outer-17 consequence

- **Plain theorem.**  Every complete source in the priority outer-\(17\)
  family is impossible.
- **Lean theorem.**  `Erdos364.noSm2OuterSeventeenBlocks : Erdos364.NoSm2OuterSeventeenBlocks`
  ([source](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L2052-L2063)).
- **Source record consumed.**
  `Sm2LowerSquareUpperSourceGenerator.OuterSeventeenPacket`.
- **Reconstruction map.**  Its same witness has \(A\equiv2\pmod8\) and
  \(F_{17}(A)=\texttt{allocation.y}^2+1\).
- **Proof and certificate.**  The exact packet definition, SS17, the
  reconciled outer-17 certificate, and its GP replay.
- **Allowed wording.**  “\(17\) divides the selected outer exponent.”
- **Forbidden strengthening.**  Never “the upper kernel is \(17\).”

### Selected-41 outer consequence

- **Plain theorem.**  A complete outer-large source satisfying the additional
  hypothesis \(41\mid(2t+1)\) is impossible.
- **Lean theorem.**  `Erdos364.no_outerLarge_selected_fortyOne`
  ([source](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13938-L13951)).
- **Source record consumed.**  `OuterLargePacket` plus a separate explicit
  \(41\)-divisibility hypothesis.
- **Reconstruction map.**  Divide the exact outer exponent by \(41\);
  reconstruct the same intermediate \(A+B\sqrt K\), its \(2\bmod8\) phase,
  and the original source witness.
- **Proof and certificate.**  The private same-witness reconstruction,
  SS41, and the fixed-41 proof/certificates.
- **Allowed wording.**  “The outer-selected \(41\) slice is excluded.”
- **Forbidden strengthening.**  This is not
  `NoSm2OuterLargeBlocks`; \(41\) is not identified with the packet's
  unrelated existential prime.

### Selected-41 rank consequence

- **Plain theorem.**  A complete rank-defect source satisfying
  \(41\mid\operatorname{pellRank}(K)\) is impossible.
- **Lean theorem.**  `Erdos364.no_rankDefect_selected_fortyOne`
  ([source](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13953-L13967)).
- **Source record consumed.**  `RankDefectPacket` plus a separate explicit
  \(41\)-divisibility hypothesis.
- **Reconstruction map.**  Divide the exact Pell rank by \(41\);
  reconstruct the same intermediate \(A+B\sqrt K\), its \(2\bmod8\) phase,
  and the original source witness.
- **Proof and certificate.**  The private same-witness reconstruction,
  SS41, and the fixed-41 proof/certificates.
- **Allowed wording.**  “The rank-selected \(41\) slice is excluded.”
- **Forbidden strengthening.**  This is not
  `NoSm2RankDefectBlocks`; it is distinct from the outer-selected slice.

## 3. Mandatory prime-semantics table

Let

\[
E=2\,\texttt{outerIndex}+1,\qquad
R=\operatorname{pellRank}(K).
\]

| Symbol/phrase | Exact object | Divides | Source family | May be called |
|---|---|---|---|---|
| outer selected prime \(p\) | existential prime in an outer packet, or the fixed divisor explicitly supplied to an adapter | \(E\) | `OuterSeventeenPacket`, `OuterLargePacket` | outer-exponent prime |
| explicit outer divisor \(41\) | the separate hypothesis `41 ∣ E`; not identified with the packet existential | \(E\) | selected-41 outer slice | outer-exponent divisor \(41\) |
| upper-kernel prime \(q\) | a prime satisfying \(q\mid K=\texttt{data.upperKernel}\) | \(K\) | kernel arithmetic | upper-kernel prime |
| rank selected prime \(p\) | existential prime in `RankDefectPacket`, or the fixed divisor explicitly supplied to an adapter | \(R\) | `RankDefectPacket` | rank prime |
| explicit rank divisor \(41\) | the separate hypothesis `41 ∣ R`; not identified with the packet existential | \(R\) | selected-41 rank slice | rank divisor \(41\) |

### Exact implication ledger

- `pellRank_dvd_kernel` proves \(R\mid K\)
  ([source](../../Erdos364/SquareMiddle/PellDivisibilityRank.lean#L5-L23)).
  Therefore a rank prime is also an upper-kernel prime.  The converse is not
  proved.
- No general implication from an outer-exponent prime to an upper-kernel
  prime or rank prime is proved.  The complete outer-17 packet is stronger
  evidence against such a conflation: it records
  \(17\mid E\), \(17\nmid K\), and \(17\nmid R\).
- From the exact full source index \(N=RE\), every divisor of \(R\) or \(E\)
  divides \(N\).  This is the only cross-family divisibility implication used
  by the direct propagation audit.
- Neither selected-41 adapter proves that its explicit \(41\) equals the
  existential packet-selected prime.  The adapters deliberately do not use
  that existential.
- The unqualified phrase “selected prime” is forbidden in the manuscript.
  It must be qualified as outer-exponent, upper-kernel, or rank.

## 4. Quantifier and boundary audit

| Check | Exact disposition |
|---|---|
| `Nat` versus `Int` | Recurrence inputs and \(y\) are `Nat`; quadratic-ring coordinates are `Int`. |
| \(A\bmod8=2\) versus \(A\bmod4=2\) | Pure SS17/SS41 use modulo \(8\); phase-strengthened, retained odd, and #139 all-positive results use modulo \(4\). |
| fixed index versus divisible index | SS17/SS41 are fixed-index; the all-positive propagated theorem requires \(N>0\) and explicit \(17\mid N\) or \(41\mid N\). Its even branch is stronger: it needs no divisor. |
| existential \(y\) versus all \(y\) | Pure and propagated theorems take arbitrary \(y\); source adapters substitute the same retained `allocation.y`. |
| same witness | Each source reconstruction identifies the intermediate power with the original source point before taking real coordinates. A residue-class representative alone is insufficient. |
| packet existence versus terminal universal | A packet describes one retained source profile. `NoSm2OuterSeventeenBlocks` universally negates every complete outer-17 packet. The selected-41 theorems are conditional slice exclusions, not universal terminal proofs. |
| explicit \(41\) hypothesis | Required separately by both selected-41 public adapters. |
| \(A=2\) boundary | SS41 dispatches \(A=2\) separately modulo \(23\); the main Jacobi parameter \(A=8j+10\) does not include it. |
| full source index | The unchanged orbit record retains an odd \(N\) and the exact same-centre power. The all-positive sequence theorem does not change that retained source condition; `source-theorem.md` adds no duplicate packet wrapper. |

## 5. Paper-scope documentation reconciliation

The audit distinguishes current authority from dated historical snapshots.
Historical text is preserved when it records a genuine earlier obstruction or
boundary.

| File or surface | Classification | Disposition |
|---|---|---|
| `outer-seventeen-certificate.md` | current certificate, formerly stale | Reconciled in this tranche: its human/GP provenance is retained and Section 9 now records the maintained Lean theorem and complete adapter. |
| `outer-forty-one-certificate.md` | current certificate | Already contains an explicit superseding maintained-theorem section and the correct selected-slice ceiling. |
| `outer-forty-one-jacobi-certificate.md` | `SUPERSEDED_STATUS_TEXT` in early dated sections | Preserve as tranche history. Statements that SS41 or its adapters remain open are not current authority; use the later maintained Lean file and the fixed-41 certificate. |
| `outer-forty-one-jacobi-handoff.md` | `SUPERSEDED_STATUS_TEXT` | Dated handoff, not paper status authority. |
| `next-steps-handover-2026-07-28.md` | `SUPERSEDED_STATUS_TEXT` | Its outer-17 “open/0 of 4” prompt is historical and is expressly superseded by `problem.md`. |
| `leaf-closure-spine-2026-08-03.md` | current terminal snapshot with historical planning prose | Its phrase “closes the first remaining upper prime sector” may not be reused as a whole-packet claim. The file's explicit terminal table remains correct. |
| `problem.md` | current mathematical status authority | Correctly records outer-17 proved and the other three terminals open. Its old PR #76 process pointer is not theorem or paper authority. |
| `Erdos364.lean` and named Lean modules | current formal authority | Root imports the fixed-17, fixed-41, and #119/#139 propagation surface. |

No current authority claims `2/4`, whole OuterLarge closure, whole
RankDefect closure, leaf closure, canonical acceptance, or Ledger admission.

## 6. Manuscript wording gate

Approved:

> Let \(\varepsilon=u+v\sqrt K\) be a positive norm-minus-one Pell unit with
> \(u\equiv2\pmod4\).  If \(N>0\) is divisible by \(17\) or \(41\),
> then the real coordinate of \(\varepsilon^N\) is not one more than a
> square.

Approved source consequences:

```text
complete outer-17 source family impossible;
outer-selected 41 slice impossible under 41 | (2*outerIndex+1);
rank-selected 41 slice impossible under 41 | pellRank(K).
```

Forbidden:

```text
we close OuterLarge
we close RankDefect
the upper kernel 17/41
the selected prime is 41
all admissible selected primes are covered
all positive indices are covered without the stated 17/41 divisor
packet count equals global coverage
the fixed 17/41 results close the sm2LowerSquare leaf
```

The paper must lead with the recurrence and Pell-unit theorems.  Packet,
allocation, generator, `OuterSeventeenPacket`, `OuterLargePacket`, and
`RankDefectPacket` belong only in this formal crosswalk or an implementation
appendix.

## 7. Claim ceiling

This crosswalk supports:

- the source-independent fixed-\(17\), fixed-\(41\), phase, composition,
  retained odd-index, exact even-valuation, free even, all-positive, and
  Pell-unit theorems;
- the complete maintained outer-17 consequence;
- the two explicit selected-41 source slices.

It does not prove a uniform selected-prime theorem, either remaining
non-atomic terminal, the atomic terminal, the complete leaf, Erdős 364,
canonical acceptance, Ledger admission, publication priority, or manuscript
acceptance.
