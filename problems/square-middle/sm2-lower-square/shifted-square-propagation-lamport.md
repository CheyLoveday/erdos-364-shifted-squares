# All-positive-index shifted-square propagation at 17 and 41

## Status and authority

This note is the complete human proof and theorem crosswalk for Issue #139.
It retains the Issue #119 odd-index propagation theorem as one branch and
adds the independent positive-even-index valuation theorem. It is
source-independent: it uses the maintained Dickson--Lucas recurrence and the
already maintained fixed-`17` and fixed-`41` obstructions. It does not change
any packet, terminal, canonical, Ledger, or manuscript status.

### 0) Problem restatement (brief)

For `A,n : Nat`, define

```text
F_0(A) = 1,
F_1(A) = A,
F_(n+2)(A) = 2*A*F_(n+1)(A) + F_n(A).
```

The maintained Lean definition is `sm2LucasReal A n`.  Prove

```text
A % 4 = 2,
n > 0,
17 divides n or 41 divides n
  -> F_n(A) != y^2 + 1
```

for every natural square witness `y`, and then transport the theorem to the
real coordinate of an arbitrary natural norm-minus-one Pell point.

### 1) Assumptions ledger

- Assumption: `A,n,y : Nat`.
  - Used in: every recurrence and modular statement.
  - If false, degrade to: an integer-index or integer-square theorem would
    require separate definitions and cast adapters and is not claimed here.
- Assumption: `A % 4 = 2`.
  - Used in: the odd-index phase lemma and both fixed-prime wrappers.
  - If false, degrade to: no obstruction is claimed outside this phase.
- Assumption for the retained odd branch: `Odd n`.
  - Used in: phase preservation, norm-minus-one preservation under the inner
    power, quotient oddness, and the composition theorem.
  - If false, that branch does not apply: composition with the same plus-sign
    recurrence is false in general. The separate positive-even branch is
    supplied in Section 3.
- Assumption: `17 ∣ n ∨ 41 ∣ n`.
  - Used in: selecting the maintained fixed-prime obstruction.
  - If false, degrade to: no uniform prime-index theorem is claimed.
- Assumption for the Pell form: `u^2 + 1 = K*v^2` and `u % 4 = 2`.
  - Used in: identifying the real coordinate of `(u+v*sqrt(K))^n` with
    `F_n(u)` and applying the sequence theorem.
  - If false, degrade to: the maintained power-coordinate identity is not
    available for an arbitrary quadratic-ring element.
- Maintained inputs:
  - `no_sm2LucasReal_seventeen_square_of_mod_eight_two`;
  - `ss41_shiftedSquare_impossible`;
  - `sm2UpperNegativeUnit_pow_re`;
  - `sm2UpperNegativeUnit_pow_coordinates`;
  - `sm2LucasReal_odd_negative_equation`.
  - Used in: L3, L4, and L7 below.
  - If false, degrade to: Issue #119 cannot proceed; it does not reprove or
    replace these inputs.

### 2) Retained odd-index branch (#119)

- L1: PROVED
  - Statement: if `A % 4 = 2` and `n` is odd, then
    `F_n(A) % 4 = 2`.
  - Proof: modulo four, `2*A = 0`.  The recurrence therefore gives

    ```text
    F_(j+2)(A) = F_j(A) mod 4.
    ```

    Write `n=2*k+1` and iterate this two-step equality until reaching
    `F_1(A)=A=2 mod 4`.
  - Lean: `sm2LucasReal_mod_four_two_of_odd`.
  - Notes: oddness is exact.  For `A=2,n=2`, `F_2(2)=9=1 mod 4`.

- L2: PROVED
  - Statement: if `A % 8 = 6` and `n % 4 = 1`, then
    `F_n(A) % 8 = 6`.
  - Proof: modulo eight, `2*A=4`.  Expanding four recurrence steps gives

    ```text
    F_(j+4)(A)
      = 72*F_(j+1)(A) + 17*F_j(A)
      = F_j(A) mod 8.
    ```

    Thus the sequence is four-periodic modulo eight.  Reduction to index one
    gives `F_n(A)=F_1(A)=A=6 mod 8`.
  - Lean: `sm2LucasReal_mod_eight_six_of_index_mod_four_one`.
  - Notes: the initial residues are `1,6,1,2`; the theorem must not reuse the
    distinct `A=2 mod 8` residue table.  The index condition is exact:
    `A=6,n=3` gives `F_3(6)=882=2 mod 8`.

- L3: PROVED
  - Statement: the maintained fixed-`17` and fixed-`41` obstructions extend
    from `A % 8 = 2` to `A % 4 = 2`.
  - Proof: `A % 4 = 2` implies exactly `A % 8 = 2` or `A % 8 = 6`.
    In the first branch, apply the corresponding maintained theorem.  In the
    second, both `17` and `41` are one modulo four, so L2 gives
    `F_p(A)=6 mod 8`.  A natural square modulo eight is `0`, `1`, or `4`, so
    one plus a square is `1`, `2`, or `5`, never `6`.
  - Lean:
    - `no_sm2LucasReal_seventeen_square_of_mod_four_two`;
    - `no_sm2LucasReal_fortyOne_square_of_mod_four_two`.
  - Notes: the square-residue sublemma quantifies over `y` and checks the
    complete residue class `y % 8`; it is not finite evaluation of `A`.

- L4: PROVED
  - Statement: for odd inner index `n`,

    ```text
    F_(m*n)(A) = F_m(F_n(A)).
    ```

  - Proof: put `K=A^2+1` and `eta=A+sqrt(K)`.  Then
    `Norm(eta)=-1`, and the maintained coordinate theorem gives

    ```text
    eta^n = B + C*sqrt(K),
    B = F_n(A),
    C = sm2LucasCoeff A n.
    ```

    Since `n` is odd, the maintained norm equation gives

    ```text
    B^2 + 1 = K*C^2.
    ```

    Hence powers of `B+C*sqrt(K)` have real-coordinate recurrence `F_m(B)`.
    Now

    ```text
    eta^(m*n) = eta^(n*m) = (eta^n)^m.
    ```

    Comparing real coordinates yields the claimed identity.
  - Lean: `sm2LucasReal_mul_of_odd_right`.
  - Notes: the multiplication order is rewritten before `pow_mul`, because
    the inner power must be `eta^n`.  No positivity hypothesis is used.
    Oddness cannot be dropped: at `A=1,m=2,n=2`,
    `F_4(1)=17`, whereas `F_2(F_2(1))=19`.

- L5: PROVED
  - Statement: if `n` is odd and `p` is `17` or `41` with `p ∣ n`, then the
    quotient `q=n/p` is odd.
  - Proof: a divisibility witness writes `n=p*q`.  If `q` were even then the
    product would be even, contrary to `Odd n`.  Lean uses
    `Nat.Odd.of_mul_right` on the exact product equality.
  - Notes: the proof derives oddness of the right factor, rather than merely
    observing that the selected prime is odd.

- L6: PROVED
  - Statement: if `A % 4 = 2`, `n` is odd, and `17 ∣ n ∨ 41 ∣ n`, then
    `F_n(A)` is not one plus a natural square.
  - Proof: select `p` and write `n=p*q`.  L5 gives `Odd q`, L1 gives
    `F_q(A)=2 mod 4`, and L4 gives

    ```text
    F_n(A) = F_p(F_q(A)).
    ```

    Apply the corresponding L3 fixed-prime obstruction at the new parameter
    `F_q(A)`.
  - Lean: `no_sm2LucasReal_shiftedSquare_of_odd_index_factor`.
  - Notes: no assertion is made for even totals, arbitrary primes, or every
    prime congruent to one modulo eight.

- L7: PROVED
  - Statement: if `u^2+1=K*v^2`, `u % 4 = 2`, and `n` satisfies the L6 index
    hypotheses, then the real coordinate of
    `(u+v*sqrt(K))^n` is not one plus a natural square.
  - Proof: the maintained theorem `sm2UpperNegativeUnit_pow_re` identifies
    the integer real coordinate with the natural number `F_n(u)`.  Cast a
    hypothetical equality back to naturals and apply L6.
  - Lean: `normNegativeOneUnit_real_ne_square_add_one_of_index_factor`.
  - Notes: the statement uses the raw quadratic-ring constructor and adds no
    squarefreeness, fundamentality, source, packet, or rank assumptions.

### 3) Positive-even-index valuation and complete local-2 layer (#139)

- E1: PROVED (self-contained doubling identities)
  - Put \(K=A^2+1\) and \(\eta=A+\sqrt K\). Comparing real coordinates
    of \(\eta^{2m}=(\eta^m)^2\), with the norm of \(\eta^m\) separated by
    the parity of \(m\), gives

    \[
    F_{2m}(A)-1=
    \begin{cases}
    2F_m(A)^2,&m\text{ odd},\\
    2(F_m(A)-1)(F_m(A)+1),&m\text{ even}.
    \end{cases}
    \tag{E1}
    \]

  - Lean: private helpers in `ShiftedSquarePropagation.lean`, derived from
    `sm2UpperNegativeUnit_pow_coordinates` and the norm equation. These are
    deliberately separate identities. In particular, they do **not** use
    \(V_{2m}-2=(P^2+4)U_m^2\) without its necessary `m`-even guard.

- E2: PROVED (exact valuation)
  - If \(A\equiv2\pmod4\), then \(F_m(A)\equiv2\pmod4\) for odd \(m\)
    and \(F_m(A)\equiv1\pmod4\) for even \(m\). Thus
    \(v_2(F_m)=1\) in the odd case and \(v_2(F_m+1)=1\) in the even case.
  - Strong induction on positive even \(N=2m\), using (E1), gives

    \[
      \boxed{v_2(F_N(A)-1)=2v_2(N)+1.}
      \tag{E2}
    \]

  - Lean:
    `sm2LucasReal_sub_one_padicVal_two_of_positive_even`.
    Nat-subtraction nonzero obligations are explicit: in the recursive even
    case the induction value forces \(F_m(A)-1\ne0\).
  - Normalization boundary: the formal theorem is only this \(F\)-form.
    Paper/replay notation may put \(P=2A\) and \(V_N(P,-1)=2F_N(A)\), but
    no arbitrary-integer-\(P\) theorem is claimed.

- E3: PROVED (free even nonsquare and all-positive theorem)
  - Squares have even two-adic valuation, whereas (E2) is odd. Hence every
    positive even index is excluded without a `17` or `41` hypothesis.
  - Splitting a positive index by parity combines this free result with the
    retained odd-index theorem:

    \[
    A\equiv2\pmod4,\quad N>0,\quad(17\mid N\ \text{or}\ 41\mid N)
    \Longrightarrow F_N(A)-1\text{ is not a square}.
    \tag{E3}
    \]

  - Lean:
    `no_sm2LucasReal_shiftedSquare_of_positive_even_index`,
    `no_sm2LucasReal_shiftedSquare_of_positive_index_factor`, and the
    corresponding two Pell-unit corollaries.

- E4: PROVED (complete recurrence-local layer at \(2\))
  - For \(A\equiv2\pmod8\), the four residues of \(F_N(A)\) for
    \(N\bmod4=0,1,2,3\) are \((1,2,1,6)\). For
    \(A\equiv6\pmod8\), they are \((1,6,1,2)\). The complementary table is
    formalized privately by `sm2LucasReal_mod_eight_six`; the existing
    `sm2LucasReal_mod_eight` is the first table.
  - Positive even indices are rejected by E2. At odd indices, the cross
    phases \((A\bmod8,N\bmod4)=(2,3),(6,1)\) have
    \(F_N(A)-1\equiv5\pmod8\), so they are neither integral squares nor
    \(\mathbf Q_2\)-squares. The surviving phases \((2,1),(6,3)\) have
    \(F_N(A)-1\equiv1\pmod8\), hence are squares in \(\mathbf Z_2^\times\).
  - The exact **2-adically admissible** region is therefore the odd surviving
    phase region, with no `17`/`41` condition. After E3, the smaller
    unresolved paper-level region also requires \(17\nmid N\) and
    \(41\nmid N\). Local square admissibility is not an integral or global
    square claim.

### 4) Main theorem

- PROVED
- Full proof: the retained odd branch uses L1--L7. Section 3 independently
  excludes every positive even index by the exact valuation E2. Splitting by
  parity proves E3, and the same all-index split transfers through the exact
  real-coordinate identity for every natural norm-minus-one Pell point.

The paper-leading form is therefore:

> Let `A=2 mod 4` and `N>0`. If `17` divides `N` or `41` divides `N`, then
> `F_N(A)-1` is not a natural square.

### 5) If refuted: repaired statement

- Not applicable.  The stated theorem and every hinge lemma are proved.
- The hostile even-inner-index computation records why L4 is not extended to
  unrestricted inner indices; E1 is the separate, valid even-total route.

### 6) Verification plan for the verifier role

- Independently re-derive L4 from quadratic-unit powers, checking the order
  of `m*n`, `n*m`, and the application of `pow_mul`.
- Check the two modular sequences independently, including `A=2`, `A=6`,
  indices `0`, `1`, `2`, `3`, `17`, and `41`.
- Check the quotient-parity step in both divisibility branches.
- Plug in the boundary indices `n=17` and `n=41` and composite odd multiples.
- Independently re-derive both E1 identities from the quadratic-unit norm,
  checking that the `m`-odd and `m`-even cases are not conflated.
- Check the strong-induction decrease from `N=2m` to positive even `m`, the
  `Nat` subtraction nonzero proof, and the exact use of
  `padicValNat.mul`/`padicValNat.pow`.
- Check representative valuation rows for `P=4,12,20` and
  `N=2,4,6,8,10,12,16,24`, including direct `V=2F` recurrence evaluation.
- Check the entire local-2 table, the cross-phase witnesses
  `F_3(2)-1=37` and `F_5(6)-1=128765`, and the surviving witness
  `26^2 < F_5(2)-1=681 < 27^2`.
- Confirm the counterexamples:
  - `(A,m,n)=(1,2,2)` breaks unrestricted composition;
  - `(A,n)=(2,2)` breaks the mod-four conclusion without oddness;
  - `(A,n)=(6,3)` breaks the mod-eight conclusion outside index one mod four.
- Confirm the guarded formula controls: for `P=4,N=2,m=1`,
  `V_N-2=16` whereas `(P^2+4)U_m^2=20`; for `N=4,m=2`, both are `320`.
- Confirm `A=2,N=0` gives `F_N-1=0` while both `17` and `41` divide zero,
  so positivity is load-bearing; at `N=2`, the wrong `A mod 4` phases
  `A=0,1,3` have observed valuations `0,1,1`, and the additional
  `A=4` control has valuation `5`, never the target `3`.
- Run the deterministic replay in
  `experiments/shifted_square_propagation/replay.py` and compare it byte-for-
  byte with `expected.json`.
- Compile the focused module, the root, and the full project at one immutable
  commit; audit every public theorem with `#print axioms`.

## Theorem-to-manuscript crosswalk

| Manuscript role | Lean theorem | Claim |
|---|---|---|
| Odd-index phase | `sm2LucasReal_mod_four_two_of_odd` | `F_n(A)=2 mod 4` |
| Dyadic easy phase | `sm2LucasReal_mod_eight_six_of_index_mod_four_one` | `F_n(A)=6 mod 8` |
| Fixed instance 17 | `no_sm2LucasReal_seventeen_square_of_mod_four_two` | strengthened SS17 |
| Fixed instance 41 | `no_sm2LucasReal_fortyOne_square_of_mod_four_two` | strengthened SS41 |
| Composition | `sm2LucasReal_mul_of_odd_right` | `F_(mn)(A)=F_m(F_n(A))` |
| Retained odd theorem | `no_sm2LucasReal_shiftedSquare_of_odd_index_factor` | odd-index factor obstruction |
| Exact even valuation | `sm2LucasReal_sub_one_padicVal_two_of_positive_even` | `v2(F_N(A)-1)=2*v2(N)+1` |
| Free even theorem | `no_sm2LucasReal_shiftedSquare_of_positive_even_index` | every positive even index is excluded |
| Paper-leading theorem | `no_sm2LucasReal_shiftedSquare_of_positive_index_factor` | all-positive factor obstruction |
| Free even Pell corollary | `normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index` | even real-coordinate obstruction |
| All-positive Pell corollary | `normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor` | all-positive real-coordinate obstruction |

If Issue #139 survives independent review, the propagated theorem should be
stated before the two fixed-prime inputs in the manuscript introduction.  The
fixed-prime theorems are its foundational instances.  This note does not open
or modify the manuscript.

## Deterministic replay contract

The replay is a regression oracle, not a proof.  It uses Python standard-
library arbitrary-precision integers and checks:

```text
composition: A=0..16, m=0..8, odd n=1..15       1,224 cases
mod-four:    A=0..63 with A=2 mod4, odd n<=41     336 cases
mod-eight:   A=0..63 with A=6 mod8, n=17 or 41     16 cases
even-value:  A=2,6,10; N=2,4,6,8,10,12,16,24        24 cases
local-two:   both A mod8 phases, all N mod4 phases   8 cases
hostile:     composition, zero, wrong phase, and guarded-U controls
```

For every even-value row it independently computes the (V)-recurrence with
`P=2*A`, checks `V_N=2*F_N`, and records both `P=4 mod 16` and
`P=12 mod 16` phases.  The local table records exactly one of
`EVEN_ODD_VALUATION_REJECTION`, `ODD_UNIT_CLASS_REJECTION`, or
`ODD_2ADIC_ADMISSIBLE` for each row.  It uses no randomness, network,
factorisation, floating point, external package, or source-shaped packet
fixture.  The runtime budget is 30 seconds, the memory budget is 256 MiB, and
output is capped at 8 KiB.

## Claim ceiling

This is a source-independent infinite-index sequence theorem and Pell-unit
corollary.  It does not:

- prove a uniform `SS_p` theorem;
- add `p=73` or any other fixed prime;
- extend odd-inner-index composition to an unrestricted even inner index;
- enlarge the existing odd-exponent source-terminal exclusion merely from the
  free even-index theorem;
- add or change a packet adapter;
- close `NoSm2OuterLargeBlocks`, `NoSm2RankDefectBlocks`, or
  `NoSm2AtomicResiduals`;
- close the `sm2LowerSquare` leaf or Erdős 364;
- alter the maintained terminal count `1/4`;
- create a Ledger or canonical result;
- authorize manuscript or publication status.
