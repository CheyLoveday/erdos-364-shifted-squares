# Semantic review of published Paper I v1.0.1

**Review completed on 26 October 2026. No blocking mathematical gap or
paper-to-Lean statement mismatch was identified in the twelve numbered results.**
The correspondence is mixed: some conclusions have Lean proofs, others have
written human proofs with exact finite certificates. Absence of a Lean version
of a human argument is a formalisation gap, not evidence of a mathematical gap.

Reviewer: **OpenAI Codex**, automated source and mathematical-argument review
requested by Chey. This is not external human peer review, an independent human
sign-off, or a fresh six-checker run. The author retains mathematical and
publication responsibility. The assessment concerns the published statements
and their proof routes, not every research result in the current Lab.

## Exact objects reviewed

- Article: [published v1.0.1 reading copy](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/5cf294a29a6858e031b769381ba54bd316031acc/papers/shifted-square-17-41/manuscript/revision/paper_1_github.md),
  dated 30 September 2026. Its authoritative Pandoc source is
  `papers/shifted-square-17-41/manuscript/revision/paper_1.md`, SHA-256
  `c439887383fba9a1b18a98a10fa4a04780fba70a2aabfcbe909d47280b492bdd`.
  These bytes were compared with tag `v1.0.1` and public main at
  `5cf294a29a6858e031b769381ba54bd316031acc`.
- Formal source: the public files at that same commit, their definitions,
  signatures and relevant proof blocks; the retained
  [elaborated signatures and axiom output](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/5cf294a29a6858e031b769381ba54bd316031acc/papers/shifted-square-17-41/verification/records/2026-09-10-standalone/axioms.json);
  and the separately frozen Lean 4.35 selection described in the
  [six-checker note](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/verification/LEAN-ASSURANCE-2026-10-25.md).
  The historical printed signatures are evidence from Lean 4.31, not newly
  printed Lean 4.35 output. Source identity and the retained protected comparison
  provide the connection to the three later comparison targets.
  All 61 Lean files in the historical standalone source inventory still match
  the public source snapshot; the historical signature output is therefore
  applicable to those sources, without claiming a new execution.
- Existing correspondence: the [theorem crosswalk reading copy](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md),
  [Hilbert–Jacobi crosswalk reading copy](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/hilbert-jacobi-crosswalk.md), article Appendix B
  and [historical proof record reading copy](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/PROOF_RECORD.md). The historical proof record
  retains its earlier manuscript identity; this review supplies the v1.0.1
  reconciliation instead of rewriting that record.

The following declaration-bearing files are byte-identical in the public
snapshot and frozen Lean 4.35 selection:

| File under `Erdos364/` | SHA-256 |
| --- | --- |
| `DicksonLucas/ShiftedSquarePropagation.lean` | `af4b58e21788cdda136e4f2cac158b6e305f10493c0e7db13c93fb1db7314b0b` |
| `SquareMiddle/Sm2LowerSquareGeneratorRank.lean` | `dc0ccf9d4db51178367a94352d5381011d0a8db79153b2485f25828bf8a46d64` |
| `SquareMiddle/Sm2LowerSquareOuterSeventeen.lean` | `51bb7046da75483126c98f6d5825481823f17503781f2a76e37dba0d943db50a` |
| `SquareMiddle/Sm2LowerSquareOuterFortyOne.lean` | `d0411d0dad4261d43074a4003a97565299e3c521a39ae417b6231adcfe358813` |

Overall, 58 of the 61 selected source files agree. `LeafCompiler.lean` has
the documented Lean 4.35 compatibility change; `PellDivisibilityRank.lean`
and `QuarticPellCohn.lean` contain later Lab additions. This review does not
transfer the six-checker result to all current Lab files or the public
Lean 4.31 environment. The three mechanically compared statements are the
positive-even exclusion, the positive-index 17/41 exclusion, and fixed-41
exclusion. Twelve article results were reviewed semantically; twelve formal
statement comparisons were not run.

## Result-by-result disposition

“Lean conclusion” means the paper's conclusion follows from the named formal
statement with the domain bridges below. It does not mean the article's
particular human proof has been formalised. Every declaration below is in
namespace `Erdos364`; full names and source routes are in the crosswalk.

| Published result | Proof support and semantic disposition |
| --- | --- |
| Theorem 1.1 | Lean conclusion: [all-positive 17/41 theorem](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#all-positive-index-factor-theorem). Requires nonnegative parameter congruent to 2 modulo 4, positive index, and divisibility by 17 or 41. The even and odd proof branches cover the stated domain. |
| Theorem 1.2 | Lean conclusions: [phase-strengthened SS17](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#phase-strengthened-ss17) and [phase-strengthened SS41](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#phase-strengthened-ss41). The hard modulo-8 phase and elementary complementary phase cover the modulo-4 hypothesis. |
| Theorem 1.3 | Lean valuation identity: [exact even-index valuation](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#exact-positive-even-index-valuation); its consequence is [free even-index exclusion](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#free-positive-even-index-shifted-square-theorem). Positivity makes the paper's valuation and natural subtraction agree. No 17/41 divisor is needed. |
| Corollary 1.4 | Lean conclusions: [even-index Pell theorem](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#norm-minus-one-pell-unit-corollaries) and [17/41 Pell theorem](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#norm-minus-one-pell-unit-corollaries), using [power-coordinate identity](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#norm-minus-one-pell-unit-corollaries). These two cases cover the three divisibility alternatives. |
| Corollary 1.5 | Supported by the complete human proof in §§6.2–6.3 and Theorem 1.1. Existing source adapters have stronger allocation hypotheses, so they do not formalise this exact corollary. No missing mathematical step was identified. |
| Proposition 2.1 | Human proof: the four recurrence residue cases and the odd 2-adic unit square criterion. Lean residue arithmetic supports parts of this route; no exact formal theorem about squares in the 2-adic field is claimed. |
| Proposition 3.1 | Human proof: the prescribed local signs contradict Hilbert reciprocity. No Lean Hilbert-reciprocity theorem is claimed. |
| Theorem 3.2 | Human proof: monogenic support control, norm-valuation parity, local neutrality and strict dyadic stability. All five hypotheses are used with their stated scope; see below. |
| Proposition 4.1 | Human proof: the untwisted detector has square residue 4 at odd supporting primes; infinity is neutral; reciprocity forces dyadic product +1. It is not the detecting-unit theorem. |
| Theorem 4.2 | Human proof: Theorem 3.2 with the exact field certificates. The same exclusion conclusion has separate Lean integer-Jacobi proofs: [fixed-17 theorem](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#ss17-pure-fixed-index-theorem) and [fixed-41 theorem](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#ss41-pure-fixed-index-theorem). |
| Lemma 5.1 | Lean conclusion: [odd-inner composition](https://github.com/CheyLoveday/erdos-364-shifted-squares/blob/main/papers/shifted-square-17-41/reading/theorem-formal-crosswalk.md#odd-index-composition). The inner index must be odd; zero outer index is permitted. |
| Proposition 7.1 | Human proof of the uniform Jacobi identity, positive odd denominator and coprimality, including the endpoint. The Lean arithmetic chains support the exclusions; the full published uniform identity is not identified here with one public Lean declaration. |

## Formal statement meaning and boundaries

1. **Recurrence, types and square witnesses.** `sm2LucasReal` has initial
   values 1 and A and the plus-sign recurrence printed in §1.1. The inspected
   top-level signatures quantify over `Nat`; they contain no hidden source
   packet or abstract algebraic typeclass premise. The paper's nonnegative
   integer inputs are identified with naturals. An arbitrary integer square
   is the square of its natural absolute value, so the natural witness in the
   formal exclusion covers negative as well as nonnegative integer witnesses.
   The integer coordinate casts in the Pell theorems are injective.
2. **Subtraction and valuation.** The phase implies A is at least 2. The
   recurrence then gives F_N at least 2 for positive N. Natural truncated
   subtraction therefore agrees with integer subtraction, and F_N minus 1
   is nonzero. The convention for `padicValNat` at zero cannot make Theorem
   1.3 vacuous. The proof uses the separate odd-half and even-half doubling
   identities, with nonzero factors before invoking valuation additivity.
3. **Domain checks.** N = 0 is excluded: F_0 minus 1 is the square 0.
   Divisibility remains essential for the all-positive theorem's odd branch:
   A = 2, N = 1 gives the square 1. The even theorem needs positivity and
   parity, but no prime-index restriction. These are domain checks, not
   counterexamples to any published theorem.
4. **Composition and propagation.** The formal identity orders its arguments
   as `sm2LucasReal (sm2LucasReal A n) m`, exactly F_m(F_n(A)). Oddness of n
   preserves norm minus one; an even inner index fails, for example
   F_4(2) = 161 whereas F_2(F_2(2)) = 163. In propagation, writing an odd N
   as p times q makes q odd and preserves the modulo-4 phase of F_q(A).
   It is the same value F_N(A) that reaches the fixed-index obstruction.
5. **Fixed-41 endpoint and signs.** The formal split is A = 2 or A = 8j + 10.
   The latter enters `outer41MainJacobi`; A = 2 is excluded separately by
   the nonsquare residue 20 modulo 23. The positive-oriented numerator
   minus U_41 has the same character as U_41 because the denominator is
   1 modulo 8. This endpoint proof establishes nonsquareness; it is not a
   formal proof of the endpoint's full character identity. The formal
   square-denominator contradiction also handles Jacobi value zero.
6. **Pell coordinates.** `Zsqrtd.re` is the integer coefficient of 1, not
   the analytic real value of the whole unit. `sm2UpperNegativeUnit_pow_re`
   derives that coefficient from the same norm equation and recurrence.
   No squarefree-radicand or fundamental-unit premise is silently imported
   into Corollary 1.4. Those premises belong to the separate normal form
   in Corollary 1.5.

## Human proof review

### Hilbert criterion and maximality

Theorem 3.2 uses the integral generator and maximal order before transferring
norm parity to prime-ideal valuations. The quotient by x minus theta is
the integer quotient by g(x). Consequently, for each odd rational prime
dividing g(x), there is exactly one supporting prime ideal and its residue
degree is one, including at ramified primes. Since theta has norm 2, it
is a unit there. Thus a square norm gives an even valuation at that specific
prime. The proof does not use the false general inference that a square
global norm makes every ideal valuation even.

The detector b generates the same ideal as theta, so it is an odd-place
unit. The tame Hilbert-symbol formula makes the odd symbols neutral under
the square hypothesis. At the unique real embedding, x is at least 4 and
theta lies strictly between 0 and 4, so the relevant quotient is positive;
complex places contribute +1. At dyadic places the ratio to the reference
value is 1 plus (x minus 4)/(4 minus theta). The strict bound
`4e - d > 2e` is precisely the strong-Hensel threshold. The x = 4 ratio is
1. Equality at the threshold would be insufficient, as the nonsquare
2-adic unit 5 illustrates. The negative reference product then contradicts
reciprocity. No odd-prime local-solubility assertion is needed.

For the two fixed fields, Appendix A.2 first proves maximality by Dedekind's
index criterion at the only possible index primes, 2 and p. The correction
remainder at 2 is 1; at p the residues are 12 and 26, both nonzero. Only
then is Dedekind–Kummer used for the dyadic prime types. The resultant -1
certifies that each printed detector polynomial gives a unit; no full unit
basis, class-group computation or GRH assumption is needed. The strictly
increasing real Dickson expression proves the unique real root and its
location without a numerical root approximation.

Appendix A.1 recovers the required dyadic product from exact rational-prime
characters and reciprocity. The individual dyadic signs in Table 4 are
stronger corroborating data and were not recomputed in this review. Their
individual values are not an unmet premise of the proof route, which uses
the product. The shared detector coefficients mean the Hilbert and Jacobi
routes are not independently discovered certificates.

### Exact Corollary 1.5

The published hypotheses require X at least 2, X minus 1 square, and X squared
plus 1 powerful. They do not require X squared minus 1 powerful. If X were
odd, the upper value would have 2-adic valuation one. Hence X is even; its
lower square forces X congruent to 2 modulo 8. The unique powerful normal
form is K cubed times V squared, with K squarefree, both positive, and no
coprimality requirement between K and V. K is greater than 1 and congruent
to 5 modulo 8.

The proof uses units of the order `Z[sqrt(K)]`, preserving integral
coefficients. Bounded positive units have bounded coefficients, so the
existing unit X + KV sqrt(K) supplies a nonempty finite interval in which
the least unit greater than 1 exists. Division by powers of that least
unit proves generation and uniqueness. Existence of a norm-minus-one unit
forces the generator's norm to be -1 and the exponent N to be positive
and odd. Its coefficients u and v are positive integers; reduction modulo
8 gives v odd and u congruent to 2 modulo 4.

Taking the coefficient of 1 gives the exact same-centre identity
X = F_N(u) = y squared plus 1. Theorem 1.1 therefore excludes 17 and 41
from N. The binomial coefficient congruence in §6.3 and coprimality of u
and K give, for every positive n, K dividing the second coefficient if
and only if K/gcd(K,v) divides n. Thus the displayed R really is the
least positive divisibility index, R divides N, and N = RE with positive
odd R and E. All four published exclusions follow. An upper-kernel prime
need not be a rank or outer-exponent prime.

This supplies the corollary under its exact hypotheses. Using stronger Lean
allocation adapters as a substitute would leave a formal correspondence
gap; the written proof already supplies the mathematics. Formalising this
exact normal form is optional further work, not a missing paper proof.

### Local square criterion and uniform Jacobi bridge

Proposition 2.1 uses an odd unit throughout. Its residue is 1 modulo 8 in
exactly the two listed phase pairs; strong Hensel proves sufficiency and
reduction of odd squares proves necessity. This does not assert solvability
at every odd prime.

For Proposition 7.1, the same unique-support argument applies without any
square assumption on Q = g_p(x)/2. Odd-place unitness of b gives coprimality
of x U_p(x) with the positive odd denominator Q. The tame symbol formula
identifies the odd-place product with that Jacobi symbol. Writing x = 4m
with m congruent to 1 modulo 4 gives Q congruent to -1 modulo m;
reciprocity removes m, and the square factor 4 contributes +1. The case
m = 1 uses the usual denominator-one convention. Real positivity and
dyadic stability did not use the square hypothesis, so reciprocity yields
the uniform value -1, including A = 2. There is no circular use of the
nonsquare conclusion to obtain the character identity.

### Reconciliation with v1.0.0

The source diff retains all twelve result identifiers. The only altered
numbered-result block is Corollary 1.5: the already implied modulo-8 phase
is now derived explicitly, and 17 dividing R is added to its consequence
list. The review above validates both changes. The Sanna specialization
uses parameters a = 2A and b = 1, a nondegenerate sequence, and the
prime-2 clause of Theorem 1.5; the retained doubling proof is self-contained.
Dickson composition retains parameter -1 precisely at an odd inner index.
The Walker discussion uses the same order, generator and divisibility rank;
the binomial proof supplies the claim within the article. This is a
correspondence review, not a literature-wide originality determination.

## Checks performed and assurance interpretation

The current article's embedded verifier was compared byte-for-byte with
`manuscript/revision/anc/verify_fixed_fields.py` and executed unchanged in
a temporary materialisation of public commit `5cf294a`. Command from its root:

```sh
python3 -B papers/shifted-square-17-41/manuscript/revision/anc/verify_fixed_fields.py
```

Python 3.13.12, SymPy 1.14.0; exit code 0, output:

```text
SymPy 1.14.0
p=17: polynomial, index and reference checks passed
p=41: polynomial, index and reference checks passed
FIXED_FIELDS_OK
```

Verifier SHA-256:
`82e223275f0df061a8a34e6aa8b16be5bbbf8f352245510933d06b01556c80a1`.

This checks the printed irreducibility, discriminant, resultant, maximality
and reference-character inputs. It is exact finite-certificate replay, not
a parameter search or a substitute for the quantified arguments above.
No Lean build, six-checker execution, direct dyadic-symbol computation,
manuscript render or remote computation was performed for this review.

For the release-profile semantic portion, the scope/specification,
statement-and-definition correspondence, proof mapping and boundary analysis
(A01–A04 and A07) are **PASS for the scope documented here**. A13 records
the limitations. The retained formal verification remains **PASS for its
separate frozen selection**. This document does not assert that a fresh
end-to-end release-profile reproduction (A05–A11) has been completed.

The service receipt's `assurance_status: INCOMPLETE` is preserved verbatim.
At the recorded service implementation, `ProjectConfiguration.observation`
sets that field to `INCOMPLETE` even when verification passes. It is not
a computed diagnosis of a missing mathematical proof, and a documentation
review cannot change an immutable execution receipt. Consumer assessment
must state its own scope and evidence, as this review does. The public
metadata subset is still not a complete Lean 4.35 replay bundle. A new
claim of independent clean reproduction would require the exact retained
inputs, environment/cache provenance and successful reproduction evidence;
an empty cache is not intrinsically required. Older Lean 4.31 records are
not relabelled as such a run.

| Remaining distinction | Disposition |
| --- | --- |
| Mathematical gap in the twelve stated results | None identified by this completed automated semantic and argument review. This is a review finding, not infallible certification. |
| Exact Lean versions of the human Hilbert/maximality proof, full Corollary 1.5, local square criterion and uniform character statement | Not claimed; the paper supplies human proofs. Additional formalisation is optional. |
| Independent external human mathematical review | Not supplied by this review and not required by the selected release profile. It would strengthen assurance; no new publication hold is imposed. |
| New complete Lean 4.35 public replay / independent clean reproduction | Not performed here. This evidence/reproducibility limitation is separate from the mathematical review and the six successful executions. |
| General prime indices, all residual Pell families, Erdős 364 | Outside the published theorem scope; remain non-claims. |

Useful primary checks for the human arguments include
[Dedekind's index criterion, Theorem 1.1](https://arxiv.org/pdf/1809.04122),
[Dedekind–Kummer, Theorem 6.14](https://math.mit.edu/classes/18.785/2021fa/LectureNotes6.pdf),
[strong Hensel, Theorem 9.1](https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf),
[Hilbert symbols and reciprocity, Theorems 16.32–16.33](https://www.math.columbia.edu/~gyujinoh/Spring2024/ANT.pdf),
and [Sanna, Theorem 1.5](https://fq.math.ca/Papers1/54-2/Sanna02242016.pdf).
Lean's [validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
explains why statement meaning remains distinct from proof-term checking.

The manuscript, release assets, formal sources, frozen proof record and
original execution receipts retain their existing identities. No canonical
promotion, journal peer review or new article release follows from this update.
