# Paper I proof record — frozen manuscript correspondence

This record links the [release manuscript](manuscript/candidate/paper_1_release_candidate.md)
to its actual human proofs, finite inputs and formal sources. The frozen
editorial manuscript has Markdown SHA-256
`1570a324a4aa51c44b5981fc6578b335547345076d94e6f12d52332a68b0f694`; the
version 1.0.0 view differs from it only by the metadata update recorded in
[METADATA_UPDATE.md](manuscript/METADATA_UPDATE.md), which lists its SHA-256.
The original baseline and final editorial candidate were ingested separately.
The source correspondence below was inspected against all twelve numbered
results. Source inspection is distinct from the recorded execution results.

The article allows integer square roots; the public Lean exclusion signatures
use `y : Nat`. For an integer root, apply the natural theorem to its natural
absolute value: its square casts to the same integer square. Injectivity of
that cast gives the article's exclusion. This is an exact domain transfer,
not a claim that the signatures are literally identical. In the positive-even
valuation theorem, positivity makes natural subtraction agree with integer
subtraction. No such transfer supplies a formal Hilbert-reciprocity theorem.

The [import map](verification/imports.json) binds the exact source bytes and
their upstream revisions, including all 60 local Lean dependencies and the
unchanged toolchain locks. The principal update is imported from
`758b39bac2abe0fb1a88aae818e6c27bfc9a638f`; its six changed mathematics/replay
files originate at `42d18d38383d5a68c937c8538b680f25a024f107`. A semantic
identifier below denotes a mathematical group, not article numbering or
admission status.

## P1.RECURRENCE.LOCAL_TWO

Article: [Theorem 1.3](manuscript/candidate/paper_1_release_candidate.md#thm-even), [Proposition 2.1](manuscript/candidate/paper_1_release_candidate.md#prop-two-adic).

For natural numbers, set `F₀(A)=1`, `F₁(A)=A` and
`Fₙ₊₂(A)=2 A Fₙ₊₁(A)+Fₙ(A)`. The identification with the normalized Lucas
V-sequence, the phase conventions and exact natural-number domains are in
the [source statement](source-theorem.md) and
[formal crosswalk](theorem-formal-crosswalk.md#1-recurrence-and-domain-lock).

For `A ≡ 2 (mod 4)`, positive even `N` satisfies
`v₂(F_N(A)−1)=2v₂(N)+1`, hence `F_N(A) ≠ y²+1` for every natural `y`.
No 17/41 divisor assumption is used in this even-index result.

Human proof: [propagation proof](../../problems/square-middle/sm2-lower-square/shifted-square-propagation-lamport.md).
Lean: `sm2LucasReal_sub_one_padicVal_two_of_positive_even` and
`no_sm2LucasReal_shiftedSquare_of_positive_even_index` in
[ShiftedSquarePropagation.lean](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean).
Finite [propagation replay](../../experiments/shifted_square_propagation/replay.py)
is regression evidence, including excluded boundary hypotheses; it is not
the unbounded proof. [Proposition 2.1](manuscript/candidate/paper_1_release_candidate.md#prop-two-adic)
is a human Q₂ criterion; the Lean residue arithmetic is not a formal proof
of its full Q₂ equivalence.

## P1.HILBERT.COMMON

Article: [Proposition 3.1](manuscript/candidate/paper_1_release_candidate.md#prop-dyadic), [Theorem 3.2](manuscript/candidate/paper_1_release_candidate.md#thm-criterion), [Proposition 4.1](manuscript/candidate/paper_1_release_candidate.md#prop-bare-theta).

The [common human proof](hilbert-obstruction-lamport.md) states the fixed
field hypotheses, support/valuation argument, real positivity, reference
squareclass and strict Hensel threshold. Its
[finite obligations](fixed-field-obligation-table.md) are separate from
the quantified argument. Odd-place neutrality is a consequence of a
hypothetical global square, not a local-solubility assertion for every
specialized square equation.

The article supplies the [quotient-ring support proof](manuscript/candidate/paper_1_release_candidate.md#valuation-transfer)
and [polynomial maximality proof](manuscript/candidate/paper_1_release_candidate.md#index-certificate).
The latter excludes possible index primes before using Dedekind–Kummer.
[Proposition 3.1 and Theorem 3.2](manuscript/candidate/paper_1_release_candidate.md#criterion)
and [Proposition 4.1](manuscript/candidate/paper_1_release_candidate.md#prop-bare-theta)
are human number-field proofs.
The existing arithmetic Lean proofs do not formalize a general Hilbert
reciprocity theorem or automatically certify those newer paragraphs.

## P1.FIXED17

Article: [Theorem 1.2](manuscript/candidate/paper_1_release_candidate.md#thm-fixed), [Theorem 4.2](manuscript/candidate/paper_1_release_candidate.md#thm-hard), [degree-17 detector](manuscript/candidate/paper_1_release_candidate.md#detector17).

For natural `A,y`, `A ≡ 2 (mod 8)` implies `F₁₇(A) ≠ y²+1`.
The phase extends to `A ≡ 2 (mod 4)` by the elementary other mod-8 case.
Human argument: [fixed-field proof](hilbert-obstruction-lamport.md) and
[source statement](source-theorem.md).
Lean: `no_sm2LucasReal_seventeen_square_of_mod_eight_two` in
[OuterSeventeen](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean)
and `no_sm2LucasReal_seventeen_square_of_mod_four_two` in the propagation module.
Finite inputs and exact checks: [original GP](../../experiments/sm2_outer_seventeen/outer17_verify.gp),
[independent GP](verification/replay/independent_fixed_fields.gp).
Its norm −1 unit is an explicit detecting unit; norm −1 alone is not the
detecting-character condition.

## P1.FIXED41

Article: [Theorem 1.2](manuscript/candidate/paper_1_release_candidate.md#thm-fixed), [Theorem 4.2](manuscript/candidate/paper_1_release_candidate.md#thm-hard), [degree-41 detector](manuscript/candidate/paper_1_release_candidate.md#detector41).

For natural `A,y`, `A ≡ 2 (mod 8)` implies `F₄₁(A) ≠ y²+1`, with the same
elementary strengthening to `A ≡ 2 (mod 4)`.
Lean: `ss41_shiftedSquare_impossible` in
[OuterFortyOne](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean)
and `no_sm2LucasReal_fortyOne_square_of_mod_four_two` in the propagation module.
The general Jacobi branch uses `A=8j+10`; `A=2` is separately excluded
modulo 23. Preserve both paths.

The [original GP verifier](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp),
[independent GP](verification/replay/independent_fixed_fields.gp), three
Jacobi Python/JSON replays and
[independent finite replay](verification/replay/independent_finite.py)
have distinct roles. The detector's constant coefficient is a literal
constant, not a multiple of `D₀=2`. The original GP/independent GP calculate
individual local symbols. The article's [SymPy verifier](manuscript/candidate/paper_1_release_candidate.md#standalone-verifier)
checks polynomial and rational-integer arithmetic; it does not directly
calculate those individual Hilbert symbols.

## P1.PROPAGATION

Article: [Theorem 1.1](manuscript/candidate/paper_1_release_candidate.md#thm-main), [Lemma 5.1](manuscript/candidate/paper_1_release_candidate.md#lem-composition).

Composition is `F_{mn}(A)=F_m(F_n(A))` with **odd inner index `n`**.
For natural `A,N,y`, `A ≡ 2 (mod 4)`, `N>0` and `(17∣N or 41∣N)` imply
`F_N(A) ≠ y²+1`. Oddness is not an assumption of this final theorem.

Lean: `sm2LucasReal_mul_of_odd_right` and
`no_sm2LucasReal_shiftedSquare_of_positive_index_factor` in the
[propagation module](../../Erdos364/DicksonLucas/ShiftedSquarePropagation.lean).
Human proof: [propagation proof](../../problems/square-middle/sm2-lower-square/shifted-square-propagation-lamport.md).
In the odd branch choose `p∈{17,41}` dividing `N`, compose first, then split
the composed parameter modulo 8. Splitting on the original parameter alone
would misclassify examples such as `A=6,N=51`.

## P1.PELL.APPLICATION

Article: [Corollary 1.4](manuscript/candidate/paper_1_release_candidate.md#cor-pell), [Corollary 1.5](manuscript/candidate/paper_1_release_candidate.md#cor-source).

For natural `K,u,v`, assume `u²+1=K v²` and `u ≡ 2 (mod 4)`. The real
coordinate of `(u+v√K)^N` is not `y²+1` for positive even `N`, or for
positive `N` divisible by 17 or 41. These corollaries do not require
fundamentality or squarefreeness. See the exact
[coordinate and domain crosswalk](theorem-formal-crosswalk.md#norm-minus-one-pell-unit-corollaries).
Lean: `normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index`
and `normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor`.

The source-specific applications require their displayed reconstruction
hypotheses. Existing supports include `sm2UpperNegativeUnit_pow_re`,
`Sm2LowerSquareUpperSourceGenerator.root_real_mod_eight`,
`sm2LowerSquareSource_iff_exists_generatorResidual` and `pellRank_dvd_kernel`.
The article's [Corollary 1.5](manuscript/candidate/paper_1_release_candidate.md#cor-source)
has its own [normal-form proof](manuscript/candidate/paper_1_release_candidate.md#source-normal-form)
and [rank proof](manuscript/candidate/paper_1_release_candidate.md#rank).
They establish the least unit in Z[√K], its norm −1, the unique odd exponent,
the same-centre identity and `R=K/gcd(K,v)`. The corollary requires only the
upper neighbour to be powerful; existing formal source adapters use richer
allocation hypotheses. They are not a single Lean proof of this corollary.

## P1.JACOBI.CORRESPONDENCE

Article: [Proposition 7.1](manuscript/candidate/paper_1_release_candidate.md#prop-jacobi).

The [Hilbert/Jacobi crosswalk](hilbert-jacobi-crosswalk.md) distinguishes the
unconditional character calculation from odd-place neutrality under a
square hypothesis. The human identity throughout `A ≡ 2 (mod 8)` is
`J(U_p(2A), F_p(A)−1)=−1`, for `p=17,41` and natural `A`, with positive odd
denominator. The source conventions and finite reference values are in the
fixed-field files above.

The degree-17 `outer17_main_jacobi` and degree-41 `outer41MainJacobi` are
private Lean declarations. The latter uses the oriented numerator
`−U₄₁(2A)` on `A=8j+10`. The public degree-41 nonsquare theorem combines
that proof with the separate `A=2` modulo-23 argument; it is not literally
a single public declaration of the displayed all-parameter Jacobi identity.
Public `ss41_directedTelescope` and `ss41_coefficientJacobi` expose chain
components. Their definitions and the private endpoints require source
inspection in addition to the transitive axiom audit.

## Verification and remaining inputs

The [10 September check report](verification/RESULTS-2026-09-10.md) records
the fresh core replays, axiom audit and independent standalone core build,
with exact source identities and explicit remaining NOT_RUN gates.

The [core replay coordinator](verification/run_core.py) reuses the original
bounded process runner and the existing arithmetic programs. It checks
source-content hashes and the actual local Lean import closure without
requiring a private Git ancestor. It removes inherited private Python/Lean
search paths. Fresh outputs go to a new directory; the historical
[core record](verification/RESULTS-2026-09-10.md) is unchanged and retains its original
meaning. Core replay does not replace the five final article/export gates.

The [Magma source map](verification/magma-imports.json) pins the exact
[17/41 archive](../../experiments/paper1_validation_20260909/magma-17-41-comparison.md).
All four returned PASS responses are archived, with explicit dyadic ideal
matching. Only the original 17-A script has been recovered; the other three
original scripts remain missing. Magma is secondary corroboration of finite
data, not an independent proof of the quantified theorem. No new Magma job
is part of this integration. The complete odd reference ideal support is
checked by GP, not by the four Magma web jobs.

The manuscript, its source ZIP and HTML recipe are now present. The five
operations in [the reproduction guide](verification/export-README.md) run
against exact candidate source bytes. Fresh results belong to their actual
source inventories; the earlier core checks remain historical core checks.

The original Magma inputs 17-B, 41-A and 41-B remain unrecovered. The supplied
outputs and known hashes are archived as secondary finite corroboration, with
this reproducibility limitation. This does not replace or obstruct the
article's self-contained ancillary verification route. No new Magma run is
part of this work.

The expanded explanatory supplement and Brauer appendix remain separate;
this core integration does not claim completion of that publication
programme. No 73/97 controls, searches or canonical/Ledger changes are included.
Actual public release is separately gated by the author’s metadata decisions
and the final tested companion tree and history.
