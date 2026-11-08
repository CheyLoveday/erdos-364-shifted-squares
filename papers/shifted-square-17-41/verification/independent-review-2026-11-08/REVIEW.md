# Ultra Review of the shifted-square paper

**Review date:** 8 November 2026
**Mathematical baseline reviewed:** `c663b4e1e65c99846d41270a288f154559cc9fd6`
**Branch base for this package:** `fd35ce953306db0361a376e2b1993f5f2e0eb32f` (including merged reproduction PR #8)
**Investigation record:** Ultramath swarm `smw70l62n`
**Nature of review:** independent agent-assisted mathematical audit, exact computation and referee checking of submitted claims

## 1. Executive verdict

The investigation found **no mathematical error, counterexample or load-bearing statement mismatch in the paper**. Confidence increased materially in both the formal recurrence results and the human Hilbert/Pell arguments.

Six packages passed referee acceptance, several after explicit corrections. Corollary 1.5 was independently re-proved as well, although its submitted sieve was rejected twice, first for defects in the numerical proof and then in the Hensel-lift implementation. Correcting that implementation and rerunning the full computation confirmed its stated `X ≤ 10^14` conclusion.

This is not external human peer review. It is not a complete Lean formalisation of the human Hilbert or Corollary 1.5 arguments, and it does not extend the paper's conclusions to new exponent families or to the full three-consecutive-powerful-number problem.

### Main distinctions

| Evidence class | What was established |
|---|---|
| Kernel-checked formal proof | Paper-strength bridge for Theorems 1.1, 1.2, 1.3, hard-phase 4.2 and Corollary 1.4 |
| Independent finite certificates | All load-bearing finite field data reconstructed by separate exact code |
| Direct local computation | All three dyadic Hilbert signs in each fixed field, plus the arbitrary-valuation odd-prime bridge |
| Human mathematical proof with checked inputs | The Hilbert chain and a new two-phase Jacobi identity; Corollary 1.5 |
| Published external literature | Sanna's valuation theorem and Walker's property-Q/Pell classification |
| Impossibility/scope theorem | No fixed-modulus covering-congruence certificate for the hard phase |
| Exact numerical experiment | More than two million statement assertions and the completed `X ≤ 10^14` sieve |

The numerical assertions are not substitutes for the quantified proofs. The documentation below keeps them separate.

## 2. Review process and accepted directions

Eight initial directions were investigated. Six submissions were accepted after referee review; one direction ended without a solution, and the Corollary 1.5 numerical submission was rejected before its computation was independently corrected and rerun.

| Direction | Accepted result | Full report |
|---|---|---|
| Formal statement fidelity (`d4`, member m5) | Paper-strength Lean bridge and 2,078,952 exact assertions | [formal-statement.md](reports/formal-statement.md) |
| Finite-certificate provenance (`d7`, m4) | Independent 51-check exact reconstruction | [finite-certificates.md](reports/finite-certificates.md) |
| Direct dyadic/certificate audit (`d2`, m3) | Direct local signs and odd-prime bridge instances | [direct-dyadic.md](reports/direct-dyadic.md) |
| Hilbert chain (`d3`, m6) | Full sign/stability audit and two-phase Jacobi lemma | [hilbert-chain.md](reports/hilbert-chain.md) |
| Alternative elementary routes (`d5`, m7) | Correctly bounded no-fixed-modulus theorem | [elementary-routes.md](reports/elementary-routes.md) |
| Literature/priority (`d6`, m1) | Checked locators, Sanna/Walker specialisation and bounded novelty review | [literature.md](reports/literature.md) |
| Corollary 1.5 (`d1`, m8), independently completed outside acceptance | Normal form, non-maximal-order Pell analysis, rank and sharpness verified; sieve corrected by the referee | [corollary-1-5.md](reports/corollary-1-5.md) |
| Trust-base inventory (`d8`, m2) | No submission before budget ended; m5's axiom/build work supplies the principal named-declaration coverage, not a second complete audit | see `logs/axiom_footprint.txt` |

The review did not accept unsupported claims of independence. In particular, the Hilbert and maintained Jacobi proofs share the same polynomial and detector data. Computing the same certified conclusion by another route is useful verification, not independent discovery of a new certificate.

## 3. Formal statement fidelity

The maintained development already contained the central recurrence and integer-Jacobi results. The remaining semantic issue was whether their statements literally imply the paper's claims, especially because the paper allows `y ∈ ℤ` while the maintained theorems use `y : ℕ`.

[`scripts/formal/PaperStatementBridge.lean`](scripts/formal/PaperStatementBridge.lean) proves the required conversions inside Lean and derives, without additional hypotheses:

- Theorem 1.1 for every natural `A,N` with `A % 4 = 2`, `N > 0` and `17 ∣ N ∨ 41 ∣ N`, for every integer `y`;
- both fixed-index exclusions of Theorem 1.2 at `A % 4 = 2`;
- both hard-phase exclusions of Theorem 4.2 at `A % 8 = 2`, including `A = 2`;
- the exact positive-even-index valuation of Theorem 1.3 and its integer-square consequence;
- Corollary 1.4 using
  `((⟨u,v⟩ : ℤ√(K:ℤ))^N).re`,
  the real coordinate of a genuine `Zsqrtd` power, with no squarefreeness, coprimality or fundamental-unit hypothesis.

The integer/natural transfer is proved using `Int.natAbs`; it is not a fresh mathematical assumption. The degree-41 endpoint is genuinely inside the formal statement, and the separate residue witness `F_41(2)-1 ≡ 20 (mod 23)` and nonresidue of 20 were checked in Lean.

### Axioms

The accepted bridge and all 19 crosswalk-attributed declarations inspected by m5 use only:

```text
propext, Classical.choice, Quot.sound
```

No `sorryAx` or project-specific axiom appears in those checks. This is a named-declaration footprint, not a claim that every declaration in the whole repository was separately inspected.

### Toolchain boundary

The out-of-tree audited build elaborated the 60-module propagation closure under Lean **4.35.0** and Mathlib `a3a10db`. Two visible adaptations were required:

1. an explicit equivalent `Fintype` instance in `LeafCompiler.lean`;
2. `set_option maxRecDepth 20000` for a large primality term in `Sm2LowerSquareOuterFortyOne.lean`.

These are preserved as small diffs in `provenance/`, not as changed public mathematical declarations. The public Lean 4.31 reproduction is a separate evidence package; this audit does not reinterpret it as a 4.35 unchanged-source run.

The independent arithmetic script `audit_statements.py` reran successfully with **2,078,952 assertions and 0 failures**, including 62,500 hard-phase `A` values per prime for Proposition 7.1 and 35 Pell triples, six with non-squarefree `K`.

## 4. Independent finite-certificate reconstruction

The 51-check script [`verify_independent.py`](scripts/finite-certificates/verify_independent.py), with its separate arithmetic kit, was rerun successfully and printed `FIXED_CERTIFICATE_INDEPENDENT_OK`.

It reconstructs, using exact integer/polynomial and modular methods rather than the project's GP verifier:

- `disc(g_17) = 2^24 17^17` and `disc(g_41) = 2^60 41^41`;
- irreducibility and index one at both `2` and `p`, hence `𝒪_L = ℤ[θ]`;
- the dyadic factorisations with residual degrees `1,4,4` and `1,10,10`;
- total ramification at `p`;
- `Res(g_p,U_p) = -1`, `N(θ)=2`, `N(u_p)=-1` and `N(b_p)=-2`;
- the reference factorisations, primality and all seven Table A1 Legendre signs;
- signatures, composition and residue checks;
- a direct `Q_2` computation at the degree-one dyadic prime;
- ramified-phase and large exact Jacobi stress tests.

The mathematical derivation is also checked in [theorem-1-2-rederivation.md](reports/theorem-1-2-rederivation.md). It correctly proves numerator/denominator coprimality from odd-place unitness, handles ramified supporting primes, and restricts the `A ≡ 6 (mod 8)` residue exclusion to `n ≡ 1 (mod 4)`.

## 5. Direct dyadic signs and the odd-prime bridge

The paper needs only the product of the reference dyadic signs and obtains it indirectly via reference characters plus Hilbert reciprocity. Two investigations recomputed the individual signs directly using PARI `nfhilbert`:

| Field | Direct local signs (PARI ordering) | Product |
|---|---|---:|
| Degree 17 | `+1,+1,-1` | `-1` |
| Degree 41 | `+1,-1,+1` | `-1` |

The degree-17 ordering differs from the manuscript's displayed order only in the two equal-type primes; the paper explicitly defines a multiset, so there is no discrepancy. The degree-one completion was independently checked by direct `Q_2` arithmetic, and the untwisted `b=θ` product was confirmed to be `+1`, as Proposition 4.1 requires.

The flagship degree-17 GP script initially had a real syntax error. It was repaired, rerun, and accepted only after both direct scripts and the clean output inventory succeeded.

### Arbitrary odd-prime valuations

The final Hilbert audit expanded the bridge beyond the reference point and beyond even valuations. `audit_bridge.gp` verifies six non-reference points and 28 supporting-prime characters, including:

- a denominator valuation of three;
- ramified support;
- positive and negative odd-place products;
- both residue phases.

At each supporting prime it checks uniqueness, residue degree one,

`v_𝔓(δ_x) = v_ℓ(Q)`, and equality between the local Hilbert symbol and the corresponding Legendre-power factor. All checks passed. This is important because the hypothetical-square neutrality uses even valuations, but Proposition 7.1 uses **arbitrary** valuations and genuinely depends on the local residue character.

## 6. Two-phase Jacobi identity

A new human proof strengthens Proposition 7.1:

```text
For p ∈ {17,41} and every A ≥ 2 with A ≡ 2 (mod 4),
J(U_p(2A), F_p(A)-1) = -1.
```

The original proposition states the `A ≡ 2 (mod 8)` phase. The second phase uses a new reference `x_0 = 12`:

- direct dyadic reference product at `x=12`: `+1`;
- strict Hensel remains valid for every `x ≡ 12 (mod 16)` because `x-12` is divisible by 16;
- `m=x/4 ≡ 3 (mod 4)` and `Q ≡ 5 (mod 8)` give `J(x,Q)=-1`;
- the changed dyadic sign and Jacobi factor cancel, leaving `J(U_p(x),Q)=-1`.

The identity is proven, not merely inferred from finite examples. It adds no new non-square conclusion because that phase was already impossible modulo 8. It also shows why the earlier Hilbert transfer cannot simply compare `x=12` with `x=4`: the strict inequality reaches equality at the degree-one prime and the reference symbol really changes. This is accepted as a human proof with exact finite computations, not as a Lean declaration.

## 7. Corollary 1.5 and the Pell rank

The complete Corollary 1.5 argument was independently reconstructed:

- `X-1` square and `X²+1` powerful imply `X ≡ 2 (mod 8)`;
- the unique squarefree-cube decomposition `X²+1=K³V²` gives `K ≡ 5 (mod 8)`;
- `η=X+KV√K` is a norm-minus-one unit in the **non-maximal order** `ℤ[√K]`;
- the least unit `ε>1` in that order generates all positive units and itself has norm `-1`;
- hence `η=ε^N` for a unique positive odd `N`;
- the generator has `v` odd and `u ≡ 2 (mod 4)`, and its powers give exactly `X=F_N(u)`;
- Theorem 1.2 and odd-inner composition then force `gcd(N,17·41)=1`.

### Rank, checked three ways

For `ε^n=a_n+b_n√K`, the rank statement is

```text
K | b_n  ⟺  R := K/gcd(K,v) divides n.
```

It was proved independently by:

1. the binomial congruence `b_n ≡ n u^{n-1}v (mod K)`;
2. the nilpotent ring `ℤ[s]/(s²,K)`, where `s²=0` isolates the same linear term;
3. Walker's Theorems 2.2(3) and 2.5, whose minus-sign property-Q solutions are odd powers of the least property-Q unit.

Squarefreeness is **not** needed for the binomial equivalence itself: with `g=gcd(K,v)`, the cancellation uses coprimality of `K₀=K/g` and `v₀=v/g`. Squarefreeness remains necessary for the unique `K³V²` normal form and for writing Walker's product as `K/gcd(K,v)`.

Computations checked 411 negative-Pell instances, including eight non-squarefree examples, and independently reproduced 456 soluble odd squarefree cases through `K ≤ 5000`, 21 with `R<K`, with no rank mismatch.

### Norm-one comparison and sharpness

Equation (6.7) really needs odd `K`. Even counterexamples include `K=2`, where the two ranks are `2` and `1`. This matters semantically because Lean's `pellRank` uses the norm-one fundamental solution: equality with the paper's `R` is a derived fact under the paper's hypotheses, not a definition.

The lower-square condition is also essential. Exact examples at `K=5`, `N=85` and `N=205` give powerful `X²+1` with `X ≡ 2 (mod 8)` and respectively `17 ∣ N` and `41 ∣ N`, while `X-1` is not square. Thus the exclusion cannot be extended merely to the larger powerful-plus-phase family. The same-centre identity is what rules those cases out.

### Corrected exhaustive numerical result

The original numerical submission first used an incomplete classification of powerful survivors. Its replacement established the right smooth/cofactor criterion but retained a factor-of-two Hensel-lift bug:

```text
N(y) = y^4 + 2y^2 + 2
N'(y) = 4y(y^2+1), not 2y(y^2+1).
```

All 158 root-class lifts through `q ≤ 1000` failed with the submitted version and passed with the one-line correction. With the corrected code:

- `selftest_E` agrees with brute-force factorisation;
- `selftest_powerful` agrees on 2,000 random integers;
- the full search over every odd `y ≤ 10^7` has **748,369 survivors and zero candidates**.

Therefore no member of the Corollary 1.5 hypothesis class exists with `X ≤ 10^14`. The corrected implementations and complete outputs are preserved in `scripts/cor15/` and `logs/`. Independently, all 14 wider-family members with `X ≤ 10^60` and odd squarefree `K ≤ 20000` fail the lower-square condition.

This establishes the numerical bounds, not non-emptiness or emptiness of the full hypothesis class.

## 8. Alternative congruence routes: a real impossibility theorem

The elementary-route investigation proved:

> For either `p ∈ {17,41}`, every finite set `S` of odd primes and every choice of prime exponents, there are infinitely many `A ≡ 2 (mod 8)` for which `F_p(A)-1` is a square modulo all those prime powers and at every power of two.

Consequently no fixed-modulus covering-congruence certificate for the hard phase exists.

The argument is complete: the hard phase supplies a square in `Q_2`; a quadratic-character Weil bound supplies a nonzero square residue for every sufficiently large odd prime; a finite exact check covers all 668 odd primes up to 5000; odd-prime Hensel lifting and CRT assemble arbitrary prime powers.

The conclusion is deliberately narrow. It does **not** rule out:

- the paper's Jacobi proof, whose numerator and denominator depend on `A`;
- global height or integral-point methods;
- every Pell, resultant or cyclotomic construction;
- an as-yet-unknown lower-complexity detector.

Those remain route diagnoses, not impossibility theorems. The submission also produced exact cyclotomic/resultant and `w_p ≡ p (mod A²+1)` identities, preserved in [route-scope.md](reports/route-scope.md).

## 9. Literature and priority

The revised literature audit found every numbered/paged locator used by the paper to support its intended statement. The inaccessible Dickson monograph is explicitly marked unchecked; the needed composition identity was independently verified and is also proved directly in the paper, so nothing load-bearing depends on that unavailable text.

Two classical specialisations checked out:

- **Sanna, Theorem 1.5:** gives the exact even-index valuation with `a=2A`, `b=1` and `Δ=4(A²+1)`;
- **Walker, §2:** supplies the property-Q rank and odd-exponent classification in the same order `ℤ[√K]`, including the published example `(2+√5)^5=682+305√5`.

Walker supports the rank/oddness half of Corollary 1.5, not its whole normal form, same-centre identity or `17/41` consequence, and not its formalisation.

In the searches documented in [literature.md](reports/literature.md), no earlier theorem was found that implies Theorems 1.1, 1.2, 4.2 or Proposition 7.1. That is a bounded search result, **not an absolute novelty proof**. Finkelstein/Ribenboim and related fixed-sequence shifted-square work are worth adding to a future related-work discussion; their hypotheses do not cover this fixed-index/varying-parameter family.

## 10. Review errata and rejected claims

The review process itself found errors in investigator submissions. None was propagated into the accepted conclusions without correction or independent repair.

1. A first literature draft wrongly evaluated `D_p(2)=2` and inferred a rational curve point. The corrected report uses `D_p(2)=2F_p(1)` and makes no unsupported rational-point assertion.
2. A first certificate proof wrongly generalised the modulo-8 phase to every odd index and wrote an incorrect gcd conclusion for a square denominator. Both were corrected before acceptance.
3. The first direct degree-17 GP script failed to parse. It was repaired and rerun before acceptance.
4. The elementary-route draft overgeneralised its negative result and misclassified `A²+1 ∣ p`. Its accepted theorem is restricted to fixed-modulus tests.
5. The Hilbert report was corrected to distinguish inert even-valuation neutrality from the genuinely character-dependent arbitrary-valuation bridge.
6. The Corollary 1.5 sieve was rejected once for incomplete powerful-shape classification and again for a genuine Hensel-derivative bug. The corrected one-line implementation was rerun by the referee and is the version included here.
7. A side claim about coprimality with an unnormalised denominator was false (`D=12,Y=18`). The accepted proof uses the normalised `K₀=K/g` and `v₀=v/g`.
8. The dedicated trust-base direction produced no final submission. Its role is only partly replaced by m5's named-declaration build and axiom checks; it is not counted as an accepted second trust-base audit.

## 11. Repository correction in this PR

The degree-41 GP header formerly described `u_41 = Σ a_nD_n` including `n=0`. Its code actually computes `c_0·1 + Σ_{n≥1} c_nD_n`, as the paper explicitly requires. Because `D_0=2`, following the old comment literally produces a non-unit.

The comment now says that `c_0` multiplies `1`, not `D_0`. The executable statement is unchanged. The supplied degree-41 GP certificate still passes after the edit; see the test inventory below. The affected input-manifest and root checksum entries are reconciled to the new comment bytes.

No other publication source, detector coefficient, recurrence, theorem or proof was edited for this PR.

## 12. Verification inventory

Checks run by the referee during the audit are recorded in the preserved reports and logs. No check is listed here merely because another report asserted it without a reproducible artifact.

| Check | Result |
|---|---|
| Paper-strength Lean bridge recompilation | `exit=0`; only the three approved axioms in principal declarations |
| 60-module Lean 4.35 out-of-tree closure | Successful with the two disclosed syntactic adaptations |
| Independent fixed certificates | 51 checks; `FIXED_CERTIFICATE_INDEPENDENT_OK` |
| Exact statement arithmetic | 2,078,952 assertions, 0 failures; `STATEMENT_AUDIT_OK` |
| Direct degree-17 and degree-41 dyadic signs | Both products `-1`; clean scripts and outputs |
| `Q_2` convention validation and degree-one signs | Passed |
| Six non-reference odd-prime bridge points | All 28 local character checks passed |
| Corrected Corollary 1.5 sieve self-tests | `selftest_E` agreement; 2,000 random criterion checks with no mismatch |
| Corrected full Corollary 1.5 sieve | 748,369 survivors, zero candidates |
| Walker exhaustive numerical range | 456 soluble odd squarefree `K ≤ 5000`; 21 `R<K`; no mismatch |
| Route-scope scripts | `ROUTE_SCOPE_OK`, `ROUTE_SCOPE_CHECKS_OK`, `JACOBI_EXTENDED_OK` |
| Degree-41 executable GP certificate after comment edit | `OUTER41_CERTIFICATE_OK` |
| Root checksum inventory, excluding three documented stale baseline entries | Every listed source passed; see `logs/checksums-filtered.txt` |

Captured output is under `logs/` and beside the relevant Hilbert/dyadic scripts. The GP certificate and finite-certificate reruns are also executable from `README.md`.

The unfiltered root checksum command still reports the three already-documented stale metadata entries in `README.md`, `manuscript/revision/README.md`, and `theorem-formal-crosswalk.md`. Those unrelated historical bytes were not altered in this PR. This is explicitly recorded in `logs/VALIDATION.md`; it is not presented as a full unfiltered checksum pass.

## 13. Remaining limitations and sensible next steps

- The human Hilbert proof remains human mathematics, not a Lean formalisation.
- Corollary 1.5 remains an exact human proof with literature/computation support, not a single formal corollary declaration.
- The two-phase Jacobi identity and paper-strength bridge are audit additions, not imported maintained declarations.
- No alternative proof with genuinely independent detector provenance was found.
- Large numerical sweeps are falsification evidence only.
- The public Lean 4.31 replay, this 4.35 compatibility build, and the historical six-checker selection must remain distinct evidence packages.
- External independent human peer review is still a different assurance level.

Reasonable future work is to review and, if desired, integrate the paper-strength bridge into the maintained Lean surface; to formalise the two-phase Jacobi identity; or to seek external review of the human Hilbert and Pell arguments. None of those is silently claimed by this PR.
