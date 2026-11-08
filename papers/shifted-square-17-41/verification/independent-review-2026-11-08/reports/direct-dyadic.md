# Independent audit: Hilbert-route certificate data at p = 17, 41

Member m3, swarm smw70l62n (direction d2: Hilbert-free / specialization-safe transfer).
Commit audited: `c663b4e1e65c99846d41270a288f154559cc9fd6`.
Sources read: `papers/shifted-square-17-41/manuscript/revision/paper_1_github.md`
(sections 2–5, 7, Appendix A), `hilbert-jacobi-crosswalk.md`,
`reading/theorem-formal-crosswalk.md`, and `Erdos364/SquareMiddle/*.lean`.

**Verdict.** No mathematical error was found in the audited chain. Every finite
hypothesis of Theorem 3.2 at p = 17 and p = 41 is reconfirmed here by
computations that are independent of the project's own verifier
(`outer17_verify.gp`, `outer41_verify.gp`). In particular hypothesis 5 — the
dyadic product (4.12) — which the article derives only indirectly (through
reciprocity plus the reference character), is confirmed here by a **direct
local Hilbert-symbol computation**. Two scope/route findings are reported that
the article does not state: (i) the phase restriction `A ≡ 2 (mod 8)` of
Proposition 7.1 is exactly the phase reachable by the article's two inputs, and
both inputs genuinely fail at `A ≡ 6 (mod 8)` (a dyadic sign flips), although
the Jacobi identity itself continues to hold there numerically; (ii) the naive
"pseudo-remainder Jacobi chain with square/2-power multipliers" does **not**
give a specialization-safe transfer, because the chain's consecutive resultants
carry odd prime factors and those common factors really occur inside the hard
phase. Hence the elaboration of the Lean chain is not avoidable by the obvious
shortcut.

Status categories used below: **[P]** proof checked line by line by hand;
**[C]** exact computation (reproducible script); **[N]** numerical experiment
(finite range, not a proof); **[H]** standard theorem invoked but not reproved.

---

## 1. What was verified, and how

### 1.1 Theorem 3.2, hypotheses 1–5, at p = 17 and p = 41

Theorem 3.2 (monogenic fixed-field criterion) has five hypotheses. All five are
verified, so the theorem's conclusion — no integers `x ≥ 4`, `x ≡ 4 (mod 16)`,
`Y` with `g_p(x) = 2Y²` — follows from the human proof §§3.3–3.5 plus Hilbert
reciprocity. The human proof itself was checked line by line [P]; reciprocity
(3.1) is a standard theorem [H].

| Hypothesis | Claim | Status |
|---|---|---|
| 1a | `O_{L_p} = Z[θ_p]` (index 1) | [C] two independent ways |
| 1b | `N(θ_p) = 2` | [P] monic odd degree, `g_p(0) = −2` |
| 2 | one real embedding, `0 < θ_R < 4` | [C]+[P] unique real root `= 2 sinh(arsinh(1)/p)` |
| 3 | `(b_p) = (θ_p)`, i.e. `u_p = U_p(θ_p)` a unit | [C] `Res(g_p,U_p) = −1` |
| 4 | `4e_P − d_P > 2e_P` at every dyadic `P` | [C] rows `3 > 2`, `8 > 4` |
| 5 | `∏_{P|2} (δ_4, b_p)_P = −1` | [C] direct `nfhilbert`, both fields |

Computed values (script `work/certificate_check.py`):

* `disc(g_17) = 2^24·17^17`, `disc(g_41) = 2^60·41^41`; both `g_p` irreducible
  over Q; disc has no prime divisor other than 2 and p.
* Dedekind index criterion at ℓ = 2 and ℓ = p gives index not divisible by ℓ in
  both fields, so `[O_L : Z[θ]] = 1`. The routine was validated against the
  classical examples `Z[√5]` (index 2 at 2 detected), `Z[√−3]` (index 2 at 2
  detected) and `Z[√2]` (index 1).
* PARI's `nfinit` independently reports `nf.disc = 2^24·17^17` and
  `2^60·41^41`, i.e. the order is already maximal.
* `Res(g_17,U_17) = Res(g_41,U_41) = −1`; hence `N(u_p) = −1` and `u_p` is a
  unit, `(θ_p U_p(θ_p)) = (θ_p)`.
* `g_17(4) = 45537549122`, `g_41(4) = 50755107359004694554823202`;
  `H_17 = 13·1751444197`, `H_41 = 79·1373·115471·1506563·1344905911`;
  `U_17(4) = 532303029`, `U_41(4) = −43956715453803235217163523`;
  `J(U_17(4),H_17) = J(U_41(4),H_41) = −1`.
* Table A1 is reproduced exactly: `(4U_p(4)/ℓ) = (−1, +1)` at `ℓ = 13,
  1751444197` and `(+1, −1, −1, −1, +1)` at `ℓ = 79, 1373, 115471, 1506563,
  1344905911`; odd product `−1` in both fields.
* (A.3) `g_p ≡ T·φ_p²·ψ_p² (mod 2)` with the printed `φ_p, ψ_p`, both
  irreducible and distinct mod 2; the correction `H_{p,2}` reduces to `1` mod
  `φ_pψ_p`; (A.5) residues `12` and `26`.

### 1.2 Direct verification of the dyadic certificate (Table 4, equation (4.12))

This is the one hypothesis of Theorem 3.2 that is analytic rather than
polynomial, and the article itself notes that the *individual* dyadic signs are
"additional data … not deductions from the valuation columns"; Appendix A
obtains only their product, and only by applying reciprocity to the reference
character. I computed the three local symbols directly in the completed local
fields with PARI `nfhilbert`, independently of that derivation. The primary
direct runs are **`work/dyadic17.gp`** (p = 17) and **`work/dyadic41.gp`**
(p = 41); each prints `(e,f)`, `(t,d,s)`, `4e−d` against `2e`, and the
individual sign at every dyadic prime:

| p | `(e,f)` | `(t,d,s) = (v_P(θ), v_P(4−θ), v_P(b))` | `(δ_4,b_p)_P` | `4e−d > 2e` |
|---|---|---|---|---|
| 17 | (1,1) | (1,1,1) | **+1** | 3 > 2 |
| 17 | (2,4) | (0,0,0) | **+1** | 8 > 4 |
| 17 | (2,4) | (0,0,0) | **−1** | 8 > 4 |
| 41 | (1,1) | (1,1,1) | **+1** | 3 > 2 |
| 41 | (2,10) | (0,0,0) | **−1** | 8 > 4 |
| 41 | (2,10) | (0,0,0) | **+1** | 8 > 4 |

Both runs print product `−1`, i.e. (4.12) holds, and `Σef = p`. As a multiset
this is exactly Table 4's `{+1, −1, +1}`; PARI's ordering of the two equal-type
primes is arbitrary, so for p = 17 the last two rows appear interchanged with
respect to the printed table (for p = 41 the order even coincides). In the
p = 17 run the same script also prints the *bare-`θ`* reference product
`∏_P (δ_4,θ)_P = +1`, which is Proposition 4.1's (4.2) — the unit twist is
therefore doing real work. The direct computation agrees with the article's
indirect derivation (Appendix A.1 reference character `−1` plus reciprocity),
which is a nontrivial consistency check on both routes. Scripts:
`work/dyadic17.gp`, `work/dyadic41.gp`; recorded output in
`work/OUTPUTS.txt`.

A **separate** script, `work/dyadic_general.gp`, is used in §2.1 to compare the
dyadic symbols at specific values `A = 2, 10, 6, 14, 22`. It happens to include
the reference `A = 2` and reproduces the same signs (`+1, +1, −1`, product `−1`)
there; that agreement is a cross-check, not the primary direct evidence, which
is the dedicated p = 17 and p = 41 runs above.

Convention check (`work/nfhilbert_validation.gp`): the degree-one dyadic prime
has `L_P = Q_2`, so for rational inputs `nfhilbert` must agree with the
`hilbert(·,·,2)` function. It does on the test set
`(5,2),(3,−1),(−1,−1),(2,2),(5,10),(3,5),(−2,3)`, with the expected answers
`−1,−1,−1,1,−1,1,1`.

### 1.3 The bridge (7.3)–(7.4), including ramified primes and higher valuations

The identity `∏_{P finite, P∤2} (δ_x,b_p)_P = J(xU_p(x), Q)` with `x = 2A`,
`Q = g_p(x)/2`, and the reduction to `J(U_p(x),Q)` under `A ≡ 2 (mod 8)` was
checked line by line [P] and then verified numerically at concrete
specialisations with `nfhilbert` [C] (`work/bridge17.gp`, `work/bridge_ramified.gp`,
`work/bridge_higher.gp`):

* A = 2, 10: odd product `−1 = J(xU_p(x),Q)`;
* A = 14 (`≡ 6 mod 8`): odd product `+1 = J(xU_p(x),Q)` — a check where the
  product is not `−1`, so the identity is not being confirmed vacuously;
* A = 18: includes the **ramified** prime `ℓ = p = 17`; the supporting prime has
  `e = 17`, `f = 1`, `v_P(x−θ) = 1`, and the local symbol `+1` equals the
  Legendre symbol — the article's claim that "the argument also applies at
  ramified primes" is correct;
* A = 22 (`v_3(Q) = 3`) and A = 58 (`v_3(Q) = 2`, `A ≡ 2 mod 8`): local symbols
  agree with the Legendre symbols raised to the exact valuations, so the
  exponent bookkeeping of (3.7) is right.

All supporting primes found in these runs have residue degree one (`f = 1`), as
(3.5) predicts.

### 1.4 Proposition 7.1 in its stated phase [N]

`J(U_p(2A), F_p(A)−1) = −1` and `gcd(U_p(2A), F_p(A)−1) = 1` were checked for

* p = 17: all `A = 8k+2`, `0 ≤ k < 5000`;
* p = 41: all `A = 8k+2`, `0 ≤ k < 500`;

5500 exact integer checks, zero exceptions, zero non-coprime pairs
(`work/stress_final.py`). This is a finite-range check only; it is not offered as
a proof. It also covers the endpoint `A = 2`.

---

## 2. Findings beyond restatement

### 2.1 The phase `A ≡ 2 (mod 8)` is exactly the phase the proof reaches, and both inputs fail at `A ≡ 6 (mod 8)`

Two steps of the article use `A ≡ 2 (mod 8)`, i.e. `x ≡ 4 (mod 16)` and
`m = x/4 ≡ 1 (mod 4)`:

1. (3.9) needs `v_P(x−4) ≥ 4e` to get `4e−d > 2e`. At `x ≡ 4 (mod 16)` this
   holds. At `x ≡ 12 (mod 16)` (`A ≡ 6 mod 8`) one only has `v_P(x−4) ≥ 3e`, and
   at the degree-one dyadic prime `e = d = 1` this gives `3e−d = 2 = 2e`, so
   strong Hensel does not apply.
2. `J(m,Q) = J(Q,m) = J(−1,m) = 1` needs `m ≡ 1 (mod 4)`; at `A ≡ 6 (mod 8)`,
   `m ≡ 3 (mod 4)` and instead `J(m,Q) = −1`.

Both failures are structural: they follow from the stated exponents (`3e−d = 2e`
instead of `> 2e` at the degree-one prime) and from `m ≡ 3 (mod 4)`, so the
article's Hilbert argument cannot be re-run verbatim at `A ≡ 6 (mod 8)`. The
sign flip is also **observed numerically** [N]: direct `nfhilbert` computation
(`work/dyadic_general.gp`) at `A = 6, 14, 22` gives, at the three dyadic primes,
`(−1, +1, −1)` where `A = 2, 10` give `(+1, +1, −1)`; so the dyadic product
becomes `+1` at `A ≡ 6 (mod 8)` (it is `−1` at every tested `A ≡ 2 mod 8`). The
bridge computation at `A = 14` gives odd product `+1` together with
`J(x,Q) = −1`, consistent with the sign flip.

Nevertheless, the conclusion of Proposition 7.1 continues to hold there: 5500
additional exact checks at `A = 8k+6` (5000 for p = 17, 500 for p = 41) give
`J(U_p(2A),F_p(A)−1) = −1` with trivial gcd. The reason is that the two sign
changes cancel in the final integer character: odd product `+1` and
`J(x,Q) = −1` give `J(U_p(x),Q) = +1·(−1) = −1`. So:

* Proposition 7.1 as stated (`A ≡ 2 mod 8`) is true and its hypothesis is sharp
  for the proof given;
* the identity also holds numerically on the wider phase `A ≡ 2 (mod 4)` (the
  exact phase where `F_p(A)−1` is odd), but **this is a numerical observation
  only: no uniform Hensel or dyadic-stability argument is supplied for the wider
  phase, and the observation is not used in any proof.** It would add no theorem
  anyway, since `A ≡ 6 (mod 8)` is already excluded by `F_p(A)−1 ≡ 5 (mod 8)`.

This is a scope observation, not a gap.

### 2.2 Negative route-scope result: the naive specialization-safe Jacobi chain does not exist

The Lean development proves the hard phase by a pseudo-remainder/Jacobi chain,
not by the Hilbert route (crosswalk: "exact polynomial pseudo-remainder
identities and Jacobi-symbol transfer"). Its 14 explicit polynomials
`R_0,…,R_14` satisfy, identically in `A` [C, `work/chain17.py`],

```
R0 = (4A^3+5A)R1 + R2,   3R1 = 2A R2 − R3,   R2 = 4A R3 + R4, ...
... 25R13 = (740A+267)R14 + 5476,
```

with `R_0 = F_17(A) − 1` and `R_1 = U_17(2A)` (verified symbolically). The
tempting reading — "each multiplier is a square or a power of 2, so every
transfer contributes a sign determined by `A mod 16`, and the whole chain is a
one-line uniform proof" — is **false**:

* the consecutive resultants are not 2-powers:
  `Res(R2,R3) = −2^142·3^11`, `Res(R3,R4) = −2^120·3^9`,
  `Res(R5,R6) = 2^90·3^9·11^18`, `Res(R7,R8) = 2^49·5^14·13^14`,
  `Res(R8,R9) = 2^40·7^12`, `Res(R11,R12) = −2^12·5^6`,
  `Res(R12,R13) = 2^6·31^4`, `Res(R13,R14) = 2^4·37^2`;
* the common factors really occur inside the hard phase: at `A = 10`
  (and `A = 34`, i.e. `A ≡ 1 mod 3`) one has `3 | R_2(A)` and `3 | R_3(A)`, so
  `gcd(R_2(A),R_3(A)) = 3` and the Jacobi symbol of that pair is `0`, not `±1`.
  The transfer `J(R_1,R_2) → J(R_2,R_3)` then reads `J(3,R_2)·J(R_1,R_2) =
  J(R_3,R_2) = 0`, which is consistent but carries no value; the chain cannot
  pass through this pair for those `A`.

Hence any specialization-safe transfer of this shape needs an explicit
common-factor analysis prime by prime — which is what the Lean's
bottom/middle/top decomposition with the value-level Bézout identities
(`S·P10 = U·P11 + 8`, `125·P11 = E2·H + 2M`, `103²·H = E3·M + 125²`) does, and
why the formal file is 2065 lines for degree 17 and 13982 lines for degree 41.
I verified the polynomial identities and the endpoint identifications of that
chain, but **not** its transfer bookkeeping; that verification belongs to the
formal-trust-base line of the audit, not here. The Lean file's own final step
(`outer17_main_jacobi` followed by `jacobiSym.pow_right` and
`jacobiSym.trichotomy` in `no_sm2LucasReal_seventeen_square_of_mod_eight_two`)
is the same "a square denominator has Jacobi symbol 0 or 1" incompatibility that
Proposition 7.1 uses, so the two routes agree at the final transfer.

---

## 3. What is *not* verified here

* Hilbert reciprocity (3.1) itself: invoked as a standard theorem, not reproved.
* The strong form of Hensel used in (3.9): standard, checked only for its stated
  hypotheses and strictness threshold.
* The Lean transfer bookkeeping for `Sm2LowerSquareOuterSeventeen` /
  `OuterFortyOne` (only the polynomial identities and endpoint values were
  checked here).
* A Hilbert-free *proof* of Proposition 7.1 uniformly in `A`: not obtained. The
  only Hilbert-free argument visible to me is the formal Jacobi chain, and §2.2
  shows the naive reconstruction of it fails. The identity
  `∏_{P∤2}(δ_x,b_p)_P = J(U_p(x),Q)` values a quadratic Hecke character on
  principal ideals, so a uniform proof must contain a reciprocity law — either
  Hilbert reciprocity in `L_p` (article), or an explicit quadratic-reciprocity
  computation carried out as a polynomial identity in `A` (Lean chain). It
  cannot be a finite list of residue-class checks at finitely many primes,
  because the obstructing prime varies with `A` (§7.2 of the article is correct
  on this point) — this is what §2.2 illustrates concretely.
* Corollary 1.5 / §6 (Pell exponent, R | N): outside this direction; covered by
  another member.

---

## 4. Reproduction

Everything below runs on the audit VM from `.ultramath/smw70l62n/m3/`.

```
python3 work/certificate_check.py    # §1.1: disc, maximality, resultants, Table A1, (A.2), (A.3), (A.5)
gp -q < work/dyadic17.gp             # §1.2: three local symbols, p = 17 (+ bare-theta product)
gp -q < work/dyadic41.gp             # §1.2: three local symbols, p = 41 (nfinit takes ~14 s)
gp -q < work/nfhilbert_validation.gp # §1.2: nfhilbert convention vs hilbert(.,.,2) at the e=f=1 prime
gp -q < work/dyadic_general.gp       # §2.1: dyadic product at A = 2,10 (2 mod 8) and 6,14,22 (6 mod 8)
gp -q < work/bridge17.gp             # §1.3: odd-product bridge at A = 2,10,14
gp -q < work/bridge_ramified.gp      # §1.3: ramified prime l = 17 at A = 18
gp -q < work/bridge_higher.gp        # §1.3: higher valuations v_3 = 3, 2 at A = 22, 58
python3 work/stress_final.py         # §1.4: 11000 exact Jacobi/gcd checks
python3 work/chain17.py              # §2.2: Lean chain identities, resultants, common factor at A = 10
```

Files: `work/defs.py` (D_n, F_n, g_p, U_p from the article's definitions),
`work/certificate_check.py`, `work/chain17.py`, `work/stress_final.py`, `work/dyadic17.gp`, `work/dyadic41.gp`, `work/dyadic_general.gp`,
`work/bridge17.gp`, `work/bridge_ramified.gp`, `work/bridge_higher.gp`,
`work/nfhilbert_validation.gp`, `work/OUTPUTS.txt` (recorded output of every
command above, produced by one clean batch run; it contains no error lines).
