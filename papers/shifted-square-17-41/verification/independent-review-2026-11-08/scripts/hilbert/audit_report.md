# Independent audit of the human-only Hilbert / 2-adic chain (p = 17, 41)

Member m6 (direction d3), swarm smw70l62n.
Repository commit: `c663b4e1e65c99846d41270a288f154559cc9fd6`.
Sources read: `papers/shifted-square-17-41/manuscript/revision/paper_1_github.md`
(§§1.3, 2.4, 3, 4, 7, Appendix A/C),
`papers/shifted-square-17-41/hilbert-obstruction-lamport.md` (H1, H2),
`papers/shifted-square-17-41/hilbert-jacobi-crosswalk.md`,
`papers/shifted-square-17-41/reading/magma-17-41-comparison.md`,
`papers/shifted-square-17-41/reading/fixed-field-obligation-table.md`.
Tool: `PARI/GP 2.17.3` (`/opt/math/bin/gp`), invoked as `gp -q <script>`.

## 0. Verdict

**No mathematical gap was found in the Hilbert / 2-adic chain as it is stated and
used at p = 17, 41.** Every load-bearing finite input was recomputed from the
paper's own definitions, and every cited theorem is instantiated correctly. The one
citation whose application is genuinely load-bearing at *arbitrary* exponents — the
non-dyadic symbol formula (3.7), used to turn the odd-place symbols into a Jacobi
symbol — is additionally verified directly at six non-reference parameter points
(28 supporting-prime characters, §5), not merely at the reference. Two reporting
points are recorded: §3.3's (3.5) is a shorthand that needs one localization sentence
(§4; expanded here, and nothing outside the paper is required), and Prop 7.1's phase
restriction `A ≡ 2 (mod 8)` is stronger than needed (§6). One open end flagged by
another member (the `A ≡ 6 (mod 8)` Jacobi identity, "true numerically but needs a
different argument") is closed here with a complete proof and exact scope (§6).

Independence level, stated honestly:

* **Derivation path: independent.** All numbers below were produced by scripts
  written from the paper's definitions only (`D_n`, `g_p`, `U_p`, `b_p = θU_p(θ)`,
  `δ_x = (x−θ)/θ`), without importing any project script, and the dyadic Hilbert
  symbols are computed **directly and locally** (`nfhilbert`), whereas the paper
  derives their product by reciprocity from the odd reference characters. At the
  degree-one dyadic prime (completion `Q_2`) the sign is additionally reproduced by
  a from-scratch 2-adic computation that uses no number-field routine at all.
* **CAS: not independent.** `PARI/GP 2.17.3` is the same version the project's own
  archived GP comparison used (Magma was the second CAS there). This audit is a
  reproduction with an independent *method*, not a cross-CAS check; that is
  direction d7's task. No Magma and no class-group/unit-basis computation was used.

## 1. Finite inputs, recomputed (all exact, exit status 0)

Script `audit_data.gp` (output `out_audit_data.txt`), `audit_hilbert.gp`
(`out_audit_hilbert.txt`), `audit_chain.gp` (`out_audit_chain.txt`):

| Claim (paper location) | Recomputed value | Status |
|---|---|---|
| `g_17(4)`, `g_41(4)` (A.1) | 45537549122, 50755107359004694554823202 | match |
| `disc g_17`, `disc g_41` (Table 3) | `2^24·17^17`, `2^60·41^41` | match |
| field disc = poly disc (index 1) | `nfdisc = poldisc` in both fields | match |
| signature (Table 3) | `(1,8)`, `(1,20)` | match |
| irreducibility witness (Table 3) | `g_17 mod 67`, `g_41 mod 163` irreducible, single factor of degree p | match |
| `Res(g_p,U_p) = −1` (4.5),(4.9) | `−1`, `−1` | match |
| `N(θ)`, `N(u_p)`, `N(b_p)` (4.11) | `2`, `−1`, `−2` | match |
| `U_17(4)`, `U_41(4)` (4.6),(4.10) | 532303029, −43956715453803235217163523 | match |
| `H_17`, `H_41` factorisations (4.6),(4.10) | `13·1751444197`, `79·1373·115471·1506563·1344905911`; all factors prime, all exponents 1 | match |
| Table A1 Legendre vector `(4U_p(4)/ℓ)` | `(−1,+1)`; `(+1,−1,−1,−1,+1)`; products `−1` | match |
| `J(U_p(4),H_p)` | `−1` in both fields | match |
| Dedekind index criterion inputs (A.3),(A.5) | `factormod(g_p,2)` = `[T^1,φ^2,ψ^2]` with `deg φ=deg ψ=(p−1)/4`; `g_p(2)/p mod p` = 12, 26 | match |
| unique prime above p (H2 hypothesis 3) | one prime, `e=p`, `f=1`, equals `(p,θ−2)` | match |
| dyadic prime types (Table 4) | `(1,1),(2,4),(2,4)`; `(1,1),(2,10),(2,10)`, `Σef=p` | match |
| dyadic valuations `(t,d,s)` (Table 4) | `(1,1,1),(0,0,0),(0,0,0)` in both fields | match |
| strict inequalities `4e−d>2e` (Table 4) | margins `3>2`, `8>4`, `8>4` | match |
| odd supporting primes at x=4 | for every `ℓ|H_p`: exactly one prime above `ℓ` divides `δ_4`, with `f=1`, `v_P(δ_4)=1=v_ℓ(H_p)`, others 0 | match (paper's A.1 claim "unique supporting prime of residue degree one, valuation one") |

So the finite data of Tables 3, 4, A1 and the claims (4.5)–(4.12), (A.1)–(A.5)
are all reproduced from scratch.

## 2. The dyadic reference product: direct local computation

The paper is explicit that its own finite verifier does **not** recompute the
individual dyadic signs and that these are "additional data from the number-field
certificate [8], not deductions from the valuation columns", the product `(4.12)`
being recovered by reciprocity from the odd characters A.1. That is the thinnest
point of the chain (a single sign, obtained indirectly). I computed it directly.

`nfhilbert(nf, δ_4, b_p, P)` at the three primes `P | 2`
(`audit_hilbert.gp`):

| p | `(e,f)` of P1, P2, P3 | `(δ_4,b_p)_P` | product |
|---|---|---|---|
| 17 | `(1,1),(2,4),(2,4)` | `+1, +1, −1` | `−1` |
| 41 | `(1,1),(2,10),(2,10)` | `+1, −1, +1` | `−1` |

As a **multiset** this is exactly Table 4 (`+1,−1,+1`) in both fields. Positionally
it differs for p = 17 only: the table's `−1` row is the repeated-type prime with
identifier `h = [1,1,0,0,1]` in the archived Magma/GP comparison, which is P3 in
PARI's `idealprimedec` ordering, whereas the table lists that row second (p = 41
agrees positionally, the `−1` being the prime `h = [1,1,0,1,1,0,0,1,1,0,1]` =
P2 for PARI). The paper states that Table 4 "specifies the multiset of rows, not a
preferred ordering", so there is no discrepancy; but a reader who reads the table as
a positional assignment sees one. Worth a one-line clarification in a revision.

At the prime with `(e,f) = (1,1)` the completion is `Q_2`, so the sign there can be
checked without any number-field routine (`audit_chain.gp`):

1. Newton-lift the root `τ ∈ 2Z_2` of `g_p` (start `2`, `v_2(g_p(2)) = 6` or `5`,
   `g_p'(τ)` odd) to `|τ|_2 = 2^{-64}`; verified `g_p(τ) ≡ 0 (mod 2^32)`.
2. `δ_4 ↦ (4−τ)/τ = (2−σ)/σ` with `σ = τ/2`; `b_p ↦ τ U_p(τ)`. Reduce to residues
   mod 8: `(4−τ)/τ ≡ 1 (mod 8)` and `b_p/2 ≡ 1 (mod 8)` in both fields.
3. Classical `Q_2` symbol: for units `a ≡ 1 (mod 8)`, `(a,2) = (−1)^{(a²−1)/8} = +1`,
   and for units `a, v ≡ 1 (mod 8)`, `(a,v) = (−1)^{((a−1)/2)((v−1)/2)} = +1` since
   `(v−1)/2` is even. With `b_p = 2v` this gives `((4−τ)/τ, b_p)_{Q_2} = +1`.
   Cross-check with GP's own p-adic `hilbert(a,c,2)` on the residue representatives:
   `+1`, agreeing with `nfhilbert` at that prime.

Also checked (paper Prop 4.1, the "why a unit is needed" step): replacing `b_p` by
`θ_p` gives product `+1` in both fields, as Prop 4.1 asserts.

## 3. Strict Hensel: instantiation, transfer, and sharpness

*Form of the citation.* The strong-Hensel hypothesis used, `v(F(a)) > 2v(F'(a)) ⇒
root near a`, is the standard form (Conrad, *Hensel's Lemma*, Thm 9.1; equally
Jarden's Hensel–Rychlik form). Applied to `F(S) = S² − (1+z)` at `S = 1` it reads
`v_P(z) > 2v_P(2) = 2e_P`, exactly hypothesis 4. Note `v_P(z) ≥ 4e−d > 2e ≥ 0`
also gives `1+z ∈ O_L`, so no integrality side condition is missing.

*Transfer.* For `x = 4 + 16k` (`k = 0..6`) and `x = 16 000 004`, the three dyadic
symbols `(δ_x,b_p)_P` are **identical** to the `x = 4` reference in both fields
(`audit_chain.gp`, `audit_phase2.gp`, `audit_extra.gp`). The same holds for
`x = 12 + 16k` against the `x = 12` reference, up to `x = 16 000 012`. So (3.8)–(3.10)
is confirmed far from the reference, not just at it.

*Sharpness (the strictness is not cosmetic).* At `x ≡ 12 (mod 16)` the hypothesis
fails by exactly one unit: for the degree-one prime `3e−d = 3·1−1 = 2 = 2e`, and the
symbol really does change:

| p | `(δ_x,b_p)_P` at `x=4` | at `x=12` | at `x=28,44,60,76` |
|---|---|---|---|
| 17 | `+1,+1,−1` | `−1,+1,−1` | `−1,+1,−1` |
| 41 | `+1,−1,+1` | `−1,−1,+1` | `−1,−1,+1` |

So `δ_12/δ_4` is not a dyadic square at the degree-one prime in either field, while
`δ_x/δ_12` is one for all `x ≡ 12 (mod 16)`. Hypothesis 4 cannot be weakened to
`≥`; this is the concrete counterexample to such a weakening, the abstract one being
`5 = 1+4` in `Q_2` quoted in §3.5.

## 4. One shorthand in the paper, expanded (not an error, and not a missing input)

§3.3, step (3.5): "For each rational prime `ℓ | g(x)`, the right side has exactly one
prime above `ℓ`, with residue field `F_ℓ`. Consequently, exactly one prime ideal
`P | ℓ` divides `x−θ`, and its residue degree is one."

`O_L/(x−θ) ≅ Z/(g(x))` is a nonzero ring, so it does have prime ideals; what the
sentence abbreviates is a statement about a *rational* prime `ℓ`, obtained by
localizing at `ℓ`:

  `O_L/(x−θ) ⊗_Z Z_ℓ ≅ Z_ℓ / ℓ^{v_ℓ(g(x))}`,

which is a local ring with residue field `F_ℓ` (and `ℓ`-adic length `v_ℓ(g(x))`). On
the other hand `O_L/(x−θ) ⊗ Z_ℓ ≅ ∏_{P|ℓ} O_{L,P}/(x−θ)^{v_P(x−θ)}`, and a nonzero
factor has residue field `F_{ℓ^{f(P/ℓ)}}`. A product of two nonzero factors has
residue ring a product of two fields, not a field, and a zero factor is impossible
since `g(x) ≠ 0`. Hence exactly one `P | ℓ` supports `x−θ`, with `f(P/ℓ) = 1` — also
at a ramified `ℓ` — which is exactly what (3.6) uses
(`v_ℓ(Nδ_x) = Σ_Q f(Q/ℓ) v_Q(δ_x) = v_P(δ_x)`).

So the paper's (3.5), plus this one sentence of localization, yields the step: nothing
external is needed. The companion note reaches the same conclusion by a
Dedekind–Kummer case split, which is an alternative route rather than a dependency.
The only expository defect is that the sentence cannot be read literally as written
("the right side has exactly one prime above ℓ").

## 5. Cited-theorem instantiation audit

| Input | Citation | Verdict |
|---|---|---|
| Hilbert reciprocity | Milne, CFT VIII §5.10 (+ III §4 for the pairing) | standard, correctly used (all places, finitely many non-trivial) |
| non-dyadic local formula (3.7) | Oh, ANT Thm 16.32 | correct; used in two roles, only one of which is convention-insensitive — see the paragraph below the table |
| strong Hensel | Conrad, Thm 9.1 | matches (§3) |
| Dedekind's index criterion | Vidaux–Videla, Thm 1.1 | statement matches exactly ("for all i, `e_i = 1` or `φ_i ∤ ḡ`"); both instantiations (at 2 with `φ²ψ²`, at p with `(T−2)^p`) are literal instances of it |
| Dedekind–Kummer | Sutherland 6.14 | used only to read off dyadic types `(e,f)`; independently confirmed by `idealprimedec` |
| Sanna Thm 1.5 (alternative proof of Thm 1.3) | Sanna, FQ 54 (2016) | not needed; the article's own doubling proof is complete, and Thm 1.3 is Lean-covered |

**The two roles of (3.7), and how far the sign-insensitivity goes.**

* *Odd-place neutrality* (hypothetical square, `Q = Y²`): here `r = v_P(δ_x) = v_ℓ(Q)`
  is even and `s = v_P(b_p) = 0`, so all three factors of (3.7) equal `1` for trivial
  reasons (`rs = 0`, `χ(ā₀)^0 = 1`, `χ(b̄_p)^r = 1` for even `r`). This step, and only
  this step, is insensitive to every convention in (3.7).
* *The Jacobi bridge* (Prop 7.1, and the lemma of §6): `r` is **arbitrary**, and it is
  precisely the factor `χ(b̄_p)^r` that produces `(xU_p(x)/ℓ)^{v_ℓ(Q)}`, i.e. the
  Jacobi symbol. Here (3.7) is load-bearing at arbitrary `r`; what `s = 0` still kills
  is the prefactor `(−1)^{rs(q−1)/2}` and the factor `χ(ā₀)^s`. The `r`-dependence
  itself is essential and is not a convention.

I therefore verified the bridge directly, and at **non-reference points**, not only at
`x = 4` (`audit_bridge.gp`, output `out_audit_bridge.txt`). Six points are checked —
`p = 17` at `x = 20, 28, 36` and `p = 41` at `x = 12, 20, 28` — with `Q = g_p(x)/2`
factored at each, giving 28 rational primes `ℓ | Q` in total; at every one of them I
check three assertions: exactly one prime `P | ℓ` supports `δ_x`; `f(P/ℓ) = 1` and
`v_P(δ_x) = v_ℓ(Q)`; and `(δ_x,b_p)_P = (xU_p(x)/ℓ)^{v_ℓ(Q)}`. All 28 local checks
pass and the products equal `J(xU_p(x), Q)` in every case: `−1, +1, −1` for `p = 17`
and `−1, +1, +1` for `p = 41`. The sample is chosen to exercise the two cases the
argument is most exposed to: `p = 41, x = 12` has `v_5(Q) = 3` (so the valuation
assertion `v_P(δ_x) = v_ℓ(Q)` is tested with exponent three, not only one), and
`p = 17, x = 36` has `17 | Q`, so the **ramified** prime `ℓ = p` occurs in the support
and the ramified branch of §4 is exercised directly. Two of the points (`x = 28`) are
in phase 2, where the product is `+1` as §6 requires. So the content of (3.7) that the
Jacobi bridge relies on is machine-verified rather than merely cited; what remains
unverifiable by computation is only the general statement of (3.7) for arbitrary `r`,
which these checks support, and not its sign conventions in the even-`r` neutrality
step (which are inert there for the reasons above).

Machine spot checks of the 2-adic side of the same story: `F_n(A) − 1 ≡ 1 (mod 8) ⟺
(A mod 8, n mod 4) ∈ {(2,1),(6,3)}` for 90 `(A,n)` pairs (no mismatch); 2-adic
squareness of odd units against `issquare` on `Q_2` p-adics agrees with the mod-8 test;
Theorem 1.3's valuation formula `v_2(F_N−1) = 2v_2(N)+1` holds for 180 `(A,N)` pairs.

## 6. Closing the phase-2 loose end: a two-phase Jacobi certificate

**Lemma.** Let `p ∈ {17,41}` and let `U_p` be the detector polynomial of (4.4) or
(4.7)–(4.8). Then for every `A ∈ Z_{≥0}` with `A ≥ 2` and `A ≡ 2 (mod 4)`,

  J(U_p(2A), F_p(A) − 1) = −1.

(The paper's Prop 7.1 is the case `A ≡ 2 (mod 8)`.)

**Proof.** Put `x = 2A`, `Q = g_p(x)/2 = F_p(A) − 1 > 0` odd, `δ_x = (x−θ)/θ`,
`b_p = θ U_p(θ)`.

(a) *Phase-independent bridge.* The support analysis of §3.3 and the local formula
(3.7) with `s = v_P(b_p) = 0` give, for every admissible `x` and with no squareness
assumption,
`∏_{P∤2} (δ_x,b_p)_P = J(xU_p(x), Q)`.

(b) *Archimedean.* `0 < θ_R < 2` and `x ≥ 4`, so `δ_{x,R} > 0` and the real symbol is
`+1`; complex symbols are `+1`.

(c) *Phase 1, `A ≡ 2 (mod 8)`*, i.e. `x ≡ 4 (mod 16)`. Strict Hensel relative to
`x₀ = 4` gives `∏_{P|2}(δ_x,b_p)_P = ∏_{P|2}(δ_4,b_p)_P = −1` (computation in §2), so
reciprocity forces the odd product to be `−1`. Here `x = 4m` with `m = A/2 ≡ 1 (mod 4)`
and `Q ≡ 1 (mod 8)`; `Q ≡ −1 (mod m)` gives `gcd(m,Q) = 1`, and
`J(m,Q) = J(Q,m)(−1)^{((m−1)/2)((Q−1)/2)} = J(−1,m) = +1`,
so `J(x,Q) = J(4,Q)J(m,Q) = 1`. Hence `J(U_p(x),Q) = −1` (this is Prop 7.1).

(d) *Phase 2, `A ≡ 6 (mod 8)`*, i.e. `x ≡ 12 (mod 16)`. Strict Hensel relative to the
**new reference `x₀ = 12`** applies with the same margins: `v_P(x−12) ≥ 4e_P`, and
`v_P(12−θ) = (1,0,0)` with `4e−d' = (3,8,8) > 2e = (2,4,4)`. Hence
`∏_{P|2}(δ_x,b_p)_P = ∏_{P|2}(δ_12,b_p)_P = +1` (computed: `(−1,+1,−1)` for p = 17,
`(−1,−1,+1)` for p = 41; product `+1`). Reciprocity forces the odd product to be `+1`,
i.e. `J(xU_p(x),Q) = +1`. Now `x = 4m` with `m = A/2 ≡ 3 (mod 4)` and `Q ≡ 5 (mod 8)`
by (2.8), so `(Q−1)/2` is even and
`J(m,Q) = J(Q,m)·1 = J(−1,m) = −1`, whence `J(x,Q) = −1`. Therefore
`J(U_p(x),Q) = J(xU_p(x),Q)/J(x,Q) = (+1)/(−1) = −1`. ∎

**Exact scope.**

* The lemma is an unconditional arithmetic identity in `A`; it strictly strengthens
  Prop 7.1 (which is stated only for `A ≡ 2 (mod 8)`).
* It adds **no exclusion content**: for `A ≡ 6 (mod 8)` one already has `Q ≡ 5 (mod 8)`,
  a nonsquare modulo 8 (Prop 2.1), so no shifted square occurs there.
* It does show that the *Hilbert* route cannot be run in phase 2 with any reference
  point in `x ≡ 12 (mod 16)`: the dyadic reference product is `+1` there, so
  Theorem 3.2's hypothesis (5) / H1's condition (3) fails identically. The sign of the
  reference product is a property of the residue class of `x₀` modulo 16, not of a
  cleverer detector. Phase 2 is excluded only by the modulo-8 argument.
* The Jacobi identity survives in phase 2 because the Jacobi numerator factor `J(x,Q)`
  flips from `+1` to `−1` exactly when the dyadic product flips from `−1` to `+1`.
  That is the mechanism behind the phenomenon observed numerically by member m3 (d2).

**Evidence.** `audit_phase2.gp`, `audit_extra.gp`, `audit_chain.gp`: the identity holds
for all `A ≡ 6 (mod 8)`, `6 ≤ A ≤ 4002` (500 values per prime) and at `A = 8 000 006`
(`J = −1`, `J(x,Q) = −1`, dyadic symbols equal to the `x = 12` reference); the
reference data at `x = 12` are exact: `Q₁₂ = g_p(12)/2` factors as
`5·7·2027·327409·53676437` (p = 17) and `5³·7·127·340589686313053·3088464279517699581144853`
(p = 41), all factors prime, and `J(12U_p(12),Q₁₂) = +1`, `J(U_p(12),Q₁₂) = −1` in both
fields — so reciprocity at `x = 12` (`odd·dyadic·real = 1`, odd `= +1`, real `= +1`)
independently predicts dyadic `= +1`, agreeing with the direct local computation.

## 7. What remains human-only after this audit, with residual risk

| Step | Status after this audit | Residual risk |
|---|---|---|
| finite inputs, Tables 3, 4, A1 | exact machine data, reproduced twice | negligible |
| dyadic product `−1` (hypothesis 5) | computed directly at the three primes; also re-derived by reciprocity | negligible |
| odd-prime valuation parity (H2.2) | elementary human argument, checked case split, machine instances verified | low: any error must be in the localization/Dedekind–Kummer step, which is short |
| non-dyadic local formula use | neutrality step insensitive to conventions; Jacobi-bridge step uses arbitrary `r` and is verified directly at 6 non-reference points (28 prime-ideal characters, including one exponent-3 prime and the ramified supporting prime) | low |
| strict Hensel transfer | human proof with cited standard theorem; machine-verified at 12 parameter points; sharpness confirmed | low |
| real-embedding positivity | human, exact via `D_p(T) = 2 sinh(p arsinh(T/2))` strictly increasing | negligible |
| reciprocity (H1) | human, cited | negligible |
| `b_p` unit / `(b_p) = (θ)` | resultant `−1`, exact | negligible |

The chain is therefore not a "human-only argument over unverified numbers": the
numbers are verified, and the human content that remains is the short parity lemma,
the real-embedding positivity argument, and the instantiation of two cited theorems
(reciprocity, strong Hensel) whose hypotheses are checked above. My audit of the paper-to-Lean boundary is out of scope here (direction d8),
as is Corollary 1.5 (d1) and the certificate regeneration for other consumers (d7).

## 8. What I did not do

* Did not rerun the public build, the Lean development, or the project's own verifier.
* Did not compute class groups or unit-group bases (not needed for any input used).
* Did not use Magma, so this is not a cross-CAS check; it is a same-CAS, independent-method
  reproduction.
* Did not audit Corollary 1.5 (exponent/rank), the manuscript's Corollary 1.5 numbers, or
  the Lean statement fidelity.
* All stress tests are *numerical experiments*, not proofs; they are labelled as such.
  The only new theorem asserted is the Lemma of §6, whose proof is given in full.

## 9. Reproduction

```
cd <session workdir>
gp -q audit_data.gp        # polynomial, discriminant, resultant, norm, H_p, A1 characters
gp -q audit_hilbert.gp     # dyadic types/valuations, direct nfhilbert signs, transfer tests, odd support
gp -q audit_chain.gp       # signature, ramified prime, Prop 4.1, from-scratch Q_2 sign, stress tests
gp -q audit_phase2.gp      # x=12 reference data, phase-2 stability, reciprocity consistency
gp -q audit_final.gp       # mod-2 factorisation, Prop 2.1 scan, phase-2 characters
gp -q audit_extra.gp       # phase-2 margins, huge-A identities, Theorem 1.3 scan
gp -q audit_bridge.gp      # (3.7) at non-reference points, arbitrary r, per supporting prime
gp -q audit_sweep.gp       # no shifted squares for A = 2 mod 4, A <= 4002
```

Captured outputs: `out_audit_*.txt` (all runs exit 0).
Environment: `PARI/GP 2.17.3`, run as `gp -q`; no project scripts imported.
