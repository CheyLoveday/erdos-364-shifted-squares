# A complete re-derivation of Theorem 1.2 (fixed indices 17, 41)

Independent of the paper's prose: every hypothesis below is either (i) a finite
computation reproduced in `cert/verify_independent.py`, or (ii) a named standard
theorem. No step is asserted without one of these. This is a human proof (with
finite certificate inputs), not a formalisation.

Notation: `p ∈ {17,41}`; `A ∈ Z`, `A ≥ 2`, `A ≡ 2 (mod 8)`; `x = 2A`;
`Q = g_p(x)/2 = F_p(A) - 1`; `θ = θ_p` a root of `g_p`; `L = Q(θ)`; `O_L = Z[θ]`;
`U_p` the detector of (4.4) / (4.7)–(4.8); `u = U_p(θ)`; `b = θu`;
`δ_x = (x-θ)/θ`; `J(·,·)` the Jacobi symbol with `J(c,1) = 1`.

## H0. Field hypotheses (all finite, all reproduced independently)

| Hypothesis | Source | Verified |
|---|---|---|
| `g_p` monic irreducible, `g_p(0) = -2`, `disc(g_p) = 2^{3(p-1)/2} p^p` | Table 3 | exact |
| `[O_L : Z[θ]] = 1` (Dedekind criterion at `q = 2` and `q = p`) | A.2 | exact, own implementation |
| signature `(1,(p-1)/2)`; real root `θ_R ∈ (0,2)` | (4.1) | Descartes + sign analysis |
| `N(θ) = 2`, `N(u) = -1`, `N(b) = -2`, `Res(g_p,U_p) = -1` | (4.5),(4.9),(4.11) | exact |
| `(2) = P_1P_2^2P_3^2`, `f(P_1)=1`, `f(P_2)=f(P_3)=(p-1)/4` | Table 4 | exact (`g_p ≡ Tφ²ψ² mod 2`) |
| `(p)` totally ramified, `f = 1` | (A.4) | exact |
| `v_{P_1}(θ) = 1`, `v(θ) = 0` at every other prime | §A.2 | from `N(θ)=2` |

Consequences used below, each immediate:

* `v_P(θ) = 0` at every odd `P`, so `b` is a unit at every odd `P` (since `N(b) = -2`).
* `(b) = (θ) = P_1` (both have norm `2`), so `v_P(b) ≥ 1` implies `P = P_1 | 2`.
* `δ_x ∈ O_L` and `N(δ_x) = g_p(x)/2 = Q`.
  Integrality: at `P_1`, `v(θ)=1` and `v(x-θ) ≥ min(v(x),1) = 1` because
  `v_{P_1}(x) = v_2(x) = v_2(2A) ≥ 1`; at all other `P`, `v(θ) = 0`.
* `Q > 0` and `Q` odd for `A ≥ 2`, `A ≡ 2 (mod 8)`: positivity because
  `g_p'(t) > 0` for `t > 0` (every nonconstant coefficient of `g_p` is positive),
  `g_p(0) = -2 < 0 < g_p(4)`; oddness from `Q_0(A) ≡ A - 1 (mod 8)` (report.md §3.3).

## H1. Odd places: the local product is a Jacobi symbol

Let `ℓ` be an odd rational prime with `ℓ | Q`, and let `P` range over primes of
`O_L` above `ℓ` with `v_P(δ_x) > 0`, i.e. with `θ ≡ x (mod P)`.

Since `O_L = Z[θ]`, the primes above `ℓ` match the irreducible factors of
`g_p mod ℓ`. The residue class `x` is a root of `g_p mod ℓ`, so the only factor that
can vanish at `θ` is the linear one `T - x`; hence there is **exactly one** such `P`,
it satisfies `f(P) = 1`, and its ramification index is the multiplicity `e` of `x` as
a root of `g_p mod ℓ` (so `P` may be ramified; it is still unique, with `f = 1`).

*Valuation.* `N(x - θ) = g_p(x)`, so (with `ℓ` odd)
`v_ℓ(Q) = v_ℓ(g_p(x)) = Σ_{P|ℓ} f(P) v_P(x-θ) = v_{P}(x-θ)`,
and `v_P(δ_x) = v_P(x-θ) - v_P(θ) = v_ℓ(Q)`.

*Local symbol.* Let `π = π_P` be a uniformiser and `a = v_P(δ_x) = v_ℓ(Q)`.
The tame symbol formula at a place of residue characteristic `ℓ` with residue field
`F_ℓ` (Serre, *Local Fields*, XIV §2) gives `(π,w)_P = (w mod P)^{(ℓ-1)/2}` for a unit
`w`, and `(w_1,w_2)_P = 1` for units `w_1,w_2` (the extension `K_P(√w_1)/K_P` is
unramified and a unit is a norm from it). Hence

    (δ_x, b)_P = (π,b)_P^{a} = (b mod P)^{a·(ℓ-1)/2},

and `b = θU_p(θ) ≡ x U_p(x) (mod P)` with `xU_p(x)` not divisible by `ℓ` (H2 below).
Therefore

    ∏_{P ∤ 2∞} (δ_x,b)_P = ∏_{ℓ|Q} (x U_p(x) / ℓ)^{v_ℓ(Q)} = J(xU_p(x), Q).      (1)

## H2. Coprimality, and removal of the factor `x`

*Claim.* `gcd(U_p(2A), Q) = 1`. Suppose an odd `ℓ` divided both. Then `ℓ | Q = N(δ_x)`,
so some `P | ℓ` has `v_P(δ_x) > 0`, hence `θ ≡ x (mod P)`, hence
`U_p(θ) ≡ U_p(x) ≡ 0 (mod P)`, so `v_P(b) ≥ 1` and `ℓ | N(b) = -2`: contradiction.
This is the argument the paper invokes when it says that `b_p` is an odd-place unit and
therefore the residue `xU_p(x)` on the right of (7.3) is nonzero; §2 here only spells it
out. Worth recording: `Res(g_p,U_p) = -1` alone would *not* give the claim, since a
resultant forbids a common polynomial root, not a common prime divisor of
specialisations. The second ingredient, `ℓ ∤ x`, follows from `Q_0(A) ≡ -1 (mod A)` for
every `A`, which gives `gcd(Q,A) = 1`, while `ℓ | x = 2A` would force `ℓ | A`. Also
`Q ≠ 0`, so the symbol is defined.

Write `x = 4m`, so `m ≡ 1 (mod 4)` (as `x ≡ 4 mod 16`). Since `Q_0(A) = -1 + Σ_{k odd} c_k A^k`
and `A = 2m`, every term with `k ≥ 1` is divisible by `m`, so `Q ≡ -1 (mod m)` and
`gcd(m,Q) = 1` (including `m = 1`). Quadratic reciprocity, `m ≡ 1 (mod 4)` and
`Q ≡ -1 (mod m)` give `J(m,Q) = J(Q,m) = J(-1,m) = 1`, and `J(4,Q) = 1` because `Q` is
odd. So `J(xU_p(x),Q) = J(U_p(x),Q)`, and (1) becomes

    ∏_{P ∤ 2∞} (δ_x,b)_P = J(U_p(2A), Q).                                          (2)

## H3. The places above 2 and ∞

*Real.* `θ_R ∈ (0,2)` and `x ≥ 4`, so `δ_x > 0` at the real embedding: symbol `+1`.
*Complex:* `+1`.

*Dyadic.* Claim: `∏_{P | 2} (δ_x,b)_P = -1` for every `x ≡ 4 (mod 16)`.

(a) *At `x = 4`.* The odd product is `∏_{ℓ | H_p} (4U_p(4)/ℓ)` with
`H_p = g_p(4)/2`, computed exactly in Table A1: `-1` in both fields. The real and
complex symbols are `+1`. Hilbert's product formula at `x = 4` therefore forces the
dyadic product to be `-1`.

(b) *Stability.* `δ_x/δ_4 = 1 + t` with `t = (x-4)/(4-θ)`. For `P | 2`,
`v_P(x-4) = e·v_2(x-4) ≥ 4e` and `d := v_P(4-θ) ∈ {1,0,0}`, so
`v_P(t) ≥ 4e - d > 2e = 2v_P(2)`. Newton–Hensel applied to `f(Z) = Z² - (1+t)` at
`Z = 1` (`v(f(1)) = v(t) > 2v(f'(1)) = 2v(2)`) gives a square root in `K_P`, so
`(δ_x,b)_P = (δ_4,b)_P` for each `P | 2`. Hence the dyadic product is `-1` for all
`x ≡ 4 (mod 16)`.

Note (b) uses only `d < 2e`, which holds for the three rows `(e,d) = (1,1),(2,0),(2,0)`;
those rows are themselves forced by `N(θ) = 2`, not independent data (report.md §3.4).

## H4. Conclusion

By (2), H3 and Hilbert's product formula over `L`,
`J(U_p(2A), Q) = ∏_{finite P} (δ_x,b)_P = -1` for every `A ≡ 2 (mod 8)`, `A ≥ 2`.
If now `Q = y²` with `y ∈ Z`, then `y ≠ 0` (as `Q > 0`) and every prime divisor of
`y` divides `Q`, so H2 gives `gcd(U_p(2A), y) = 1`; hence
`J(U_p(2A), Q) = J(U_p(2A), |y|)² = 1`, contradicting (2)/H3. (Note `gcd(y,Q) = |y|`
in general: the coprimality that matters is with the *numerator*, not with `Q`.) So
`F_p(A) - 1` is not a square for `A ≡ 2 (mod 8)`.

For `A ≡ 6 (mod 8)` and `n ≡ 1 (mod 4)` — in particular `n = 17, 41` —
`F_n(A) - 1 ≡ nA - 1 ≡ 5 (mod 8)` (report.md §3.3), which no integer square is. The
hypothesis `n ≡ 1 (mod 4)` is needed: at `A = 6`, `n = 3` one has
`F_3(6) - 1 = 881 ≡ 1 (mod 8)`, so the congruence excludes nothing. Combining, for
every `A ≥ 2` with `A ≡ 2 (mod 4)`, `F_p(A) - 1` is not a square — that is Theorem 1.2
for both `p`.

## What this proof rests on

* Finite exact computations (all reproduced in `cert/verify_independent.py` with
  independent code): `disc`, index one, the two dyadic factorisations, `Res = -1`,
  `H_p` factorisations, the seven Legendre signs of Table A1, `φ_p,ψ_p` irreducibility
  and the correction remainder.
* Standard theorems: quadratic reciprocity, Hilbert's product formula, the tame symbol
  formula, Newton–Hensel in a local field of residue characteristic 2.
* **Not** used: any individual dyadic Hilbert sign at `P_2,P_3` (only the product), the
  unit group or class group of `L`, any search over `A`, and any Lean development.
