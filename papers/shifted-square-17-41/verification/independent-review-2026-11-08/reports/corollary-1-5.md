# Independent audit of Corollary 1.5 (exponent restriction in the lower-square family)

Target: `papers/shifted-square-17-41/manuscript/revision/paper_1_github.md`
(article v1.0.1, source SHA-256 `c4398873…92bdd`, repository commit
`c663b4e1e65c99846d41270a288f154559cc9fd6`), Corollary 1.5 on p. 4 and its
proof in §6.2–§6.3, with the primary source D. T. Walker, *Consecutive
integer pairs of powerful numbers and related Diophantine equations*,
Fibonacci Quarterly 14 (1976) 111–116.

Everything below was done in this work area. Scripts:
`audit/cor15_audit.py` (hand-rolled exact arithmetic, no CAS),
`audit/crosscheck_sympy.py` (SymPy 1.14.0 cross-check),
`audit/pell_rank.py` (first, smaller version of §B).
Recorded output: `audit/audit_output.txt`.

---

## 0. Verdict

1. **No gap found in Corollary 1.5.** Each of its steps (normal form, phase,
   least unit, same-centre identity, rank divisibility, 17/41 exclusion) is
   re-proved below with its exact hypotheses and is correct. The step the
   corollary actually rests on and that is *not* in the Lean development —
   the rank computation (6.5)–(6.6) — is verified here both by an independent
   proof and by machine computation on 411 Pell instances.
2. **Sharpening (F2).** Lemma 1 below shows (6.6) needs **no** squarefreeness
   of `K`; the article's squarefree hypothesis is needed only for the
   `K^3 V^2` normal form and for Walker's product formula. Confirmed on 8
   non-squarefree instances.
3. **Hypothesis sharpness (F3).** (6.7) is false for even `K` (`K = 2` gives
   `R = 2` against norm-one rank `1`; 192 even `K ≤ 5000` fail). This matters
   for the paper↔Lean correspondence: Lean's `pellRank` is built from the
   *norm-one* fundamental solution, so it coincides with the article's `R`
   only under the article's own hypotheses (see F3).
4. **The hypothesis "`X-1` is a square" is load-bearing (F4).** Without it,
   with `X^2+1` still powerful and `X ≡ 2 (mod 8)`, one has `17 | N`
   (`K = 5, N = 85`) and `41 | N` (`K = 5, N = 205`). So (1.9) cannot be
   strengthened to the wider family, and the same-centre identity (6.4) in §6.2 is
   exactly what makes the corollary work.
5. **Walker's citation is accurate** in statement, equation number and page
   number (§3 below, verbatim from the scan). The article's own proof of
   (6.6) is self-contained, so Walker is corroboration, not a dependency.
6. **Non-vacuity is open (F6).** No `X` in the corollary's hypothesis class
   exists with `X ≤ 10^14` (a two-stage exact computation over all odd
   `y ≤ 10^7` with `X = y²+1`: necessary sieve plus a complete
   smooth-part/square-or-cube test, validated against brute force), nor among
   all 14 members with `X ≤ 10^60` of the family over odd squarefree
   `K ≤ 20000`. The corollary is therefore a genuine conditional statement:
   its conclusion is not vacuous *as a theorem*, but no witness is known in
   these ranges, so no numerical test of the conclusion is possible.

---

## 1. The claims, restated exactly

Setting (article (1.1)): `F₀(A)=1`, `F₁(A)=A`, `F_{n+2}(A)=2A F_{n+1}(A)+F_n(A)`.

**Corollary 1.5.** Let `X ≥ 2` with `X-1` a square and `X²+1` powerful.
Write `X²+1 = K³V²` with `K` squarefree, `K,V > 0`. Let `ε = u+v√K` be the
least unit `> 1` of the order `Z[√K]` (with `√K > 0`). Then
`N(ε) = -1`, there is a unique positive odd `N` with
`X + KV√K = ε^N`, `R := K/gcd(K,v)` divides `N`, and
`gcd(N, 17·41) = 1`.

Steps (article locators): (a) phase `X ≡ 2 (mod 8)`; (b) uniqueness of the
`K³V²` decomposition, `K > 1`; (c) `K ≡ 5 (mod 8)`; (d) `η := X+KV√K` is a
norm-`-1` unit of `Z[√K]`; (e) existence and generation property of the least
unit, `N(ε) = -1`; (f) `v` odd and `u ≡ 2 (mod 4)` (eq. (6.3)); (g) the
same-centre identity `X = F_N(u)` (eq. (6.4), using §6.1's (6.1));
(h) `R | N` (eq. (6.5)–(6.6)); (i) `gcd(N,17·41)=1` from Theorem 1.1.

---

## 2. Independent proofs

Throughout `K` is squarefree, `K > 1`, `K ≡ 5 (mod 8)` unless stated.

**(a) Phase.** `X²+1` powerful forces `X` even (`X` odd ⇒ `X²+1 ≡ 2 mod 4`,
i.e. `v₂ = 1`). Then `X-1 = y²` with `y` odd, so `y² ≡ 1 (mod 8)` and
`X ≡ 2 (mod 8)`. ✓

**(b) Decomposition.** For `n = Π q^{e_q}` put `K = Π_{e_q odd} q` and
`V = Π q^{(e_q - 3[2∤e_q])/2}`; powerfulness (`e_q ≥ 2`) makes the exponents
non-negative. Uniqueness: `v_q(n)` is `3 + 2v_q(V)` or `2v_q(V)`, so the
parity of `v_q(n)` decides `q | K`, and then `v_q(V)` is determined. ✓
`K > 1` because `X² < X²+1 < (X+1)²`. ✓

**(c) Phase of `K`.** `X ≡ 2 (mod 8)` ⇒ `X²+1 ≡ 5 (mod 8)`; `K,V` are odd
and odd squares are `1 (mod 8)`, so `K ≡ K³V² ≡ 5 (mod 8)`. Hence `K` is odd,
not a square, and `K ≡ 1 (mod 4)`. ✓

**(d) The unit.** `N(η) = X² - K²V²·K = X² - K³V² = -1`. ✓ (`η` lies in the
order since its coordinates are `X, KV ∈ Z`.)

**(e) Least unit.** Norms of units of an order of a real quadratic field are
`±1`. The set `{w unit : 1 < w ≤ M}` is finite: `|u| = |w + w̄|/2 ≤ (M+1)/2`
and `|v| = |w - w̄|/(2√K) ≤ (M+1)/(2√K)`, and `w̄ = ±1/w`. So a least unit
`ε > 1` exists. Any unit `w > 1` has a maximal `n ≥ 0` with `w ε^{-n} ≥ 1`;
the quotient is a unit and `1 ≤ w ε^{-n} < ε`, so it is `1` by minimality.
Hence the unit group is `{±ε^n}`. Since `η` has norm `-1` and `η > 1`,
`η = ε^N` with `N > 0`, and `(-1)^N = N(η) = -1`, so `N` is odd. Also
`N(ε) = -1` (otherwise all powers would have norm `+1`). Uniqueness of `N`
follows from `ε > 1`. ✓

Note the order `Z[√K]` is **not** the maximal order here (`K ≡ 1 mod 4`
makes `(1+√K)/2` integral); the article is explicit that it works in the
order, and every step above uses only the order. This is the point at which a
careless argument would break, and it does not. The choice is not cosmetic:
for `K = 5` the maximal order has fundamental unit `(1+√5)/2` and
`((1+√5)/2)³ = 2+√5`, so the article's `N = 5` (the `X = 682` member) is the
exponent **15** relative to the maximal order's least unit, and any statement
of the form `R | N` is order-relative. Both the rank `R = K/gcd(K,v)` and the
exponent `N` are computed in the same order, which is what makes (1.8)–(1.9)
coherent.

**(f) Parity (6.3).** `u² - Kv² = -1`, so `u² + 1 = Kv²`. If `v` were even,
`v² ≡ 0` or `4 (mod 8)` and `K ≡ 5`, so `Kv² - 1 ≡ 7` or `3 (mod 8)` — not a
square, contradicting `= u²`. So `v` is odd, `Kv² ≡ 5 (mod 8)`,
`u² ≡ 4 (mod 8)`, hence `u ≡ 2 (mod 4)`; also `u > 0` because
`u = (ε - ε^{-1})/2 > 0`. ✓ Machine check: 146 instances with `K ≡ 5 mod 8`,
`K ≤ 3000`, no violation (§G of the output).

**(g) Same-centre identity.** `ε² = (u² + Kv²) + 2uv√K = 2uε + 1`, so the
coefficient `X_n` of `1` in `ε^n` satisfies `X₀=1, X₁=u, X_{n+2} = 2uX_{n+1} + X_n`,
i.e. `X_n = F_n(u)` (article §6.1). Applying this to `ε^N = X + KV√K` gives
`X = F_N(u)` with `u ≡ 2 (mod 4)`, `u ≥ 0` — exactly the hypothesis of
Theorem 1.1. ✓ Machine check: 9 members with `X ≤ 10^{40}`, `K ≤ 2000`
(§G).

**(h) The rank lemma.** Write `ε^n = a_n + b_n√K`.

> **Lemma 1.** Let `K > 1` be an integer and `u,v ∈ Z_{>0}` with
> `u² - Kv² = -1` (so `gcd(u,K) = 1`). Put `g = gcd(K,v)` and `R = K/g`.
> Then for every `n ≥ 1`: `K | b_n ⟺ R | n`. In particular `R` is the least
> positive index with `K | b_n`, and `R = 1` iff `K | v`.
> **No hypothesis of squarefreeness on `K` is used.**

*Proof 1 (binomial, as in the article).* The coefficient of `√K` in
`(u+v√K)^n` is `b_n = Σ_{i≥0} C(n,2i+1) u^{n-2i-1} v^{2i+1} K^i`, and every
term with `i ≥ 1` is divisible by `K`. So `b_n ≡ n u^{n-1} v (mod K)`, which is (6.5).
As `u² ≡ -1 (mod K)`, `u` is a unit modulo `K`, so
`K | b_n ⟺ K | nv`. Writing `K = gK₀`, `v = gv₀` gives
`gcd(K₀,v₀) = 1`, hence `K | nv ⟺ K₀ | n v₀ ⟺ K₀ | n`. ∎

*Proof 2 (nilpotent thickening — a different framing).* In the ring
`A = Z[√K]/(K)` one has `(√K)² = K = 0`, so `A = Z[s]/(s², K)` and
`u + vs ↦ u^n + n u^{n-1} v s` by the binomial theorem. Hence
`K | b_n ⟺ n u^{n-1} v ≡ 0 (mod K)`, and the rest is as above. ∎

*Proof 3 (literature).* Walker, Theorem 2.2(3) and Theorem 2.5, quoted
verbatim in §3: the property-Q solutions of the minus-sign equation are
exactly the odd powers of `(x+y√D)^i`, `i` = the product of the distinct
primes dividing `D` but not `y`. For squarefree `K` odd, that product is
`K/gcd(K,v) = R`, so `K | b_n ⟺ R | n`. ∎

Then `b_N = KV` in (1.8) gives `R | N`. `N` odd and `R | K` odd give `R, E = N/R`
odd. ✓

**(i) The exclusions.** Lemma 1 plus (g) plus `u ≡ 2 (mod 4)` put us in
Theorem 1.1 (human-only for the fixed indices, Lean for the propagation), so
`17 ∤ N` and `41 ∤ N`. Any of `17|E, 41|E, 17|R, 41|R` implies `17|N` or
`41|N`. ✓

**Dependencies of the last step, spot-checked.** Since `N` is odd, only
Theorem 1.2 and Lemma 5.1 enter. Sampled checks (§H of the output): Lemma 5.1
`F_{mn}(A) = F_m(F_n(A))` for `A ≤ 7`, `m < 12`, `n` odd `< 24` (1152 checks,
no failure); the mod-4 phase (2.7) for `A ≡ 2 (mod 4) < 20`, `n < 40`; and
Theorem 1.3's `v₂(F_N(A)-1) = 2v₂(N)+1` for `A ∈ {2,6,10,14,22}`, even
`N < 60`. These are samples, not proofs; Theorem 1.1 itself is not
re-proved here.

---

## 3. Walker concordance (verbatim, checked against the scan)

From the scanned article (`src/walker.pdf`, text in `src/walker.txt`; FQ 14(2),
pp. 111–116):

- p. 112, Definition: *"A solution `u + v√D` of equation (1) has property Q
  if for `p` a prime, `p|D` implies `p|v`."* — matches the article's reading.
  "Without loss of generality we may assume that `D` is square-free" (p. 112)
  — the article's `K` is squarefree. ✓
- p. 112, eq. (3): `y_i = i x^{i-1} y + C(i,3) y³ D + …` — this is the
  article's (6.5). ✓
- p. 112, Theorem 2.2: "(2) If the fundamental solution has property Q, then
  all positive solutions have property Q. (3) If the fundamental solution does
  not have property Q, then the least solution with property Q, when it
  exists, is the number `(x+y√D)^i`, where the integer `i` is the product of
  the distinct odd primes dividing `D` but not dividing the integer `y`."
  ✓ (`i = R`; case (2) is `R = 1`.)
- p. 112, Lemma 2.4 and p. 113, Theorem 2.5: "… the formula
  `x_{ih} + y_{ih}√D = (x_i+y_i√D)^h` gives all positive solutions with
  property Q of equation (1) with the plus sign for positive integers `h`,
  and gives all such solutions of (1) with the minus sign for odd positive
  integers `h`." ✓ This is precisely `R | N` for the minus-sign family;
  since `R` is odd, `{Rh : h odd} = {n : R | n}`.
- p. 113, Example (3): "The fundamental solution of `X²-5Y² = -1` is `2+√5`.
  The solution `(2+√5)⁵ = 682+305√5` … leads to the powerful numbers 465,124
  and 465,125 or `(682)²` and `(5³)(61²)`." — my computation reproduces this
  exactly: `K = 5`, `R = 5`, `N = 5`, `X = 682 = a₅`, `X²+1 = 5³·61²`
  (`audit/crosscheck_sympy.py` prints `{5: 3, 61: 2}`). The article's family
  is Walker's TYPE I family with the square below.

Conclusion: the citation `[14, equation (3), p. 112; Theorems 2.2(2)–(3) and
2.5, pp. 112–113]` and the reading in §6.3 ("His negative-Pell
parametrisation uses odd powers") are accurate in content, numbering and
pagination. The article does not need Walker: its (6.5)–(6.6) proves the same
statement, and does so without squarefreeness (Lemma 1).

---

## 3A. Prior-art note on the rank half

The `R | N` part of Corollary 1.5 is not new mathematics: Walker's §2
classifies *all* consecutive powerful pairs of TYPE I, i.e. all pairs
`(X², DY²)` with `DY²` powerful and `X² - DY² = ±1`; with `D = K`,
`Y = KV` the pair `(X², X²+1)` is of this type, and Theorem 2.2(3) +
Theorem 2.5 (minus sign, odd `h`) give exactly `N = R·h` with `h` odd, hence
`R | N` and `N, E` odd — in the same order `Z[√D]` that the article uses.
So the honest classification of Corollary 1.5 is:

- **literature support**: the rank/divisibility half (`R | N`, parity of
  `N`, `E`) — Walker 1976, and re-proved self-containedly (and slightly more
  generally, F2) in the article's (6.5)–(6.6);
- **human proof, presumably new**: the normal form and phase `X ≡ 2 (mod 8)`,
  `K ≡ 5 (mod 8)`, the least-unit analysis in the non-maximal order, and the
  same-centre identity `X = F_N(u)`;
- **depends on the main theorem**: `gcd(N, 17·41) = 1`;
- **not claimed new, nor claimed here**: any classification of the remaining
  odd exponents.

(Another swarm member reached the same Walker-based reading of the rank half
independently — board direction d6, finding f3, accepted — and reports 456
soluble odd squarefree `K ≤ 5000` with no mismatch in the least property-Q
index; that is the same corpus size as my §C, computed by different code. I
did not re-run their scripts.)

---

## 4. Findings

**F1 (no gap).** §2 is a complete proof of Corollary 1.5 from its
hypotheses; the only inputs from outside §6 are Theorem 1.1 (main result) and
elementary real-quadratic-order theory. The order `Z[√K]` is handled
correctly (it is non-maximal), the `+1` of `u²+1 = Kv²` is correct (norm
`-1`), and the parity argument is complete.

**F2 (Lemma 1 is stronger than the article states).** Squarefreeness is used
in the article's §6.3 only to write `K/gcd(K,v) = Π_{p|K, p∤v} p` (Walker's
product) and, earlier, to define the `K³V²` normal form. It is *not* needed
for (6.6): Lemma 1 holds for all `K > 1`, the cancellation being
`K | nv ⟺ K₀ | v₀n ⟺ K₀ | n` with `K₀ = K/g`, `v₀ = v/g` and
`gcd(K₀,v₀) = 1`. Machine check: the 8 non-squarefree
`D ≤ 1000` with solvable negative Pell — `D = 50, 125, 250, 325, 338, 425,
845, 925` — all pass (§B(b)).

A related *formal* point, correctly stated: Mathlib's
`Nat.coprime_div_gcd_of_squarefree` has statement `Squarefree m → Coprime (m /
gcd m n) n`, which is **false** without the squarefree hypothesis (`m = 12`,
`n = 18` gives `Coprime 2 18`, false), so the Lean docstring in
`Erdos364/SquareMiddle/PellDivisibilityRank.lean` that attributes the
coprimality to squarefreeness is accurate for that Mathlib step. The
*mathematical* content of (6.6) needs only `gcd(K₀,v₀) = 1`, which holds for
every `K`; the formal path instead uses the stronger statement
`Coprime (K/g) v`, which is true precisely because the article's `K` is
squarefree (that is exactly Mathlib's hypothesis above), so the formal step is
available in the article's setting.

**F3 (scope of (6.7); paper↔Lean correspondence).** (6.7) is false without
"`K` odd": for `K = 2`, `ε = 1+√2`, `2uv = 2`, so `K/gcd(K,2uv) = 1` while
`K/gcd(K,v) = 2`. My scan finds that *all* 192 even squarefree `D ≤ 5000` with
solvable negative Pell fail the identity, and no odd `D` does (§C). Consequence worth recording: `Erdos364.pellRank D = D /
D.gcd (fundamentalY D _)` is defined from the **norm-one** fundamental
solution (`Pell.Solution₁`, `fundamental_pell_equation` proves `X²-DY² = 1`),
so it equals the article's `R` only because in the application the negative
Pell equation is solvable (hence the norm-one fundamental solution is
`ε²`, with `y = 2uv`) *and* `K` is odd (so `gcd(K,2uv) = gcd(K,v)`). The
identification is thus a derived arithmetic fact, not a definitional
identity; the article supplies both hypotheses ((d) and (c) above), and the
Lean rank theorems are about the norm-one sequence
(`kernel_dvd_pellSolutionY_succ_iff` is the `(e^{n+1}).y ≡ (n+1)xⁿy mod D`
congruence, i.e. the norm-one analogue of (6.5)). I did not run the Lean
build (the repository pins `leanprover/lean4:v4.31.0`, this VM has 4.35.0 and
no `.lake` build); the statements above are read from the sources.

**F4 (the "`X-1` square" hypothesis is sharp).** Dropping it, `gcd(N,17·41)=1`
fails inside the same powerful family. Explicit witnesses (exact integers;
`audit/audit_output.txt` §F):

| `K` | `N` | `X mod 8` | `17·41` | digits of `X` | `X-1` square? |
|:--:|:--:|:--:|:--:|:--:|:--:|
| 5 | 85 | 2 | `17 \| N` | 53 | no |
| 5 | 205 | 2 | `41 \| N` | 129 | no |
| 17 | 17 | 4 | `17 \| N` | 16 | no |
| 41 | 41 | 0 | `41 \| N` | 74 | no |

In each row `X = a_N`, `R \| N` and `X²+1 = K³V²` with `V = b_N/K` (checked
exactly). The first two lie in the corollary's phase `X ≡ 2 (mod 8)`, so what
excludes them is precisely the failure of `X = y²+1`, i.e. of the
same-centre identity (6.4). So (1.9) cannot be extended from "`X²+1`
powerful" to "`X²+1` powerful and `X ≡ 2 mod 8`".

**F5 (the `R = 1` branch).** `R = 1` (Walker's Theorem 2.2(2) branch: the
fundamental solution already has property Q, i.e. `K | v`) never occurs among
the 6692 squarefree `D ≤ 60000` with solvable negative Pell (§B(c)). Lemma 1
covers the branch anyway (`R = 1` trivially divides `N`), so this is
immaterial; it does mean that a numerical test of the article's argument never
exercises that branch. No claim of impossibility is intended — I did not prove
the branch empty.

**F6 (search scope; numerical, not a proof of anything about the paper).**
- Complete for `X ≤ 10^{14}` (all odd `y ≤ 10^7`, `X = y²+1`): no `y` has
  `N(y) = y⁴+2y²+2` powerful. Method (§E), two stages, both exact:
  *stage 1* — every prime divisor of `N(y)` for odd `y` is `≡ 1 (mod 4)`
  (if `q | N` then `(y²+1)² ≡ −1`), so only such primes matter; for every
  `q ≡ 1 (mod 4)`, `q ≤ 10^6`, the root classes of `N` mod `q` are computed
  and each `y` with `q | N(y)` but `q² ∤ N(y)` is rejected — such an `N` has a
  prime to the first power and is not powerful. 748263 survivors remain.
  *stage 2* — for a survivor, `rad` (product of the distinct primes `≤ 10^6`
  dividing `N`) is computed by a multiplicative sieve over the same classes,
  and the `10^6`-smooth part `A` and cofactor `C` are computed exactly by
  repeated gcd with `rad` (no factorisation guessed). Then
  `N powerful ⟺ rad² | N and C powerful`, and since every prime of `C`
  exceeds `10^6` while `N < 10^{28}`, a powerful `C` is `1`, `q²`, `q³`,
  `q⁴ = (q²)²` or `(q₁q₂)²` — i.e. `C` is a perfect square or cube
  (`q₁²q₂³ > 10^{30}` and products of three such primes are out of range).
  So the test `rad² | N and (C square or cube)` is necessary and sufficient,
  and it returns **no** candidate. The test is validated against brute-force
  factorisation on 2000 random `N < 10^{28}` of eight shapes, including
  rough powerfuls, `q³`, squares, cubes, and the critical non-powerful shape
  "small part squared, one large prime to the first power" (`selftest` target
  of the script; 0 mismatches).
- Family: for odd squarefree `K ≤ 20000` with solvable negative Pell (1673
  values), all 14 members with `X ≤ 10^60` are listed in §D; none has `X-1` a
  perfect square; 3 have `17 | N`; `(K mod 8, X mod 8)` takes only the pairs
  `(5,2), (5,6), (1,4)`, consistent with (c).
- Hence the corollary's hypothesis set is not known to be non-empty. The
  corollary's mathematical content is conditional and the 17/41 exclusions
  are not numerically falsifiable in these ranges.

---

## 5. How to reproduce

```
cd .ultramath/smw70l62n/m8
python3 audit/cor15_audit.py all      # 4 s; prints the whole audit (sections B-H)
python3 audit/cor15_audit.py selftest # validates the two computational tests
python3 audit/crosscheck_sympy.py     # SymPy 1.14.0 cross-check, 0.5 s
curl -sS -o src/walker.pdf https://fq.math.ca/Scanned/14-2/walker.pdf
pdftotext -layout src/walker.pdf src/walker.txt
```

`audit/audit_output.txt` is the recorded output of the first command. The
script uses only Python integers, `math.isqrt` and continued fractions; its
fundamental-unit routine is validated against brute force for `D ≤ 300`
(exhaustive below the claimed solution in 284 cases) and against SymPy's
`continued_fraction_periodic` for 13 values of `D`, including `D = 17341`
(period length 281).

---

## 6. Classification of the claims

| Step | Kind of proof here | Status |
|:--|:--|:--|
| (6.5)–(6.6) rank lemma | human proof (two independent ones) + exact computation (411 instances) + Walker | verified, strengthened (F2) |
| `η` unit, norm `-1` | human proof (one line) | verified |
| least unit, `N(ε)=-1`, `η=ε^N`, `N` odd | human proof (order theory) | verified |
| (6.3) `v` odd, `u ≡ 2 (mod 4)` | human proof + 146-instance check | verified |
| (6.4) `X = F_N(u)` | human proof + 9-instance check | verified |
| (6.7) norm-one comparison | human proof, needs `K` odd | verified; hypothesis sharp (F3) |
| (1.9) `gcd(N,17·41)=1` | depends on Theorem 1.1 (human 17/41 fixed indices; Lean propagation) | not independently re-proved here; Lemma 5.1 and (2.7) sampled |
| non-vacuity of the hypothesis | none; numerical (F6), complete for `X ≤ 10^14` | open |

Not done, deliberately: no Lean build or re-run of the public receipts; no
attempt to re-prove Theorem 1.1 or Theorem 3.2 (other members' directions);
no claim about `NoSm2RankDefectBlocks`, which stays open.
