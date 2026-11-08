# Statement-strength audit of Paper I (shifted squares at indices divisible by 17 or 41)

Member m5, swarm `smw70l62n`. Repository commit `c663b4e1e65c99846d41270a288f154559cc9fd6`.
Direction: does the maintained Lean development prove the paper's claims *as the
paper states them* (integer square roots, exact endpoints, quantifier order,
the quadratic-ring power of Corollary 1.4), and where is it silent?

## Verdict

* **No statement mismatch found** for Theorems 1.1, 1.2, 1.3 and Corollary 1.4,
  and none for the hard-phase conclusion of Theorem 4.2. Each is now
  *machine-checked at the paper's own strength*, derived from the maintained
  declarations with no extra hypothesis: `PaperStatementBridge.lean`.
* Three human-only items have **no formal counterpart at all** (Proposition 2.1's
  2-adic sufficiency, the Hilbert chain of §3–§4, Corollary 1.5). That is the
  honest boundary; "not formalised" is not "wrong", and I found no error in
  them by reading (see §3).
* Two declarations **do not elaborate as written** against the toolchain
  installed in this VM (Lean 4.35 / Mathlib `a3a10db`) because the repository
  pins Lean 4.31 / Mathlib `fabf563a`. Both adaptations are syntactic; neither
  changes a statement, a hypothesis, or a proof step (§2).

## 1. What is now machine-checked at paper strength

`PaperStatementBridge.lean` (compiles; axiom footprint printed below) proves:

| Paper claim | Paper's quantifier | Lean bridge theorem |
|---|---|---|
| (1.1) recurrence, `F_0=1,F_1=A` | `A ∈ Z≥0` | `paper_F_zero`, `paper_F_one`, `paper_F_step` |
| Thm 1.1 (1.3) | `A≡2(4)`, `N>0`, `17∣N ∨ 41∣N`, **`y ∈ ℤ`** | `theorem_1_1` |
| Thm 1.2 (1.4) | `A≡2(4)`, **`y ∈ ℤ`**, both primes | `theorem_1_2_seventeen`, `theorem_1_2_fortyOne` |
| Thm 4.2 (4.13) | `A≡2(8)`, **`y ∈ ℤ`**, both primes | `theorem_4_2_seventeen`, `theorem_4_2_fortyOne` |
| Thm 1.3 (1.5) | `A≡2(4)`, `N>0` even | `theorem_1_3` |
| Thm 1.3 consequence | same | `even_index_exclusion` |
| Cor 1.4 | `u²+1=Kv²`, `u≡2(4)`, `N>0`, `2∣N ∨ 17∣N ∨ 41∣N`, **`y ∈ ℤ`**, `X_N` = coefficient of 1 in `(u+v√K)^N ∈ Z[√K]` | `corollary_1_4` |
| §1.1 witness | `A=2, N=1` **is** a solution | `witness_index_one` |
| §5.2 witness | even inner index breaks composition (`161 ≠ 163`) | `witness_even_inner_composition` |
| §7.3 endpoint | `A=2` inside the degree-41 statement | `endpoint_fortyOne_included` |
| §2.4 / §7.2 | `F_41(2)-1 ≡ 20 (mod 23)`, `20` a nonresidue | `endpoint_fortyOne_residue`, `endpoint_twenty_is_nonresidue`, `endpoint_fortyOne_mod23_obstruction` |

Three points of substance behind that table:

1. **`y ∈ ℤ` versus `y : ℕ`.** The maintained theorems quantify a natural square
   root. `nat_of_int_square_add_one` and `int_square_add_one_to_nat` carry the
   transfer (`y` and `−y` have the same square), so the integer form is not an
   additional assumption. This is the one place where the paper and the formal
   statement genuinely differ, and it is now closed inside Lean rather than by
   assertion in a crosswalk table.
2. **Corollary 1.4 is about a real ring power.** `((⟨u,v⟩ : ℤ√(K:ℤ))^N).re` is
   the coefficient of `1` in `(u+v√K)^N` for Mathlib's `Zsqrtd`, whose
   multiplication is exactly `(a+b√K)(c+e√K) = ac + Kbe + (ae+bc)√K`. The
   bridge hypothesis list is `u²+1 = Kv²`, `u%4 = 2`, `N>0`, `2∣N ∨ 17∣N ∨ 41∣N`
   and nothing else: **no squarefreeness of `K`, no fundamentality, no
   coprimality** — matching the paper's explicit disclaimer.
3. **Axiom footprint.** Every bridge theorem depends only on
   `propext, Classical.choice, Quot.sound`; `endpoint_fortyOne_residue` depends
   on none. Nothing in the bridge uses `sorryAx`. The broader sweep is in §1.1.
### 1.1 Axiom footprint of every declaration the crosswalk attributes to Lean

`AxiomFootprint.lean` prints the footprint of all 19 declarations that the
crosswalk attaches to formalised paper results (fixed 17/41 at mod 8 and mod 4,
the mod-8 residue lemmas, composition, the odd-index and even-index propagation,
the exact valuation, the Pell-unit corollaries, the power-coordinate lemma,
`noSm2OuterSeventeenBlocks`, the two selected-41 slices and `pellRank_dvd_kernel`).
All 19 depend on exactly `[propext, Classical.choice, Quot.sound]`; none on
`sorryAx` or any custom axiom. A source sweep of `Erdos364/` finds **no**
`sorry`, `admit`, `axiom`, `constant`, `@[implemented_by]`, `@[extern]`,
`unsafe def` or `native_decide`. The tree does use `set_option maxRecDepth`
(in 4 files, values 4096–20000) and `maxHeartbeats` for performance; the
adaptation in §2 is the same kind of knob, not a soundness escape.

## 2. Two declarations need toolchain adaptation (not mathematical gaps)

Built out of tree (`build.py`, sources copied to `src/`, oleans in `leanbuild/`;
the repository working tree is untouched). All 60 modules of the closure of
`Erdos364.DicksonLucas.ShiftedSquarePropagation` elaborate; `~3 min` at `-j3`,
`Sm2LowerSquareOuterFortyOne.lean` alone `~110 s`.

* `Erdos364/SquareMiddle/LeafCompiler.lean`: `deriving … Fintype` for
  `SquareMiddleLeaf` fails under Mathlib `a3a10db`
  (`Membership.mem`/`SetLike.instMembership` mismatch in the generated
  instance). Replaced by an explicit `Fintype` instance with the same `elems`
  and the same cardinality proof. No statement changes.
* `Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean`: the kernel raises
  `deep recursion detected` checking the `norm_num : Nat.Prime 2731930457`
  term. `set_option maxRecDepth 20000` fixes it. No statement or proof step
  changes.

Consequence for assurance wording: "the sources compile unchanged in this
environment" is **false as stated**; they compile after two local,
semantics-preserving adaptations, or unchanged under the pinned toolchain.
Both patches are marked `LOCAL-AUDIT PATCH (m5)` in `src/`.

## 3. Independent exact-arithmetic statement audit

`audit_statements.py` re-derives every finite input from the paper's own
definitions in exact integer arithmetic written from scratch (own recurrence,
own Jacobi/Legendre symbol, own resultant by Bareiss elimination, deterministic
Miller–Rabin; no project script, no `sympy`). Run: **2 078 952 assertions,
0 failures, 17.9 s**. Coverage (all at the paper's stated quantifiers):

* Every numerical value printed in the paper ((1.1) at `A=2`, the valuations
  `3,5,7`, `161/163`, `F_51(6) = F_17(882)`, `882 = F_3(6)`, the `mod 8` residue
  of `F_51(6)-1`), recomputed from (1.1).
* (2.2)–(2.8) identities and residue tables.
* Theorem 1.3 / (1.5) exact valuation, `A ≡ 2 (4)` up to 998, `N ≤ 598`.
* Lemma 5.1 composition (odd inner index) plus the even-index failure.
* Theorem 1.1: `A ≡ 2 (4)` up to 198, `N = 17m` and `41m`, `m ≤ 20`.
* Proposition 2.1: the residue criterion for `A < 2000`, odd `n < 140`, plus an
  explicit Hensel lift of a square root mod `2^64` in the two square cases.
* Corollary 1.4: `re((u+v√K)^N) = F_N(u)` for every `K < 5000, v ≤ 60` with
  `u²+1 = Kv², u ≡ 2 (4)`, `N ∈ {1,…,6,17,18,41}`, and the norm identity —
  35 triples, **6 of them with `K` not squarefree** (`K = 325, 925, 1325,
  1445 = 5·17², 4325, 4901`), which exercises the paper's explicit
  "no squarefreeness of `K`" disclaimer.
* Tables 3/4/A1 and Appendix A.2: `monic degree p`, `θ`-norm 2, `Res(g_p,U_p) = −1`,
  discriminant `2^{3(p−1)/2}p^p`, `g_p(4)` as printed in (A.1), `H_p`
  factorisation into distinct primes, `H_p ≡ 1 (8)`, all reference Legendre
  characters of Table A1, `J(U_p(4),H_p) = −1`, `g_p ≡ Tφ²ψ² (mod 2)` with
  remainder `1` of the correction mod `φψ`, `φ,ψ` distinct irreducible of
  degree `(p−1)/4`, `g_p ≡ (T−2)^p (mod p)` and the (A.5) residues nonzero.
* **Proposition 7.1 at unformulated strength**: `J(U_p(2A), F_p(A)−1) = −1`
  together with `gcd(U_p(2A), F_p(A)−1) = 1` for **62 500 values of `A` per
  prime** (`A < 500 000`, `A ≡ 2 mod 8`), plus the two reciprocity steps of the
  proof of (7.4) (`J(m,Q) = 1`, `Q ≡ −1 mod m`, `J(xU_p(x),Q) = J(U_p(x),Q)`),
  and `F_p(A)−1` non-square at each of those `A`.
* Endpoint: `F_41(2)−1 ≡ 20 (mod 23)`, `20` nonresidue, `A=2` non-square;
  `13 ‖ H_17` and `U_17(4)` a nonresidue mod 13 (§7.2).

**Scope.** This is a falsification test over a large finite range, not a proof:
it raises confidence in the human statements, it does not replace them. It found
no failure.

## 4. Places I probed for a genuine gap, and why they hold

* **Support parity at ramified primes (§3.3).** For `ℓ | g(x)`, the ring
  isomorphism `O_L/(x−θ) ≅ Z/g(x)` gives *exactly one* prime `P | ℓ` above `ℓ`
  containing `x−θ`, with residue field `F_ℓ`. So `v_ℓ(Nδ_x) = v_P(δ_x)`
  regardless of ramification, and `θ` being a unit at odd primes follows from
  `N(θ)=2`. The argument does not need `ℓ` unramified — the paper's "the
  argument also applies at ramified primes" is correct.
* **Strict Hensel (§3.5).** `4e − d > 2e` is exactly `v(t) > 2v(2)` for
  `t = (x−4)/(4−θ)`; equality would fail (`5 = 1+4` in `Q_2`), so the strictness
  is necessary and the paper's threshold is sharp. Both table rows satisfy it
  (`3 > 2`, `8 > 4`).
* **Coprimality of (7.1).** If `ℓ | Q` and `ℓ | xU_p(x)`, then
  `b_p ≡ xU_p(x) ≡ 0 (mod P)`, contradicting `b_p` a unit at odd primes. So the
  numerator really is coprime to the denominator, and the Jacobi symbol is
  `±1`, never `0` — verified numerically on 125 000 pairs.
* **`A = 2` for `p = 41`.** The published chain excludes `8j+10`; the endpoint
  is separate. It is *inside* the Lean statement (`A % 8 = 2`), and the
  modulo-23 witness is machine-checked here.
* **Composition guard (§5.2).** `F_{mn} = F_m ∘ F_n` needs `n` odd; the parity of
  the inner iterate is what keeps `B ≡ 2 (mod 4)`, and Theorem 1.1's odd branch
  depends on exactly that. The formal composition lemma carries the same guard.

## 5. What this audit does not establish

* Hilbert reciprocity, Proposition 3.1 and Theorem 3.2 are not formalised; I
  read them and re-checked their finite inputs, not their logic in Lean.
* Proposition 2.1's sufficiency direction ("odd 2-adic unit ≡ 1 mod 8 is a
  square") is human; only its residue half and explicit Hensel lifts were tested.
* Corollary 1.5 (powerful decomposition, least unit, `R | N`, `gcd(N,41·17)=1`)
  is human-only; another member audits it.
* Signature `(1,8)`, `(1,20)` and the individual dyadic Hilbert signs of Table 4
  were not recomputed here (the paper needs only their product and derives it
  from Table A1, which I did verify).
* No claim is made that the *whole* development is sorry-free; only the
  declarations used by the bridge have the printed axiom footprint.

## 6. Reproduction

```sh
cd .ultramath/smw70l62n/m5
python3 build.py --jobs 3          # ERDOS_SRC defaults to the repo; use ERDOS_SRC=$PWD/src for the patched copy
# bridge (after the build):
LEAN_PATH="$PWD/leanbuild:$LEAN_PATH" lean -R . -o leanbuild/PaperStatementBridge.olean PaperStatementBridge.lean
python3 audit_statements.py        # 2078952 assertions, 0 failures
```

Files: `PaperStatementBridge.lean` (machine-checked bridge), `PrintStatements.lean`
/ `printed_statements.txt` (the printed types of every bridge theorem),
`AxiomFootprint.lean` / `axiom_footprint.txt` (footprints of the 19
crosswalk-attributed declarations), `audit_statements.py` (exact-arithmetic
statement tests), `build.py` (out-of-tree build), `src/` (patched source copy),
`run_log.txt` (captured output).
