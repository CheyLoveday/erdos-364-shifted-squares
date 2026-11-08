# Independent audit of the shifted-square 17/41 finite certificates (direction d7)

Repository commit `c663b4e1e65c99846d41270a288f154559cc9fd6`.
Sources audited: `papers/shifted-square-17-41/manuscript/revision/paper_1_github.md`
(§2–§7, Appendices A, C), `papers/shifted-square-17-41/hilbert-jacobi-crosswalk.md`,
`experiments/sm2_outer_seventeen/outer17_verify.gp`,
`experiments/sm2_four_translate/interpolation/outer41_verify.gp`.

**Method.** Every finite datum the human proof uses was recomputed from scratch with
my own exact code (`cert/exact.py`: integer polynomial arithmetic, GF(p) factoring,
Jacobi/Kronecker symbols, resultant and discriminant by modular reduction + CRT,
Dedekind's index criterion, 2-adic Newton/Hensel). No number-field routine was used
in the critical path; PARI is *not* in the loop. Everything is one command:

```
cd .ultramath/smw70l62n/m4/cert && python3 verify_independent.py      # ~1.4 s, 51 checks
```

Last line on success: `FIXED_CERTIFICATE_INDEPENDENT_OK`.

## 1. Verdict

No mathematical error, sign error or false statement was found in any of the paper
statements I tested. Every finite certificate input reproduces exactly, by a different implementation,
and the two stress frontiers (identity and conclusion) hold far beyond the published
data. Four steps that the written argument states tersely (in passing, or by citing a
standard theorem) are re-derived below in full (§3); they are independent
rederivations, not claims that the paper is missing them.
One practical defect exists in a shipped artifact (§4.1): the reconstruction formula
in a certificate comment gives a non-unit when followed literally.

## 2. Independent reconstruction — every claim reproduced

`x = 2A`, `Q_0(A) = g_p(x)/2 = F_p(A) - 1`, `F_0=1, F_1=A, F_{n+2}=2AF_{n+1}+F_n`,
`D_0=2, D_1=T, D_{n+2}=T D_{n+1}+D_n`, `g_p = D_p-2`.

| Claim in the paper | Where | Verdict |
|---|---|---|
| `g_p = D_p-2`; `g_p(2A) = 2(F_p(A)-1)` | (2.1),(2.2), GP L44–69 | exact, verified symbolically |
| `Q_0(A)` integral, `Q_0(0) = -1` | crosswalk (1) | exact |
| `disc(g_17) = 2^24 17^17`, `disc(g_41) = 2^60 41^41` | Table 3 | exact (CRT over 62/261 primes, Landau–Mignotte bound) |
| `g_p` irreducible over `Q` (witness 67 / 163) | Table 3 | exact (own GF(p) factorisation) |
| `[O_{L_p}:Z[θ_p]] = 1` | Table 3, A.2 | exact (own Dedekind criterion at `q=2` and `q=p`; `q∤disc` needs no check) |
| `(2) = P_1P_2^2P_3^2`, `(e,f) = (1,1),(2,h),(2,h)`, `h=(p-1)/4` | Table 4, A.2 | exact: `g_p ≡ T φ_p^2 ψ_p^2 (mod 2)` |
| `(p)` totally ramified, `(e,f)=(p,1)` | Table 4 | exact: `g_p ≡ (T-2)^p (mod p)` |
| A.2 finite inputs: `φ_p,ψ_p` irreducible/distinct, correction `≡1 mod φψ`, `(A.5)` residues 12 / 26 | A.2 | exact |
| `Res(g_p,U_p) = -1`, `N(θ)=2`, `N(u)=-1`, `N(b)=-2` | (4.5),(4.9),(4.11) | exact (CRT, 47/253 primes) |
| `H_17 = 13·1751444197`, `H_41 = 79·1373·115471·1506563·1344905911`, all prime, squarefree | (4.6),(4.10) | exact |
| `U_17(4)=532303029`, `U_41(4)=-43956715453803235217163523`, `J(U_p(4),H_p)=-1` | (4.6),(4.10) | exact |
| Table A1 odd characters `(4U_p(4)/ℓ)` | A.1 | exact, all 7 signs match |
| signature `(1,8)`, `(1,20)`; `θ_R ∈ (0,2)` | (4.1) | Descartes: 1 positive, 0 negative roots |
| Table 1 / criterion (2.9) | §2.4 | exact, and proved in §3.3 |
| Lemma 5.1 `F_{mn}(A)=F_m(F_n(A))` (n odd); `F_m(A)≡2 (4)` | §5.2,(2.7) | verified on a grid |
| `F_41(2)-1 ≡ 20 (mod 23)`, 20 non-residue | §2.4 | exact |
| Appendix C listing extracted verbatim and executed | App. C | prints `FIXED_FIELDS_OK` |

The Appendix A.2 maximality certificate is *independent of* my Dedekind computation
and agrees with it: two different implementations of the same criterion, both
certifying index one, hence `disc(Z[θ]) = disc(O_L)`.

## 3. Four steps re-derived here in full

These are independent rederivations. The paper states each of them, tersely or by
citation; I spell them out and check every hypothesis, and I record where an
intermediate assertion would be insufficient on its own.

### 3.1 Positivity, oddness and coprimality in Proposition 7.1

Prop. 7.1 asserts: "The denominator is positive and odd, and is coprime to the numerator."

* **Positivity.** `g_p` has only the constant term `-2` negative, so `g_p'(x) > 0` for
  `x > 0`; with `g_p(0) = -2 < 0` and `g_p(4) > 0` there is a unique positive root and
  `g_p(x) > 0` for `x ≥ 4`. Hence `Q_0(A) > 0` for `A ≥ 2`.
* **Oddness.** `Q_0(A) ≡ A - 1 (mod 8)` (§3.3), so `Q_0(A)` is odd for `A ≡ 2 (mod 4)`.
* **Coprimality.** §7.1 states this via "`b_p` is an odd-place unit, so every residue
  occurring on the right of (3) is nonzero", and the crosswalk says the same. Here is the
  full derivation, because one intermediate step needs care: `Res(g_p,U_p) = -1` alone
  does **not** imply `gcd(U_p(2A), Q_0(A)) = 1` — a resultant `±1` forbids a common
  *polynomial* root, not a common prime divisor of specialisations. The claim is
  nevertheless true: if an odd prime `ℓ` divided both, then `ℓ | Q_0 = N(δ_x)`,
  so some `P | ℓ` has `v_P(δ_x) > 0`, hence `θ ≡ x (mod P)`; then
  `U_p(θ) ≡ U_p(x) ≡ 0 (mod P)`, so `P | (U_p(θ))` and `v_P(b_p) ≥ 1`, giving
  `ℓ | N(b_p) = -2` — contradiction. Only `N(θ)=2`, `N(u_p)=-1` and `u_p(θ) ∈ O_{L_p}`
  are used, i.e. exactly (4.11), which is where the paper's "odd-place unit" remark
  comes from. A second ingredient, `ℓ ∤ 2A`, follows from `Q_0(A) ≡ -1 (mod A)`.

### 3.2 The supporting prime at an odd `ℓ | Q_0(A)` and `v_P(δ_x) = v_ℓ(Q)`

The paper: "equation (3.5) gives a unique supporting degree-one prime `P` … the norm
calculation, now without a square assumption, gives `v_P(δ_x) = v_ℓ(Q)`." Two facts are
being used, and both are true (the crosswalk's Lemma H2.2 also names the ramified
branch explicitly):

1. Since `Z[θ] = O_L`, primes above `ℓ` correspond to irreducible factors of
   `g_p mod ℓ`. The only prime that can contain `x - θ` is the one attached to the
   linear factor `T - x`, which has `f = 1`; if `x` is a repeated root mod `ℓ` that
   prime is ramified but still unique with `f = 1`.
2. `N(x-θ) = g_p(x)` forces `v_ℓ(Q_0) = Σ_{P|ℓ} f_P v_P(x-θ) = v_P(x-θ)`.
   Hence `v_P(δ_x) = v_P(x-θ) = v_ℓ(Q_0)` exactly, in the unramified **and** the
   ramified case. The ramified case is not exotic: `x` is a `p`-fold root of
   `g_p mod p`, and `p | Q_0(A) ⟺ A ≡ 1 (mod p)` (§5.2).

### 3.3 The 2-adic square criterion (Table 1, (2.9)) is a congruence, not Hensel

**Lemma.** For `A` even and `n` odd, `F_n(A) ≡ nA (mod 8)`; hence
`F_n(A) - 1 ≡ nA - 1 (mod 8)`.

*Proof.* `F_n` for odd `n` has only odd powers of `A`; `A^3 ≡ 0 (mod 8)` for even `A`;
the coefficient of `A` in `F_n` is `n` (induction: `[A]F_{n+2} = 2·[1]F_{n+1} + [A]F_n = 2+n`
because odd-index terms have constant term `0` and even-index terms `1`). `∎`

With "an odd 2-adic unit is a square iff `≡ 1 (mod 8)`" this gives Table 1 exactly:
`(A,n) ≡ (2,1) ↦ 1` square, `(2,3) ↦ 5`, `(6,1) ↦ 5`, `(6,3) ↦ 1` square. Hence
(a) the `A ≡ 6 (mod 8)` half of Theorem 1.2 is excluded 2-adically for every
`n ≡ 1 (mod 4)`, in particular for `n = 17, 41`. The hypothesis `n ≡ 1 (mod 4)` cannot
be dropped: for `A ≡ 6 (mod 8)` and `n ≡ 3 (mod 4)` the value is `≡ 1 (mod 8)` and the
congruence says nothing — e.g. `A = 6`, `n = 3`: `F_3(6) - 1 = 881 ≡ 1 (mod 8)`.
(b) the "hard phase" `A ≡ 2 (mod 8)` is 2-adically invisible for every `n ≡ 1 (mod 4)`;
(c) no Hensel argument beyond the standard unit criterion is needed. Verified as a polynomial identity mod 8: `Q_0(A) - (A-1) ≡ 0 (mod 8)` for both `p`
(the coefficient of `A` in `Q_0` is `p ≡ 1 mod 8`).

### 3.4 Table 4's valuation columns are forced, and (3.9) is immediate

`v_P(θ_p) = (1,0,0)` follows from `(θ_p) = P_1` (a prime ideal of norm `2`, because
`N(θ)=2` and `θ ∈ P_1=(2,θ)`). Then at the two ramified primes `v_P(4-θ) = min(2e,0) = 0`,
and at `P_1`, `v(4-θ) ≥ 1` while `v(4-θ) ≥ 2` would force `v(θ) ≥ 2`. So `(t,d,s)` in
Table 4 is *determined* by `N(θ)=2` and `(b)=(θ)`; it is not independent data.
The strict-Hensel hypothesis of (3.9) then reads `4e-d > 2e`, i.e. `3>2`, `8>4`,
`8>4` — automatically satisfied, so (3.10) (dyadic stability) is rigorous.

## 4. Audit findings

### 4.1 Defect (documentation, shipped artifact): the degree-41 reconstruction comment

`outer41_verify.gp` L33–34 says it reconstructs `u_41 = Σ_{n=0}^{40} a_n D_n`. The code
does not: it computes `a_1·1 + Σ_{n=1}^{40} a_n D_n`, and `D_0 = 2`, so the constant
term differs. Implementing the comment literally gives

* `Res(g_41, u) = -9164150124066553563165928` (not `-1`), so `u(θ)` is **not** a unit;
* `u(4) = -43956715453803235217163524`, one more than the certificate's `-…523`.

The paper is correct and explicit: (4.7)–(4.8) say "`c_0` multiplies `1`, not `D_0 = 2`",
and the Appendix C listing carries the same comment (`# c[0] multiplies 1, not D_0`).
`theorem-formal-crosswalk.md` / the GP header should carry that sentence too. Any
re-implementation from the comment alone fails the unit test, so this is a
reproducibility trap even though the mathematics is unaffected.

### 4.2 The finite certificate at `x = 4` does not witness the ramified branch

For both fields `x = 4` is a *simple* root of `g_p mod ℓ` at every support prime
`(g_p'(4) ≢ 0)`, and all support primes are unramified and split. But in the phase
`A ≡ 2 (mod 8)` the branch `A ≡ 1 (mod p)` occurs with density `1/p`
(147 values below `20000` for `p = 17`, 61 for `p = 41`; in my larger run, 1471 of
25000 for `p=17`), and there `p` is ramified and `x` is a `p`-fold root mod `p`, so
(3.5)'s "simple factor" language then needs §3.2's argument, which the crosswalk's
Lemma H2.2 supplies ("or its unique ramified-prime branch") and which the paper's §3.3
handles explicitly. The maintained integer route
covers these values (verified: `J(U_p(2A),Q_0(A)) = -1` at all of them, and
`v_p(Q_0)=1` in every case tested to `A < 400000`). So the branch is handled — by
the uniform steps; the point here is only that the finite certificate at `x = 4`, taken
by itself, does not witness it.

### 4.3 The only data not independently recomputed

The three *individual* dyadic Hilbert signs. I did recompute one of them exactly:
the `(e,f)=(1,1)` prime `P_1` has completion `Q_2`, so its symbol is the rational
`(u,2)_2 (u,w)_2` with `u=(4-r)/r`, `w=rU_p(r)` for the 2-adic root `r ≡ 2 (mod 4)`
of `g_p`; both `p` give `+1`, matching Table 4. The other two (ramified, `e=2`,
`f=4`) would need a local Hilbert routine over a degree-8 `Q_2`-field. This is not a
gap in the paper, which states explicitly (§4.5, A.1) that only the *product* is used
and derives it from Table A1 plus Hilbert reciprocity; I verified every ingredient of
that derivation: odd product `-1` (Table A1, exact), real `+1`, complex `+1`, so
dyadic product `-1`; then (3.10)/§3.4 propagates it to the whole phase.

## 5. Stress tests (numerical experiment — not a proof)

| Test | Range | Result |
|---|---|---|
| `J(U_p(2A), Q_0(A)) = -1` with `gcd = 1`, `Q_0>0` odd | 125 000 values, `p=17`, `A ≤ 10^6` | 0 failures |
| same, `p=41` | 37 500 values, `A ≤ 3·10^5` | 0 failures |
| direct conclusion `F_N(A) - 1` not a square | 1 400 pairs, `A ≡ 2 (4)`, `N ∈ {17m, 41m : m odd ≤ 11} ∪ {34,68,102,136}` | 0 squares |
| Theorem 1.3, `v_2(F_N(A)-1) = 2v_2(N)+1` | 2 900 pairs | 0 failures |
| `gcd(Q_0(A), g_p'(2A)) > 1` only at the ramified prime | 25 000 + 7 500 values | 0 non-ramified cases |
| `v_p(Q_0(A)) = 1` whenever `A ≡ 1 (mod p)` | `A < 4·10^5` | 0 exceptions |
| `Q_0(A) ≡ A-1 (mod 8)` | `A ≤ 2000` | 0 exceptions |

These are consistency tests of statements already proved; they cannot establish the
quantified theorems and are reported separately from them.

## 6. Classification of the evidence

* **Formal (Lean, maintained `Erdos364/SquareMiddle/`)**: not re-run here; the
  integer-Jacobi chain is out of scope for this direction, and no Lean file was modified.
* **Human proof**: §3 above re-derives four steps in full; `theorem12_rederivation.md`
  assembles them with the finite certificates into a complete proof of Theorem 1.2.
* **Finite certificate**: all of §2, recomputed by an independent implementation.
* **Numerical experiment**: §5 only.

## 7. Reproduction

```
cd .ultramath/smw70l62n/m4/cert
python3 verify_independent.py         # 51 checks, prints FIXED_CERTIFICATE_INDEPENDENT_OK
python3 appendixC.py                  # extracted Appendix C listing -> FIXED_FIELDS_OK
python3 step12_extended.py            # the large-range stress tests (~5 s)
```
`cert/step*.py` are the per-stage drivers that produced the numbers quoted here;
`cert/exact.py` is the self-contained arithmetic kit.
