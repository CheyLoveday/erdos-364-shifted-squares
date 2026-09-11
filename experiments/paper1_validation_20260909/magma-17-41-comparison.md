# Magma / GP comparison for the fixed degrees 17 and 41

Consumer: Paper I's secondary verification of the two explicit fields and
detectors. This integrates the four completed, user-operated calculator jobs
in [#234](https://github.com/CheyLoveday/erdos-364-lab/issues/234). No Magma
submission was made during integration. The 73/97 controls in #236–239 and
the enlarged-paper checks in #230–233/#235 are separate.

## Archive and input identities

The [complete returned responses](magma-17-41-output.txt) preserve every line
from each START marker through its terminal PASS marker. Source comments:
[degree 17 and hashes](https://github.com/CheyLoveday/erdos-364-lab/issues/234#issuecomment-5603073740),
[degree 41](https://github.com/CheyLoveday/erdos-364-lab/issues/234#issuecomment-5602995918).
The two copies of the degree-17 responses in the issue also agree exactly.

All four report **Magma V2.29-10**, run by Chey on **2026-09-09**. These are
script job IDs and browser-returned responses; no separate server-assigned
run ID, signed receipt or Unix exit status was supplied.

| Job ID | Original input filename | Reported SHA-256 | Returned PASS CPU / wall seconds |
|---|---|---|---|
| E364_17A_v1 | 01_17A.m | `63679e7724e2bd72359b8cb76283af3fd5fa2e29a2efa38b322cbe0e252b0fe1` | 0.000 / 0.010 |
| E364_17B_v1 | 02_17B.m | `6b474f53d5e319bbab24e9e9fb4e51e3afac281373aef7062d1a8ac854b496ea` | 0.050 / 0.040 |
| E364_41A_v1 | 03_41A.m | `628dc86cbb4ab653f192129e4825b279974168b1c7ce47a57cb2a3cb9c1ebb74` | 0.020 / 0.010 |
| E364_41B_v1 | 04_41B.m | `7fa6724f0b174bac45a45bfdd932275418073c8e9afacc1c1e386377a581e0e1` | 0.600 / 0.600 |

The [original-input archive](magma-17-41-inputs.m) contains the recovered
17-A source block: 3732 UTF-8 bytes, independently hashed to the reported
SHA-256. The other three original scripts remain unavailable (reported
sizes: 5954, 3919, 6095 bytes respectively). Bounded searches of relevant
checkouts, attachments and task history recovered no further source bytes;
the original generated-file links are exposed only as opaque placeholders,
and no browser is available to retrieve their attachments. Recovery has
stopped without rerunning or reconstructing scripts.

Hashes identify supplied inputs but cannot recover their contents. Until
those three original files are supplied and their hashes checked, #234
remains open and input-to-response source inspection is incomplete. The
four returned PASS responses and the identity-keyed GP comparison are
archived independently of this precise remaining gap.

## Fixed conventions and GP sources

Research source: `f8ff5ecd0f8885edaa222c9b0da6da5ec134e907`.
The old paper evidence/source pins remain unchanged. The comparison uses
the unmodified [degree-17 GP verifier](../sm2_outer_seventeen/outer17_verify.gp)
and [degree-41 GP verifier](../sm2_four_translate/interpolation/outer41_verify.gp),
with SHA-256 respectively
`81fa43697098dca78c18d9839938e6ac0d2c01e727eb9c543ab4ccec02b127bb` and
`59ac1ef75d1d5e953aec81943a28bdb6b0656721de7947506704ac498c7bb560`.
Both original verifiers passed under PARI/GP 2.17.3 on 2026-09-09.

Use \(D_0=2,D_1=T,D_{n+2}=TD_{n+1}+D_n\),
\(g_p=D_p-2\), \(L=\mathbf Q(\theta)\),
\(u=U_p(\theta)\), \(b=\theta u\), and
\(\delta_4=(4-\theta)/\theta\). All printed polynomial vectors are
constant-first in the same original \(\theta\) basis. In degree 41 the
GP coordinates mean \(U_{41}=a_0+\sum_{k=1}^{40}a_kD_k\), with a literal
constant coefficient; they do not mean \(a_0D_0+\sum_{k=1}^{40}a_kD_k\).
The expanded coefficients printed by Magma agree with this exact convention.

## Obligation comparison

Here **DIRECT_MAGMA_CHECK** records the named check reported by the actual
response and issue handoff; it is subject to the input-recovery limitation
above. **DERIVED_FROM_CHECKED_IDENTITIES** is the stated mathematical
implication. **IMPORTED_INPUT** identifies supplied definitions/data, and
**NOT_CHECKED_BY_MAGMA** preserves an omitted obligation.

| Obligation | Degree 17 | Degree 41 | Magma classification / GP comparison |
|---|---|---|---|
| Exact polynomial, detector and Lucas bridge | degree 17; irreducible mod 67 | degree 41; irreducible mod 163 | A: DIRECT_MAGMA_CHECK; supplied definitions are IMPORTED_INPUT; expanded coefficients agree with GP |
| Polynomial discriminant | \(2^{24}17^{17}\) | \(2^{60}41^{41}\) | A/B: DIRECT_MAGMA_CHECK; equal to GP |
| Maximal power order and field discriminant | index 1; same discriminant | index 1; same discriminant | B: DIRECT_MAGMA_CHECK; equal to GP |
| Signature | \((1,8)\) | \((1,20)\) | A/B: DIRECT_MAGMA_CHECK; equal to GP |
| Resultant and detector norms | \(\operatorname{Res}(g,U)=-1\); norms \((2,-1,-2)\) | same | A: resultant; A/B: norms; DIRECT_MAGMA_CHECK; equal to GP |
| Integral unit inverse | printed integer coefficient vector | printed integer coefficient vector | A: DIRECT_MAGMA_CHECK; locally multiplied by printed U modulo g, yielding 1 exactly |
| Principal-ideal relation \((b)=(\theta)\) | holds | holds | A: DERIVED_FROM_CHECKED_IDENTITIES using b=theta*u and integral u,u inverse; B: reported direct ideal check; GP direct HNF check agrees |
| Unique prime above p | \((17,\theta-2)\) | \((41,\theta-2)\) | B: DIRECT_MAGMA_CHECK; explicit GP ideal-HNF equality verified |
| Row above p | \([17,1,0,0,0,+1]\) | \([41,1,0,0,0,+1]\) | B: DIRECT_MAGMA_CHECK; same ordered descriptor in GP |
| Mod-2 factorisation, three dyadic primes | types \((1,1),2(2,4)\) | types \((1,1),2(2,10)\) | B: DIRECT_MAGMA_CHECK; explicit identity match below |
| Strict Hensel inequalities | margins 1,4,4 | margins 1,4,4 | B: DIRECT_MAGMA_CHECK; exact GP-derived inequalities below |
| Dyadic reference Hilbert product | -1 | -1 | B: DIRECT_MAGMA_CHECK; independent GP local-symbol evaluation agrees |
| Unique real root in (0,4) | signature plus endpoint signs | same | DERIVED_FROM_CHECKED_IDENTITIES; A reports bracket check; no claim of a numerical root-isolation transcript |
| Reference factorisation and primality | \(H=13\cdot1751444197\) | \(H=79\cdot1373\cdot115471\cdot1506563\cdot1344905911\) | A: DIRECT_MAGMA_CHECK; GP certifies primality and factors; local integer product agrees |
| Reference Legendre vector | \((-1,+1)\) | \((+1,-1,-1,-1,+1)\) | A: DIRECT_MAGMA_CHECK; GP and exact modular evaluation agree; products -1 |
| Full odd ideal support of delta4 | GP covers two primes | GP covers five primes | **NOT_CHECKED_BY_MAGMA**, deliberately; see existing GP sources |
| Quantified H1/H2, reciprocity, Lean/Jacobi argument | separate proof layers | separate proof layers | **NOT_CHECKED_BY_MAGMA** |

Reference values retained in full in the response archive are
\(H_{17}=22768774561\), \(U_{17}(4)=532303029\),
\(b_{17}(4)=2129212116\), and
\(H_{41}=25377553679502347277411601\),
\(U_{41}(4)=-43956715453803235217163523\),
\(b_{41}(4)=-175826861815212940868654092\).

## Explicit dyadic prime matching

For each constant-first vector h below, the identifier is the ideal
\(\mathfrak P=(2,h(\theta))\) in the verified maximal power order.
On 2026-09-09, a separate local PARI/GP 2.17.3 check formed
`idealhnf(nf,2,Mod(Polrev(h),g))` and matched it uniquely to
`idealhnf(nf,P)` for `P` in `idealprimedec(nf,2)`. It then recomputed
the six entries \([e,f,v(\theta),v(4-\theta),v(b),(\delta_4,b)_{\mathfrak P}]\).
The GP indices are observed diagnostic positions only; the ideals are the keys.

| p | Magma ID | h, constant first | GP index | Common row | Hensel margin |
|---|---|---|---|---|---|
| 17 | 1 | `[0,1]` | 1 | `[1,1,1,1,1,+1]` | 1 |
| 17 | 2 | `[1,1,0,0,1]` | 3 | `[2,4,0,0,0,-1]` | 4 |
| 17 | 3 | `[1,1,1,1,1]` | 2 | `[2,4,0,0,0,+1]` | 4 |
| 41 | 1 | `[0,1]` | 1 | `[1,1,1,1,1,+1]` | 1 |
| 41 | 2 | `[1,1,0,1,1,0,0,1,1,0,1]` | 2 | `[2,10,0,0,0,-1]` | 4 |
| 41 | 3 | `[1,1,0,0,1,0,0,0,0,1,1]` | 3 | `[2,10,0,0,0,+1]` | 4 |

The match is bijective in both degrees, with \(\sum ef=p\) and
\(v_{\mathfrak P}(2)=e\). The strict margin is
\((4e-v(4-\theta))-2e=2e-v(4-\theta)\): thus \(3>2\)
at the degree-one prime and \(8>4\) at the other two. The matched local
symbols multiply to -1 in each degree. Matching by row position would
exchange the two repeated-type primes at degree 17.

The independent check also verified
`idealhnf(nf,p,theta-2)==idealhnf(nf,idealprimedec(nf,p)[1])`
and the displayed p-prime rows. Its exit status was zero and its terminal
marker was `MAGMA_GP_EXPLICIT_IDEAL_COMPARISON_PASS pari=2.17.3 degrees=17,41 dyadic_rows=6`.
This was a separate agent using PARI/GP, not independent human review.

## Scope for writing

Use this as secondary cross-system verification of the specified explicit
polynomial, field, detector, maximal-order and dyadic local data. The full
odd reference ideal support is covered by GP alone in this comparison.
The [fixed-field obligation table](../../papers/shifted-square-17-41/fixed-field-obligation-table.md),
[human Hilbert proof](../../papers/shifted-square-17-41/hilbert-obstruction-lamport.md)
and [Hilbert/Jacobi crosswalk](../../papers/shifted-square-17-41/hilbert-jacobi-crosswalk.md)
retain their separate roles. The four jobs do not independently prove a
quantified theorem, formalise Hilbert symbols in Lean, validate newer
multiplier/CF/affine results, or promote a result into a paper or canonical repository.
