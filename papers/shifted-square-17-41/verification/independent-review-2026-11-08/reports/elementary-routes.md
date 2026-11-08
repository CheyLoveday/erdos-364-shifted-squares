# Report — swarm `smw70l62n`, member m7, direction d5

**Direction.** Independent elementary/constructive investigation of the fixed-index
exclusions at $p=17$ and $p=41$: what a congruence proof can and cannot do, plus
independent re-verification of the manuscript's printed data.

**Bottom line (revised after review).** I proved that **no fixed-modulus covering
congruence certificate** can exist for the hard phase, and located exactly why the
other standard elementary mechanisms yield no contradiction. I obtained no
alternative proof of Theorem 4.2, and I do not claim that none exists: the
manuscript's own Jacobi argument is elementary arithmetic with $A$-dependent data, and
global arguments are untouched by my results. I found **no gap, error or
counterexample**; the manuscript's numbers reproduce exactly.

Notation: $Q_p(A)=F_p(A)-1=g_p(2A)/2$, $p\in\{17,41\}$, $A\equiv2\pmod 8$ the hard
phase. Two witness notions, kept apart throughout (see `theorem_no_finite_modulus.md`
§0.1): a **(W1) witness** is a prime $\ell$ at which $Q_p(A)$ is not a square in
$\mathbb Q_\ell$ (divisibility not required); a **(W2) witness** is a prime divisor of
$Q_p(A)$ of odd valuation with non-residue detector character, the shape produced by
the manuscript's Proposition 7.1.

---

## R1. No fixed-modulus covering certificate [proof + one finite computation]

**Theorem** (`theorem_no_finite_modulus.md`). For $p\in\{17,41\}$, every finite set
$S$ of odd primes, and all integers $\alpha\ge1$, $e_\ell\ge1$, there are infinitely
many $A\equiv2\pmod 8$ with
$Q_p(A)\equiv t^2 \pmod{2^{\alpha}\prod_{\ell\in S}\ell^{e_\ell}}$; in particular
$Q_p(A)$ is a square in $\mathbb Q_2$ and in $\mathbb Q_\ell$ for every $\ell\in S$.

Ingredients: (i) an elementary proof of the manuscript's (2.8)/Proposition 2.1
($Q_p(A)\equiv1\pmod 8$, so $Q_p(A)$ is a 2-adic square) — Lemma 1; (ii) for every
odd prime $\ell$ some residue $c$ makes $Q_p(c)$ a non-zero square mod $\ell$ —
verified for all $668$ odd primes $\le5000$ and proved for $\ell>p^2$ by the Weil
bound on quadratic character sums — Lemma 2; (iii) CRT.

**Corollary.** No modulus $M$ can serve as a covering certificate (test the classes
$a\bmod M$ and reject when some $\ell\mid M$ is a (W1) witness): for the finite prime
set $S$ of any $M$ the theorem gives infinitely many admissible $A$ passing all those
tests. Equivalently, if a proof produces (W1) witnesses, they cannot be confined to a
fixed finite set of primes.

**Scope.** This is a statement about fixed-modulus tests only. It does not touch the
manuscript's route (fixed numerator $U_p(2A)$, $A$-dependent denominator), which is
elementary arithmetic in the ordinary sense; nor global arguments (heights, integral
points on $y^2=Q_p(A)$, linear forms in logarithms), which need no local witness; nor
(W2) witnesses, which the manuscript supplies uniformly.

## R2. New exact elementary identities [proof]

Write $D_p(x)=x\,V_p(x^2)$, so $F_p(A)=A\,V_p(4A^2)$.

* $F_p(A)\equiv A\pmod{A^2+1}$ for $p\equiv1\pmod4$ (and $\equiv-A$ for
  $p\equiv3\pmod4$), because $V_p(-4)=F_p(i)/i=i^{p-1}$. Hence a solution
  $F_p(A)=y^2+1$ forces $y^2\equiv A-1$ and $y^4\equiv-2A\pmod{A^2+1}$; for $A$ even
  every prime $\ell\mid A^2+1$ satisfies $\ell\equiv1\pmod4$ and $-2A$ must be a
  **fourth power** modulo $\ell^{v_\ell(A^2+1)}$.
* $D_p(T)\equiv T^p\pmod p$ for every prime $p$; hence $g_p(T)\equiv(T-2)^p\pmod p$
  — the manuscript's (A.4) for *every* odd $p$ — and $F_p(A)-1\equiv(A-1)^p\pmod p$,
  so $A-1$ is a quadratic residue mod $p$ (or divisible by $p$).
* $w_p(A)\equiv p\pmod{A^2+1}$, where $\alpha^p=F_p+w_p\sqrt{A^2+1}$; hence
  $A^2+1\mid w_p$ iff $A^2+1=p$ (which does occur, e.g. $(p,A)=(5,2),(37,6),(101,10)$,
  but never for $p\in\{17,41\}$ with $A\equiv2\pmod8$).
* $F_p(A)=A\cdot N_{\mathbb Q(\zeta_{2p})/\mathbb Q}\bigl(2A-\zeta_{2p}+\zeta_{2p}^{-1}\bigr)$,
  i.e. $\operatorname{Res}(\Phi_{2p}(T),T^2-2AT-1)=V_p(4A^2)$; and
  $\mathbb Q(\theta_p)\subseteq\mathbb Q(\zeta_p,(1+\sqrt2)^{1/p})$ with
  $\theta_p=\eta-\eta^{-1}$, $\eta^p=1+\sqrt2$.

The congruences are necessary conditions only: $205$ (resp. $193$) of the $10000$
values $A=8k+2\le80000$ satisfy all four cheap conditions, $A=2$ among them. Details:
`elementary_conditions.md`, `route_scope.md`.

## R3. Route diagnoses (not impossibility theorems) [proof / diagnosis]

| Route | Verdict | Reason |
|---|---|---|
| fixed-modulus covering congruence | **impossible** (proved) | R1 |
| refinements at 2 ($2^k$, squareclasses of $Q_p$) | impossible (proved) | $Q_p(A)\equiv1\pmod8$ |
| Pell / continued fraction / descent | diagnosis | the data produced are valuation parity, necessarily consistent with squares |
| cheap $A$-dependent congruences | insufficient as a route | $2\%$ of $A$ satisfy all of them |
| Lucas rank of apparition | unavailable at index $p$ | $w_p\equiv p\pmod{A^2+1}$, and $A^2+1=p$ has no solution in the hard phase |
| cyclotomic/Kummer resultant | new identity only | the exact norm identity is for $F_p$, not $Q_p$; "$-1$" is invisible to ideal valuations |
| manuscript's route; global/height/curve/LFT arguments | outside the scope of R1 | not addressed |

## R4. Independent re-checks of the manuscript's data [cert]

Reproduced from the recurrence with my own code (`verify_route_scope.py`):

* $g_{17}(4)/2=22768774561$, $g_{41}(4)/2=25377553679502347277411601$: matches
  (4.6), (4.10); $g_p(2A)/2=F_p(A)-1$ for $A<60$.
* $\operatorname{disc}(g_{17})=2^{24}17^{17}=13878788557563639341338591232$ and
  $\operatorname{disc}(g_{41})=2^{60}41^{41}$: matches Table 3 exactly.
* $U_{17}(4)=532303029$, $U_{41}(4)=-43956715453803235217163523$: matches (4.6),
  (4.10) using the printed coefficient lists (4.4), (4.7)–(4.8).
* Table A1 factorisations: $F_{17}(2)-1=13\cdot1751444197$ and
  $F_{41}(2)-1=79\cdot1373\cdot115471\cdot1506563\cdot1344905911$; and
  $F_{41}(2)-1\equiv20\pmod{23}$ is a non-residue — the manuscript's endpoint witness.
* Proposition 7.1, $J(U_p(2A),F_p(A)-1)=-1$, holds for all $A=8k+2\le20000$
  (2500 values per prime) with $\gcd(U_p(2A),F_p(A)-1)=1$, and at random
  $A\equiv2\pmod8$ up to $8\cdot10^{12}$ (`jacobi_extended.py`).
* Lemma 1 (the manuscript's (2.8), hence Proposition 2.1) has an independent
  elementary proof.

## R5. Numerics [num — no proof value]

* $Q_{17}(A)$ and $Q_{41}(A)$ are never squares for $A\in[0,200000]$; likewise for
  $p=3,5,7,11,13,19$ (same range). These are numerical observations at the indices
  and height stated; I make no claim about the general statement "no odd $p\ge3$, no
  $A$", and I did not survey the literature on it (shifted-power results in
  Lucas/Fibonacci-type sequences are outside this direction).
* Explicit data for R1 (`verify_route_scope.py` §[6]): for $p=17$,
  $A=13436280461778872715068835665689687346047342031343196025682332048755323382446365162$
  satisfies $A\equiv2\pmod 8$ and $Q_{17}(A)$ is a square in $\mathbb Q_2$ and in
  $\mathbb Q_\ell$ for every prime $\ell\le200$, while $211$ is a (W1) witness. No
  prime $\le200$ divides $Q_{17}(A)$, so every (W2) witness of this $A$ exceeds 200
  (not computed: $Q_{17}(A)$ has about 1400 digits). The analogous $p=41$ value is
  $A=22805347438890107579041398021068316865585543438038802371828994845480719532417275042$
  with first (W1) witness $227$.
* Square-modulus certificates: $A=72708208931635202$ ($p=17$) and
  $A=58627620392140802$ ($p=41$) give $t^2\equiv Q_p(A)\pmod M$ with
  $M=2^{20}3^25^27^211^213^223^2$, $t=84837427159578031$ resp. $76419143705971351$.

## Evidence classification

| Item | Kind |
|---|---|
| R1 Theorem, Lemma 1, Lemma 2(ii), Corollary | ordinary proof (Weil bound cited) |
| R1 Lemma 2(i), R2 resultant identity for $p\le41$, R4 re-checks | exact finite certificates (scripts here) |
| R3 route diagnoses | proofs about specific mechanisms; diagnoses otherwise |
| R5 searches | numerical experiment only |
| manuscript's Hilbert argument, uniform Prop 7.1, Cor 1.5, Lean development | not verified by me (other directions) |

## Not done / open

1. No alternative *proof* of Theorems 1.2/4.2; R1 excludes only fixed-modulus
   congruence tests.
2. The Kummer model $\mathbb Q(\zeta_p,(1+\sqrt2)^{1/p})$ (R2) is a plausible home for
   a cyclotomic-unit proof; I did not attempt its $S$-arithmetic.
3. Existence of a (W1)-witness construction of lower complexity than the manuscript's
   certificate is open in the weak sense that I have neither a construction nor an
   exclusion; no literature survey was made.
4. No re-run of the public Lean build; no change to the manuscript; no claim about the
   formal development.

## Files

| File | Contents |
|---|---|
| `theorem_no_finite_modulus.md` | witness notions, Lemma 1, Lemma 2, Theorem 1, Corollary 2, scope |
| `elementary_conditions.md` | the new congruences, four necessary conditions, data |
| `route_scope.md` | Prop. 3.1 (cyclotomic resultant), Prop. 4.1 + Cor. 4.2 ($w_p\bmod K$), diagnoses |
| `verify_route_scope.py` | all finite data; prints `ROUTE_SCOPE_OK` |
| `route_scope_checks.py` | Prop. 3.1 and Prop. 4.1 exactly; prints `ROUTE_SCOPE_CHECKS_OK` |
| `jacobi_extended.py` | Prop. 7.1 at $A=8k+2\le20000$ and large random $A$; prints `JACOBI_EXTENDED_OK` |
| `dickson.py`, `cover.py`, `routes.py`, `needed.py`, `search.py`, `jacobi_check.py`, `lemma_checks.py`, `cyclo.py` | exploratory scripts kept for audit |

## Reproduce

```
cd .ultramath/smw70l62n/m7
python3 verify_route_scope.py      # ~20 s, ROUTE_SCOPE_OK
python3 route_scope_checks.py      # <1 s,  ROUTE_SCOPE_CHECKS_OK
python3 jacobi_extended.py         # <1 s,  JACOBI_EXTENDED_OK
```
Python 3.12 + SymPy (only `jacobi_symbol`, `legendre_symbol`, `factorint`, `sqrt_mod`,
`resultant`, `cyclotomic_poly`); everything else is plain integer arithmetic.
