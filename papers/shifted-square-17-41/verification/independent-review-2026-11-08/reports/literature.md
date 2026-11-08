# Literature / priority audit: shifted squares at 17 and 41

Scope: the literature-attributable steps of the manuscript (Theorem 1.3 via Sanna;
Corollary 1.5's rank via Walker, including the part the paper does not cite from him),
the novelty of the main theorems as bounded by the searches recorded in §3, and the
exact boundary of what literature can certify. I record one error of an earlier version
of this note in §3: $D_p(2)\ne2$, so there is no rational point $(2,0)$ on the relevant
curve.
Paper audited: `papers/shifted-square-17-41/manuscript/revision/paper_1_github.md`
at commit `c663b4e1e65c99846d41270a288f154559cc9fd6` (working tree date 2026-10-26).
Environment date of this audit: 2026-11-07. Every locator below was checked against
the primary PDF, fetched 2026-11-07 (see `commands.sh`, texts in this directory).

Verdicts use the paper's own evidence classes: **formal** (Lean), **human proof**,
**finite certificate**, **literature**, **numerical experiment**.

---

## 1. Citation audit (all 16 references, primary PDFs)

All sixteen references resolve (HTTP 200); every reference that carries a numbered or
paged locator has that locator present, with the content the paper attributes to it.
The single reference cited without a locator, the monograph [16], is treated separately
after the table. No locator needs correction.

| ref | claimed locator | found in primary source | verdict |
|:--|:--|:--|:--|
| [1] Bremner–Tzanakis | JNT 107 (2004) 215–227; "$U_9$/$U_{12}$ a square, varying parameters" | arXiv:math/0405306 (same title) intro confirms exactly this; journal pages not independently checked | accurate |
| [2] Bennett–Dahmen–Mignotte–Siksek | MPCM 158 (2015) 305–329; "shifted powers using Frey curves over totally real fields" | DOI resolves to the Cambridge page; arXiv:1408.1710 (same title): Frey curves over *real quadratic* fields, $U_k = a x^n + c$ | accurate; journal pages not independently checked |
| [3] Bennett–Patel–Siksek | Res. Number Theory 5 (2019) Art. 15 | Thm 1: $F_k \pm 2 = y^p$ ($p$ prime) $\Rightarrow \lvert k\rvert \in \{1,2,3,4,9\}$ | accurate; **fixed sequence, varying index** |
| [4] Chan | Integers 25 (2025) A7 | header `#A7 INTEGERS 25 (2025)`; Thm 1: no triplet $x^3-1=p^3y^2,\ x^3,\ x^3+1=q^3z^2$; preprint arXiv:2503.21485 has the same title | accurate |
| [5] Milne, CFT | Ch. III §4 (Hilbert pairing); Ch. VIII §5 item 5.10 (reciprocity) | Ch. III §4 "The Hilbert symbol", p. 110; Ch. VIII §5.10, p. 246: $\prod_v (a,b)_v=1$ | accurate, both locators |
| [6] Oh, ANT notes | Thm 16.32, non-dyadic Hilbert symbol formula | Thm 16.32 "Tame Hilbert symbols" (general $n$) | accurate; for $n=2$ it yields (3.7) exactly |
| [7] Conrad, Hensel | Thm 9.1, strong Hensel | Thm 9.1: $\lvert f(a)\rvert<\lvert f'(a)\rvert^2$ ⇒ root, i.e. $v(f(a))>2v(f'(a))$ | accurate |
| [9] SymPy | PeerJ CS 3 (2017) e103 | standard locator | accurate |
| [10] Vidaux–Videla | arXiv:1809.04122, Thm 1.1 = Dedekind index criterion | Thm 1.1 (Dedekind 1878): $p$-maximality ⇔ no $\bar\phi_i$ with $e_i>1$ divides $\bar g$ | accurate, exact form used |
| [11] Sutherland, 18.785 Lec. 6 | Thm 6.14 = Dedekind–Kummer | yes, **with hypothesis $B=A[\alpha]$** | accurate; paper proves monogenicity (App. A.2) *before* applying it — correct dependency order |
| [12] She | Integers 25 (2025) A103 | header `#A103 INTEGERS 25 (2025)`; Thm 1: no triplet $x^3-1=p^2a^3,\ x^3,\ x^3+1=q^2b^3$, $p,q$ primes | accurate |
| [13] Ma | arXiv:2608.23418 (2026) | v1 dated 24 Aug 2026; Thm 1.2: $x^n-1=q_1^3y^2,\,x^n,\,x^n+1=q_2^3z^2$, $n\ge5$ | accurate |
| [14] Walker | eq. (3), p. 112; Thm 2.2(2)–(3), pp. 112–113; Thm 2.5, p. 113; Lemma 2.4 | all present at those pages, with those contents (see §2) | accurate |
| [15] Sanna | Thm 1.5, p. 119 | Theorem 1.5 is stated across the p. 118/119 break, corollaries on p. 119 | accurate (locator 119 is at worst half a page late) |
| [16] Lidl–Mullen–Turnwald | no locator given (monograph, Pitman 65, 1993, ISBN 978-0-582-09119-1) | ISBN-13 check digit recomputed: valid for 0-582-09119-5; book not available online here, so its content was **not** checked — see the note below | bibliographic data accurate; content unchecked |

**[16] in detail.** The paper attributes to this book only the Dickson composition law
$D_m(D_n(T,a),a^n)=D_{mn}(T,a)$ (used with $a=-1$, $n$ odd). Since the book is not
accessible here, I verified the *statement* instead: `dickson.py` checks it as an exact
polynomial identity for $a\in\{-1,2,3,5\}$ and $1\le m,n\le8$, including the
specialisation that gives Lemma 5.1 ($F_3(F_5(A))=F_{15}(A)$) and the parity guard the
paper flags ($F_2(F_2(A))\ne F_4(A)$, with $F_4(2)=161$ vs $F_2(F_2(2))=163$). Lemma 5.1
is also proved directly in the paper, so nothing load-bearing rests on the book; what
remains unchecked is only the book's own numbering, which the paper does not cite.

Nothing in the manuscript is attributed to a source I could show does not contain it;
the sole item I could not check against primary text is the monograph [16] above.

---

## 2. The literature-derived steps, checked statement-by-statement

### 2.1 Sanna ⇒ Theorem 1.3 (exact even-index 2-adic valuation)

Paper's claim (§2.3): Sanna's Theorem 1.5 with $a=2A$, $b=1$, $\Delta=4(A^2+1)$ gives
$v_2(w_r)=v_2(r)+v_2(A)$ for even $r$ and $0$ for odd $r$.

Sanna's Theorem 1.5, case " $p\mid\Delta$, $p\mid n$ ": $v_p(u_n)=v_p(n)+v_p(u_p)-1$.
Here $p=2\mid\Delta$, $u_2=a=2A$, so $v_2(u_n)=v_2(n)+1+v_2(A)-1=v_2(n)+v_2(A)$;
case $p\mid\Delta$, $p\nmid n$: $v_2(u_n)=0$. Hypotheses $p\nmid b$ ($b=1$) and
nondegeneracy ($A\equiv2\bmod4\Rightarrow A\ge2$) hold. **Exact match, no slack.**

Paper's transfer: with $F_r^2-(A^2+1)w_r^2=(-1)^r$ and $r$ even,
$F_{2r}-1=2(A^2+1)w_r^2$, so $v_2=1+2(v_2(r)+v_2(A))=2v_2(N)+1$ using $v_2(A)=1$.
Recomputed by hand and numerically (`checks.py`, part A): for all $A\equiv2\bmod4$,
$A\le478$, and $1\le r\le40$, Sanna's formula and both identities hold.

The doubling proof in §2.3 is also self-contained and correct; the only place it uses
more than (2.7) is $v_2(F_n+1)=1$ for even $n$, which (2.7) supplies.

### 2.2 Walker ⇒ the rank $R=K/\gcd(K,v)$ in Corollary 1.5

Paper's claim: Walker's eq. (3) (p. 112) gives $b_n\equiv n u^{n-1}v \pmod K$;
Thm 2.2(3) gives the least solution with property Q as $(x+y\sqrt D)^I$ with
$I=\prod_{p\mid D,\;p\nmid y}p$; since $K$ is odd, $I=K/\gcd(K,v)$; Thm 2.5 restricts
to odd powers in the minus-sign case; Lemma 2.4 identifies the norm-one normalisation.

All four statements are verbatim in Walker at the cited pages, and the specialisation
is legitimate: Walker's $D$ is squarefree (the paper's $K$ is by construction),
$(x,D)=1$ (the paper's $\gcd(u,K)=1$ from $u^2+1=Kv^2$), and the minus-sign case
forces $D$ odd (the paper's (6.2): $K\equiv5\bmod8$). Walker's (3) is exactly the
binomial expansion the paper writes out in (6.5), so §6.3 is a self-contained
re-derivation rather than a citation-only step.

Independent numerical check. Command: `python3 walker.py 5000` (about 44 s; the default
argument is 5000, the module's `check` function is cheap and exhaustively searched over
$1\le i\le R$). For **every** squarefree odd $K\le5000$ for which
$X^2-KY^2=-1$ is soluble (456 kernels; the solution is found from the continued
fraction of $\sqrt K$, period odd), with $\varepsilon=u+v\sqrt K$ the least such unit,
the least $i>0$ with $K\mid b_i$ in $\varepsilon^i=a_i+b_i\sqrt K$ equals
$K/\gcd(K,v)$ in every case, and the search over $1\le i\le R$ is exhaustive because
$R$ itself always works ($K\mid Rv$). 21 kernels exercise the non-fundamental branch
$R<K$ of Walker's Theorem 2.2(3), e.g. $K=185=5\cdot37$ with $R=37$,
$K=1241=17\cdot73$ with $R=73$, $K=4777$ with $R=281$. `checks.py` part B does the
same for the 27 kernels $\le241$ by a different route (direct negative-Pell scan).
Walker's identity (6.7) $K/\gcd(K,2uv)=K/\gcd(K,v)$ is immediate from $\gcd(u,K)=1$
and $K$ odd. Note also that $I=\prod_{p\mid K,\;p\nmid v}p$ in Walker's Thm 2.2(3) *is*
$K/\gcd(K,v)$ only because $K$ is squarefree, which the paper's (1.7) guarantees.

---

### 2.3 Walker's Type-I classification covers more of Corollary 1.5 than the paper claims

Walker's §2 does not merely supply a rank formula: it classifies **all** consecutive
powerful pairs of Type I, i.e. all $(X^2, DY^2)$ with $DY^2$ powerful, which is
exactly the paper's application pair $(X^2, X^2+1)$ with $X^2+1=K^3V^2$ powerful.
His Theorem 2.5 with the minus sign ("... all such solutions of (1) with the minus sign
for odd positive integers $h$") plus Theorem 2.2(3) give at once:

> if $K$ is squarefree odd and $X^2-KY^2=-1$ has a solution in $\mathbb Z[\sqrt K]$,
> then every solution with property Q is $\varepsilon^{Rh}$ with $h$ odd, where
> $\varepsilon$ is the least unit $>1$ of $\mathbb Z[\sqrt K]$ and $R=K/\gcd(K,v)$.

Corollary 1.5's $\eta=X+KV\sqrt K$ has second coefficient divisible by $K$, so it
automatically has property Q. Hence Walker alone already yields the paper's conclusions
$X+KV\sqrt K=\varepsilon^N$, $R\mid N$, $N$ and $E=N/R$ odd. That part of Corollary 1.5
is therefore **previously published**, not new to this paper. This is external
literature support, not machine formalisation: Appendix B records no Lean statement of
Corollary 1.5, so the paper's own evidence-table distinction (literature versus formal)
is untouched, and I make no formal claim here. What Walker does not supply is the
*normal form* itself
($X^2+1=K^3V^2$ with $K$ squarefree, $X\equiv2\bmod 8$, and the identification
$X=F_N(u)$ in (6.4)), nor $\gcd(N,17\cdot41)=1$, which is Theorem 1.1.

Two compatibility points, both of which do hold, and both of which would be silent
failure modes if they did not:

1. **Order.** Walker's "solution $x+y\sqrt D$" means $x,y\in\mathbb Z$, i.e. the order
   $\mathbb Z[\sqrt D]$, **not** the maximal order. Since $K\equiv5\bmod8$ (6.2) we have
   $K\equiv1\bmod4$, so $\mathcal O_{\mathbb Q(\sqrt K)}=\mathbb Z[(1+\sqrt K)/2]$ is
   strictly larger and its fundamental unit can differ. The paper's explicit choice to
   work in $\mathbb Z[\sqrt K]$ (§6.2: "using a generator from a larger order could
   change the exponent being discussed") is therefore *required* for the citation to be
   correct, and it is made.
2. **Least unit versus fundamental minus-solution.** Walker's $\varepsilon$ is the least
   positive solution of the minus equation; the paper's is the least unit $>1$ of the
   order. These coincide: units of $\mathbb Z[\sqrt K]$ are $\pm\varepsilon_0^{\mathbb Z}$
   for the least $\varepsilon_0>1$ (the paper's §6.2 argument), and if $N(\varepsilon_0)=+1$
   then no unit has norm $-1$, contrary to hypothesis; so $N(\varepsilon_0)=-1$ and every
   positive minus-solution is $\varepsilon_0^n$ with $n$ odd, hence $\ge\varepsilon_0$.

So the paper under-cites rather than over-cites: a load-bearing half of Corollary 1.5
(oddness of $N$, $R\mid N$, $E$ odd) is published mathematics, and the paper's own
(6.5)–(6.6) re-derivation is a correct independent route to it. The consequence for an
assurance audit is narrow: that half no longer needs re-verification from scratch — the
published classification can be checked against the paper's specialisation, which this
section does — but it is supported by a human literature argument, not by a machine
proof.

A concrete instance, taken from Walker's own Example (3) (p. 113) and verified here:
$K=5$, $\varepsilon=2+\sqrt5$, $\varepsilon^5=682+305\sqrt5$, so $X=682$,
$KV=305=5\cdot61$, and $X^2+1=465125=5^3\cdot61^2$ is powerful with $X\equiv2\bmod 8$,
$N=5$, $R=5/\gcd(5,1)=5$, $R\mid N$, $N$ odd. Walker's example satisfies every
hypothesis of Corollary 1.5 except $X-1\in\square$ ($681$ is not a square). So the
number-field mechanism of the paper's application is classical and already exemplified
in the cited source; only the lower-square condition (and hence the connection to
powerful triples) is new, and that is exactly the condition Theorem 1.1 consumes.



## 3. Priority: is any of this already published?

Searches run (Web/Exa, 2026-11-07), recorded verbatim so the claim below is bounded by
them:
(1) "shifted squares in Lucas sequences x^2 + 1 equals a term of a Lucas sequence
powerful numbers"; (2) "three consecutive powerful numbers square middle term X-1 square
X^2+1 powerful exponent restriction Pell"; (3) "Lucas sequences whose nth term is a
square or an almost square Acta Arithmetica 126 2007". From these I followed the primary
PDFs cited as [1]–[4], [12], [14], [15] plus Finkelstein (1975) and Ribenboim (1999).
Two disjoint bodies of prior art exist; **in the sources I read, neither contains the
manuscript's theorems**.

**(a) Shifted squares with the sequence fixed and the index varying.**
R. Finkelstein, *On Lucas numbers which are one more than a square*,
Fibonacci Quart. 13 (1975) 340–342 (read in full: the only Lucas numbers of the form
$y^2+1$ are $L_0=2,L_1=1$; and his earlier paper gives the Fibonacci numbers of that
form as $F_1,F_2=1,F_3=2,F_5=5$); P. Ribenboim, *Binary recurring sequences and powers,
II*, Publ. Math. Debrecen 54 (1999) 349–375 (read in full: Theorems U1, V1, U2, V2 for
$U_n,V_n=k\square$ with $(P,Q)\in S^-$, i.e. **$P,Q$ both odd**); Steiner and Williams,
the Fibonacci $x^2+1$ determination, which I know only through Ribenboim's introduction
and did not consult directly; [2], [3] above.
None applies: there $(P,Q)$ is fixed and $n$ varies, whereas Theorems 1.1/1.2 have
$n\in\{17,41\}$ fixed and $A$ varying; and Ribenboim's odd-parameter hypothesis
excludes the paper's family, where $P=2A$ is even.

**(b) Fixed index, varying parameter, unshifted (scaled) squares.**
Bremner–Tzanakis [1]; the same authors' *Lucas sequences whose nth term is a square or an
almost square*, Acta Arith. 126 (2007) 261–280, whose Theorem 2.1 reads: "Let $k,n_0$ be
fixed non-zero integers with $n_0\ge8$. Then $U_{n_0}(P,Q)=k^2$ can hold for at most
finitely many relatively prime integers $P,Q$", and which reports the small-index cases
solved ($k=1$, $8\le n\le12$) and results of Mignotte–Pethő and Nakamula–Pethő (e.g.
$U_n(P,-1)=m^2$ with $P\ge1$, $n\ge4$ only for $(P,n,m)=(1,12,12),(2,7,13)$).
Provenance caveat: I read these from a text excerpt of the 2007 paper (the arXiv PDF's
fonts defeat text extraction here, and I did not consult Mignotte–Pethő or
Nakamula–Pethő directly), so the quotations are second-hand in that one respect; the
2004 paper [1] I read in full.
These cover scaled squares $k\square$, not the *shift* $F_p(A)-1$, and give
finiteness rather than an explicit exclusion.

**Why the paper's case is not covered by any of them.** Fixing the index turns the
problem into rational points on one fixed curve: $F_p(A)-1=y^2$ is $y^2=H_p(A)$ with
$H_p(A)=F_p(A)-1=g_p(2A)/2$, of degree $p$, leading coefficient $2^{p-1}$, and
squarefree (its roots are the roots of $g_p$ halved, and
$\operatorname{disc}(g_p)=2^{3(p-1)/2}p^p\ne0$). The degree is odd, so the smooth
projective model has genus $(p-1)/2$, namely $8$ at $p=17$ and $20$ at $p=41$.

I make no assertion about the rational point set of $H_p$. Two points are worth
recording because they are easy to get wrong: $H_p(0)=F_p(0)-1=-1$ for odd $p$, and
$D_p(2)=2F_p(1)\ne2$ — e.g. $D_2(2)=6$, $D_3(2)=14$, $D_{17}(2)=3215042=2F_{17}(1)$ — so
neither $A=0$ nor $A=1$ gives a point with $y=0$, and $g_p$ has no rational root (it is
irreducible of degree $p$; its real root is $\theta_p=2\sinh(\operatorname{arsinh}(1)/p)$
from (4.1)).

The manuscript determines no rational points. It excludes exactly two
sub-progressions: $A\equiv6\bmod8$ by reduction mod $8$, and $A\equiv2\bmod8$ by the
Hilbert criterion (i.e. $x=2A\equiv4\bmod16$, $x\ge4$, as (3.3) states). I found no
published determination of the rational point set of $H_p$ for $p=17,41$; that absence,
not any theorem of the paper, is why the fixed-index results cannot be cited from
classical literature.

**Verdict on novelty claims, bounded to the sources above.** They are stated narrowly and
consistent with what I read: Theorem 1.3 is Sanna's theorem specialised (and the paper
says so); the rank and oddness statements of Corollary 1.5 are Walker's (and the paper
says so for the rank); I found no source stating the fixed-index exclusion, the
index-divisibility composition, or the Jacobi certificate; the paper does not claim the
Hilbert and Jacobi routes are independent, and it is right that they are not (same
$g_p$, same $U_p$, same reference characters). I do not claim that nothing exists
outside these searches.

**One related-work omission (presentational, no mathematical consequence).**
Section 1.4 orients the shifted target only through [1] (fixed index, varying
parameter) and never cites the fixed-sequence shifted-square line: Finkelstein (1975),
Steiner, Williams, Ribenboim (1999). Those are the closest known results for the
literal question "$F_n$ one more than a square". Their hypotheses exclude the paper's
family, so nothing is implied or contradicted; but an adversarial reader will ask why
the only prior art quoted for shifted squares is a paper about unshifted squares.
Suggested one-sentence fix: cite Finkelstein/Ribenboim and note the reversed
quantifier order and the even parameter $P=2A$.

A curious exact contact point: at $A=2$, $\alpha=2+\sqrt5=\varphi^3$, so
$F_n(2)=L_{3n}/2$ (identity checked for $1\le n<40$ in `scope.py`). Theorem 1.1 at $A=2$ therefore
reads: $L_{3N}\ne 2y^2+2$ for $17\mid N$ or $41\mid N$ — i.e. "$2\square+2$", which is
one unit away from Ribenboim's Theorem V2 ("$V_n=2\square$ ⇒ $n\in\{3,6\}$") and from
Finkelstein's "$y^2+1$". The shift by exactly $1$ (equivalently by $2$ after the
normalisation) is precisely the gap that the cited literature leaves open; this is a
clean way to say why the paper's problem is not a corollary of anything classical.

---

## 4. Numerical scope experiment (evidence class: numerical experiment only)

`scope.py`, `scope2.py`; exact integer arithmetic, `isqrt`, doubling laws
$F_{2k}=2F_k^2-(-1)^k$, $F_{2k+1}=2F_kF_{k+1}-(-1)^kA$ (self-tested against the
recurrence for $A\in\{0,1,2,3,5,6,122,882\}$, $n<40$).

* odd $3\le n\le 99$, $A\equiv2\pmod4$, $A\le 5\cdot10^5$: **zero** $A$ with $F_n(A)-1$
  a square;
* $p=17$ and $p=41$, $A\not\equiv2\pmod 4$, $A<5\cdot10^5$: **zero** solutions;
* $n=1$: exactly the family $A=y^2+1$ ($y$ odd), 224 values for $A\le2\cdot10^5$ —
  the trivial family the manuscript itself flags.

Reading: the exclusion is not a near-miss phenomenon at the two proven indices, and
the proven parameter class is not where solutions stop being squares — both facts are
consistent with the paper, and neither is evidence for it. In particular these data
give no support for a uniform-in-$n$ theorem (none is claimed) and cannot substitute
for the proofs.

---

### 4.1 Is Corollary 1.5's family non-empty? (numerical experiment)

`cor15_family.py`. A member of the family is an $X\ge2$ with $X-1\in\square$ and
$X^2+1=K^3V^2$, $K$ squarefree — equivalently a solution $X+Y\sqrt K$ of
$X^2-KY^2=-1$ with $K\mid Y$ (put $V=Y/K$), i.e. an odd power $\varepsilon^n$ of the
fundamental minus-solution with $K\mid b_n$. Since $K$ must be odd and $X\equiv2\bmod8$,
enumerating squarefree odd $K\le30000$ and all odd powers with $X\le10^{40}$ gives
exactly **9 candidates**:

| $K$ | $X$ | $X\bmod8$ | $X-1$ square |
|:--:|:--|:--:|:--:|
| 5 | 682 | 2 | no |
| 5 | 1268860318 | 6 | no |
| 17 | 1459639851109444 | 4 | no |
| 5 | 2360712083917682 | 2 | no |
| 13 | 86149711981264908618 | 2 | no |
| 5 | 4392100110703410665318 | 6 | no |
| 5 | 8171493471761113423918890682 | 2 | no |
| 5 | 15203047261220215902863544865414318 | 6 | no |
| 37 | 5484296027914919579181500526692857773246 | 6 | no |

No member of the family is found. The enumeration is bounded in **both** parameters
(squarefree odd $K\le30000$, and $X\le10^{40}$), so it is not a proof of emptiness —
kernels $K>30000$ with $X\le10^{40}$ are outside it, as are all candidates above
$10^{40}$. The smallest candidate is Walker's own Example (3), $X=682$, which satisfies
everything except $X-1\in\square$. Reading: Corollary 1.5 is a conditional restriction
whose hypothesis is extremely restrictive and for which I found no witness, so it cannot
be validated by example; its content rests entirely on its proof. This is a statement
about scope, not a defect. (Consistency check: $682^2+1=465125=5^3\cdot61^2$,
$682\equiv2\bmod8$, $R=N=5$ — as in Walker.)

## 5. What this audit does and does not establish

Established: (i) every literature locator the manuscript gives is correct and, for the
items I could read, the cited statement says what the paper needs — the one exception is
the un-numbered monograph [16], where I verified the identity but not the book; (ii) the
two literature-derived sub-results (Theorem 1.3, the Corollary 1.5 rank) are exact
specialisations, verified symbol-by-symbol and numerically; (iii) Walker's Type-I
classification gives Corollary 1.5's $R\mid N$, "$N$ and $E$ odd" as *published
mathematics* (his hypothesis holds because $K\mid KV$ and $\mathbb Z[\sqrt K]$ is his
order) — literature support, not formalisation; (iv) in the literature I searched, I
found no theorem that implies Theorems 1.1, 1.2, 4.2 or Proposition 7.1; (v) fixing the
index makes the problem rational points on one fixed curve of genus 8 and 20, and I
found no published determination of those point sets — which is why, so far as I can
see, the fixed-index results cannot be imported from classical literature.

Not established (and not claimed by the paper): Theorem 3.2, the uniform
Proposition 7.1, and the 2-adic criterion remain human mathematics. Corollary 1.5 is now
split: its rank/oddness half has published support (Walker, §2.3 above — literature, not
formalisation), while its normal-form half ($X^2+1=K^3V^2$, $X\equiv2\bmod8$,
$X=F_N(u)$) and the conclusion $\gcd(N,17\cdot41)=1$ remain human mathematics depending
on Theorem 1.1. Literature supplies no independent provenance for the two units $u_{17},
u_{41}$ or for the dyadic characters; those are finite certificates, and the only
independent check of them is recomputation (Appendix C verifier). Literature also
cannot certify the Hilbert signs, because they are not published anywhere.

Precise location of the residual human gap, from the evidence classes alone:
Appendix C mechanises the irreducibility witnesses, the discriminants, the index
certificate at 2 and at $p$, both resultants, the factorisation of $H_p$ into distinct
primes, the valuations $v_\ell(H_p)=1$, the Legendre symbols of $4U_p(4)$ and the
reference Jacobi symbol. What it does **not** mechanise is exactly: (i) that the
supporting prime over each $\ell\mid H_p$ has residue degree one and valuation one on
$\delta_4$ (the step (3.5)); (ii) the local formula (3.7) applied at those primes;
(iii) Hilbert reciprocity (3.1); (iv) the strict-Hensel stability (3.8)–(3.10) and the
threshold $4e-d>2e$. Table 4's individual dyadic signs are explicitly "additional data,
not deductions" and are not recomputed by the verifier — only their product is
recovered, and that from the odd-prime characters by reciprocity. So the assurance of
Theorem 4.2 rests on a chain of length four of human steps, and every mechanised input
to that chain is independently reproducible from the printed coefficients alone. That is
a structural strength of the paper; my audit confirms the citation layer of it is clean.

Net assurance effect: my audit removes "the manuscript misuses its sources" as a
failure mode and leaves the load exactly where the manuscript says it is — on the
Hilbert criterion and its certificate data. This is a positive result about the
manuscript's citation discipline, not a proof of its theorems.
