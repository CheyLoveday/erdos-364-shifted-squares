# Exact crosswalk between the Hilbert and integer-Jacobi proofs

Issue: #120
Consumer: Paper 1 proof architecture (#118)

## Shared source objects

For \(p\in\{17,41\}\), let

\[
D_0=2,\qquad D_1=T,\qquad D_{n+2}=TD_{n+1}+D_n,\qquad
g_p=D_p-2.
\]

For \(A\ge2\) with \(A\equiv2\pmod8\), put

\[
x=2A,\qquad
Q_0(A)=\frac{g_p(x)}2
      =\operatorname{sm2LucasReal}(A,p)-1.               \tag{1}
\]

Then \(x\ge4\) and \(x\equiv4\pmod {16}\).  Let
\(U_p\in\mathbf Z[T]\) be the exact detector polynomial recorded by the
fixed certificate, and set

\[
u_p=U_p(\theta),\qquad
b_p=\theta U_p(\theta),\qquad
\delta_x=\frac{x-\theta}{\theta}.                        \tag{2}
\]

The two GP verifiers reconstruct (1), \(U_p\), and the number-field
detector from the same source data:
[degree 17, L34–80 and L106–126](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L34-L126);
[degree 41, L35–69 and L92–109](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L35-L109).

## Local-to-integer character identity

Write \(J(a,n)\) for the Jacobi symbol with positive odd denominator
\(n\).  In the fixed phase \(Q=Q_0(A)\) is positive and odd.  The positivity
follows from the unique real root below \(4\); oddness follows from
\(g_p(0)=-2\) and \(4\mid x\).

At an odd rational prime \(\ell\mid Q\), the simple-factor argument of
[Lemma H2.2](hilbert-obstruction-lamport.md#lemma-h22-odd-place-valuation-parity),
or its unique ramified-prime branch, gives exactly one degree-one prime
\(\mathfrak P\) supporting \(\delta_x\), with

\[
v_{\mathfrak P}(\delta_x)=v_\ell(Q).
\]

Modulo \(\mathfrak P\), \(\theta\equiv x\), and hence

\[
b_p=\theta U_p(\theta)\equiv xU_p(x)\pmod{\mathfrak P}.
\]

The explicit odd local formula therefore gives

\[
\prod_{\substack{\mathfrak P\text{ finite}\\\mathfrak P\nmid2}}
(\delta_x,b_p)_{\mathfrak P}
=J(xU_p(x),Q).                                           \tag{3}
\]

There is no hidden coprimality assumption: \(b_p\) is an odd-place unit, so
every residue occurring on the right of (3) is nonzero.

Now write \(x=4m\).  The phase gives \(m\equiv1\pmod4\).  Since
\(g_p(0)=-2\),

\[
Q=\frac{g_p(4m)}2\equiv-1\pmod m.
\]

Thus \(\gcd(m,Q)=1\), including the harmless case \(m=1\).  Quadratic
reciprocity and \(m\equiv1\pmod4\) give

\[
J(m,Q)=J(Q,m)=J(-1,m)=1,
\]

while \(J(4,Q)=1\).  Therefore

\[
J(x,Q)=1
\]

and (3) becomes the exact bridge

\[
\boxed{
\prod_{\substack{\mathfrak P\text{ finite}\\\mathfrak P\nmid2}}
(\delta_x,b_p)_{\mathfrak P}
=J(U_p(x),Q_0(A)).
}                                                         \tag{4}
\]

Equation (4) is a proved identity under the fixed-field hypotheses, not a
metaphorical correspondence.

## Role-by-role correspondence

| Hilbert proof role | Integer-Jacobi proof role | Exact relationship and boundary |
|---|---|---|
| \(N(\delta_x)=Q_0(A)\) | right Jacobi argument \(Q_0(A)\) | Literal equality from (1)–(2); it is \(Y^2\) under the shifted-square hypothesis |
| detector \(b_p=\theta U_p(\theta)\) | numerator \(U_p(2A)\) before orientation | Reduction \(\theta\mapsto x=2A\), followed by removal of the Jacobi-neutral factor \(x\), gives (4) |
| odd-place support and unit control | specialization-safe common-factor transfer | Both prevent a hidden zero: Hilbert uses one degree-one supporting prime and odd-unitness; Lean proves exact gcd/endpoint corrections before every character transfer.  These are corresponding safeguards, not the same lemma |
| direct dyadic reference sign \(-1\) | reference/endpoint integer character \(-1\) | At \(x=4\), the odd character in (4) is \(-1\); reciprocity with the positive real factor gives the same nontrivial dyadic sign.  The GP scripts check both sides directly |
| dyadic squareclass stability on \(x\equiv4\pmod {16}\) | PRS/Jacobi propagation on \(A\equiv2\pmod8\) | Both keep the same detector character across the phase; one uses local Hensel squareclasses, the other exact specialization-safe polynomial identities |
| square norm forces even odd valuations and hence odd product \(+1\) | square right argument cannot have Jacobi value \(-1\) | The Hilbert contradiction and the Jacobi trichotomy are the same final incompatibility expressed locally and arithmetically |
| H1 product formula | final composition of the integer chain | Hilbert is conceptual local–global proof; the maintained chain is the formal arithmetic proof and does not formalize global reciprocity |

The requested schematic correspondence is therefore:

\[
\begin{aligned}
\text{Hilbert detector }b
&\longleftrightarrow
  \text{integer detector }U_p(2A),\\
\text{odd-place neutrality}
&\longleftrightarrow
  \text{specialization-safe common-factor control},\\
\text{reference dyadic sign}
&\longleftrightarrow
  \text{endpoint/reference Jacobi sign},\\
\text{square-norm contradiction}
&\longleftrightarrow
  \text{Jacobi trichotomy for a square right argument}.
\end{aligned}
\]

## Degree 17

The exact Lean source polynomials satisfy

\[
\operatorname{outer17R0}(A)=Q_0(A),\qquad
\operatorname{outer17R1}(A)=U_{17}(2A);
\]

compare
[Lean L16–24](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L16-L24)
with
[GP L34–57 and L69–80](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L34-L80).
The maintained proof establishes

\[
J(U_{17}(2A),Q_0(A))=-1
\]

on \(A=8k+2\) through the signed pseudo-remainder identities
[Lean L347–377](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L347-L377)
and the composed character theorem
[Lean L1914–2013](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L1914-L2013).
It then rewrites \(Q_0(A)=y^2\) and uses Jacobi trichotomy
[Lean L2015–2050](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L2015-L2050).

At the reference \(A=2\), the GP verifier checks
\(J(b_{17}(4),Q_0(2))=-1\), together with the exact odd support and local
symbols
[GP L184–274](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L184-L274).

## Degree 41 and the orientation sign

The raw number-field detector is \(U_{41}(2A)\).  The positive PRS
orientation is

\[
Q_1(A)=-U_{41}(2A),
\]

as locked by the source reconstruction
[outer41_jacobi_block.py L179–192](../../experiments/sm2_four_translate/interpolation/outer41_jacobi_block.py#L179-L192).
The later payload constructor locks the GP source bytes before rebuilding
the pair
[outer41_jacobi_block.py L619–629](../../experiments/sm2_four_translate/interpolation/outer41_jacobi_block.py#L619-L629).
The certificate reconstructs the same negatively oriented detector in
[build_source_pair](../../experiments/sm2_four_translate/interpolation/outer41_jacobi_certificate.py#L177-L186).

For the main phase \(A=8j+10\), the maintained denominator satisfies
\(Q_0(A)\equiv1\pmod8\)
[Lean L13602–13622](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13602-L13622).
Consequently

\[
J(-U_{41}(2A),Q_0(A))
=J(-1,Q_0(A))J(U_{41}(2A),Q_0(A))
=J(U_{41}(2A),Q_0(A)).                                  \tag{5}
\]

The positive orientation changes no character.  The maintained universal
coefficient chain is
[ss41_directedTelescope and ss41_coefficientJacobi, Lean L13353–13373](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13353-L13373).
It is consumed by the specialization-safe global transfer to prove
\(J(Q_1,Q_0)=-1\)
[Lean L13629–13664](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13629-L13664).

The maintained Lean theorem treats the boundary \(A=2\) separately by a
modulo-\(23\) nonsquare argument
[Lean L13666–13708](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13666-L13708).
Therefore direct proof-path identity with the maintained Lean implementation
is claimed only on the main phase \(A=8j+10\), not on that boundary branch.
The finite reference certificate separately checks

\[
J(U_{41}(4),Q_0(2))=-1
\]

and both forms of the detector character
[GP L170–195](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L170-L195).
The Hilbert reference argument covers the same \(x=4\) value.

## Logical relationship and provenance ceiling

For a general phase value, dyadic stability plus reciprocity makes the odd
product in (4) \(-1\).  Under a putative square norm, Lemma H2.2 makes every
odd valuation even, so that same product must be \(+1\).  The maintained
integer proof instead proves the left side of

\[
J(U_p(2A),Q_0(A))=-1
\]

by exact PRS/Jacobi transfer, then observes that a square right argument
cannot produce \(-1\).

Thus the Hilbert proof is a conceptual local–global proof and the
integer-Jacobi proof is the maintained specialization-safe formal arithmetic
proof.  They are two proof architectures, but they are not independent
certificate provenance.  They share:

- the same Dickson polynomial \(g_p\);
- the same detector polynomial \(U_p\);
- the same coefficient and reference data;
- the same shifted-square norm bridge.

The Lean developments add formal verification of the integer transfer
identities.  They do not formally verify the number-field Hilbert argument.

## Nonclaims

- This crosswalk does not construct \(U_p\) from a discriminant, a degree,
  or a dyadic decomposition.
- It does not prove a common detector for another prime.
- It does not turn finite GP checks into quantified local theorems.
- It does not make the Hilbert and Jacobi routes independently sourced.
- It does not identify the degree-41 \(A=2\) Lean implementation branch with
  the Hilbert/Jacobi character path.
- It has no terminal, canonical, or Ledger effect.
