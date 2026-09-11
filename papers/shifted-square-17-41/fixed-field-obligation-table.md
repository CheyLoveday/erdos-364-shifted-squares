# Fixed-field obligations for the degree-17 and degree-41 Hilbert proofs

Issue: #120
Consumer: Theorem H2 in
[hilbert-obstruction-lamport.md](hilbert-obstruction-lamport.md)

## Evidence discipline

The table distinguishes four proof classes and one validation status.

- **Direct GP input** is an exact fail-closed assertion in the named verifier.
- **Human lemma** is a complete quantified argument in the H1/H2 note.
- **Derived or explicit source datum** is an exact consequence of cited rows
  or a displayed source definition, rather than a separate GP assertion.
- **Maintained Lean** is the separate integer-Jacobi interface.  It is not a
  formalisation of the Hilbert argument.

**Replay** is validation provenance, not a proof class: it means the
unmodified verifier was executed with its locked PARI/GP version and
fail-closed marker.

No bounded calculation is used to prove a quantified lemma.  The direct
dyadic rows are the authoritative finite input for the reference product;
the odd-support calculation is a consistency cross-check and is not used to
derive that input circularly through reciprocity.

## Side-by-side obligation table

| H2 obligation | Degree 17 | Degree 41 | Proof class and use |
|---|---|---|---|
| Degree and Dickson–Lucas bridge | the displayed source polynomial has degree \(17\), and its Dickson equality and bridge are asserted: [GP L34–80](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L34-L80) | \(d=41\) is asserted, with the same bridge: [GP L42–69](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L42-L69) | Explicit source datum plus direct GP identities for degree 17; direct GP assertions for degree 41; connects H2 to the fixed target |
| Irreducibility | modulo \(67\) and over \(\mathbf Q\): [GP L82–90](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L82-L90) | modulo \(163\) and over \(\mathbf Q\): [GP L71–77](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L71-L77) | Direct GP input; also dispatches \(Y=0\) |
| Polynomial discriminant | \(2^{24}17^{17}\): [GP L92–95](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L92-L95) | \(2^{60}41^{41}\): [GP L78–81](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L78-L81) | Direct GP input |
| Maximal power order | \(\operatorname{index}=1\): [GP L97–102](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L97-L102) | \(\operatorname{index}=1\): [GP L83–88](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L83-L88) | Direct GP input; gives \(\mathcal O_L=\mathbf Z[\theta]\) and equality of polynomial and field discriminants |
| Field discriminant support | \(2^{24}17^{17}\): [GP L100–103](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L100-L103) | \(2^{60}41^{41}\): [GP L86–89](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L86-L89) | Direct GP input; all odd primes other than the named prime are unramified |
| Signature | \((1,8)\): [GP L104](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L104) | \((1,20)\): [GP L90](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L90) | Direct GP input; unique real embedding |
| \(N(\theta)=2\) | [GP L106–118](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L106-L118) | [GP L92–101](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L92-L101) | Direct GP input; square-norm orientation and odd-place unitness of \(\theta\) |
| Detector unit and norm metadata | \(\operatorname{Res}(g,u)=-1\), \(N(u)=-1\), \(N(b)=-2\): [GP L111–122](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L111-L122) | same: [GP L97–105](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L97-L105) | Direct GP input; stronger than H2 needs |
| Detector ideal | \((b)=(\theta)\): [GP L123–126](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L123-L126) | \((b)=(\theta)\): [GP L106–109](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L106-L109) | Direct GP input; load-bearing odd-place unit contract |
| Unique odd ramified prime | one prime above \(17\), descriptor \((e,f,v(\theta),v(4-\theta),v(b),(\delta_4,b))=(17,1,0,0,0,1)\): [GP L161–182](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L161-L182) | corresponding \(41\)-descriptor \((41,1,0,0,0,1)\): [GP L143–164](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L143-L164) | Direct GP input; the unique-\(f=1\) branch of Lemma H2.2 |
| Optional ramification congruence | Not part of the direct degree-17 verifier contract; H2 does not use it | \(g\equiv(T-2)^{41}\pmod {41}\): [GP L165–168](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L165-L168) | Explicitly non-load-bearing once the preceding row is certified |
| Dyadic types | \((1,1),(2,4),(2,4)\): [GP L128–154](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L128-L154) | \((1,1),(2,10),(2,10)\): [GP L111–137](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L111-L137) | Direct GP input |
| Dyadic valuation triples | sorted \((v(\theta),v(4-\theta),v(b))=(1,1,1),(0,0,0),(0,0,0)\): [GP L132–154](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L132-L154) | same triples: [GP L115–137](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L115-L137) | Direct GP input |
| Strict dyadic Hensel inequalities | \((e,d)=(1,1)\Rightarrow3>2\); \((2,0)\Rightarrow8>4\) | identical inequalities | Derived exactly from the preceding two rows by [Lemma H2.4](hilbert-obstruction-lamport.md#lemma-h24-dyadic-hensel-squareclass) |
| Direct reference dyadic symbols | sorted \(+1,-1,+1\), product \(-1\): [GP L146–159](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L146-L159) | sorted \(+1,-1,+1\), product \(-1\): [GP L129–141](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L129-L141) | Direct GP input; authoritative H2 reference-product row |
| Unique real root in \((0,4)\) | signature plus \(g(0)=-2<0<g(4)\): [GP L276–280](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L276-L280) | same: [GP L245–249](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L245-L249) | Derived from the direct GP signature/sign assertions by the intermediate value theorem; used by Lemma H2.3 |
| Reference half norm and factorisation | \(g(4)/2=13\cdot1751444197\), both factors prime: [GP L184–206](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L184-L206) | \(g(4)/2=79\cdot1373\cdot115471\cdot1506563\cdot1344905911\), all factors prime: [GP L170–209](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L170-L209) | Direct GP input; finite reference audit |
| Reference integer character | \(J(b(4),g(4)/2)=-1\): [GP L208–230](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L208-L230) | \(J(u(4),g(4)/2)=J(b(4),g(4)/2)=-1\): [GP L192–195](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L192-L195) | Direct GP input; crosswalk check |
| Reference odd ideal support and local symbols | primes above \(13,1751444197\), exponent one; symbols \(-1,+1\): [GP L232–274](../../experiments/sm2_outer_seventeen/outer17_verify.gp#L232-L274) | five displayed degree-one primes, exponent one; symbols \(+1,-1,-1,-1,+1\): [GP L211–243](../../experiments/sm2_four_translate/interpolation/outer41_verify.gp#L211-L243) | Direct GP input; consistency check against the direct dyadic product |
| Unramified simple-factor uniqueness | [Lemma H2.2](hilbert-obstruction-lamport.md#lemma-h22-odd-place-valuation-parity) | same common lemma | Complete human lemma; Dedekind–Kummer, not computation |
| Norm valuation equality and parity | [Lemma H2.2](hilbert-obstruction-lamport.md#lemma-h22-odd-place-valuation-parity) | same common lemma | Complete human lemma; does not infer local parity from a square norm without uniqueness |
| Odd Hilbert symbols | [Lemma H2.3](hilbert-obstruction-lamport.md#lemma-h23-odd-finite-and-archimedean-neutrality) | same common lemma | Complete human lemma using the exact tame formula |
| Stable congruence class | \(x\equiv4\pmod {16}\) | \(x\equiv4\pmod {16}\) | Complete human proof in [Lemma H2.4](hilbert-obstruction-lamport.md#lemma-h24-dyadic-hensel-squareclass) |
| Fixed-field Hilbert conclusion | Theorem H2 | Theorem H2 | Complete conditional human theorem with all finite inputs discharged above |
| Maintained integer-Jacobi conclusion | [no_sm2LucasReal_seventeen_square_of_mod_eight_two, Lean L2015–2050](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterSeventeen.lean#L2015-L2050) | [ss41_shiftedSquare_impossible, Lean L13696–13708](../../Erdos364/SquareMiddle/Sm2LowerSquareOuterFortyOne.lean#L13696-L13708) | Maintained Lean; separate arithmetic proof route |

## Exact finite reference rows

### Degree 17

\[
g_{17}(4)=45537549122
 =2\cdot13\cdot1751444197,
\]

\[
u_{17}(4)=532303029,\qquad
b_{17}(4)=2129212116.
\]

The odd ideal support of
\(\delta_4=(4-\theta)/\theta\) consists exactly of the degree-one primes
above \(13\) and \(1751444197\), each to exponent one.  Their local
Hilbert symbols are \(-1,+1\).

The sorted dyadic descriptors

\[
(e,f,v(\theta),v(4-\theta),v(b),(\delta_4,b))
\]

are

\[
(1,1,1,1,1,+1),\quad
(2,4,0,0,0,-1),\quad
(2,4,0,0,0,+1).
\]

### Degree 41

\[
g_{41}(4)/2=25377553679502347277411601
\]

and

\[
25377553679502347277411601
=79\cdot1373\cdot115471\cdot1506563\cdot1344905911.
\]

Also

\[
u_{41}(4)=-43956715453803235217163523,
\qquad
b_{41}(4)=-175826861815212940868654092.
\]

The odd support consists exactly of the degree-one primes above the five
displayed rational primes, each to exponent one.  In increasing order their
local symbols are

\[
+1,-1,-1,-1,+1.
\]

The sorted dyadic descriptors are

\[
(1,1,1,1,1,+1),\quad
(2,10,0,0,0,-1),\quad
(2,10,0,0,0,+1).
\]

## Replay contract

The two bounded replays are:

    gtimeout 600 gp -q -f experiments/sm2_outer_seventeen/outer17_verify.gp
    gtimeout 600 gp -q -f experiments/sm2_four_translate/interpolation/outer41_verify.gp

Each verifier rejects any PARI version other than \(2.17.3\), ignores user
startup files through the command-line flag, fixes its random seed, and
exits nonzero on any failed assertion.  Successful replay emits exactly:

    OUTER17_CERTIFICATE_OK pari=2.17.3 target=no_sm2LucasReal_seventeen_square_of_mod_eight_two
    OUTER41_CERTIFICATE_OK pari=2.17.3 target=no_sm2LucasReal_forty_one_square_of_mod_eight_two

Replay on 2026-08-26 passed under PARI/GP \(2.17.3\): both commands exited
zero and emitted exactly their displayed one-line success markers.  The
degree-17 replay took under \(0.1\) seconds and the degree-41 replay under
\(10\) seconds, each beneath a \(600\)-second external timeout.  The final
immutable-head review must verify that the two GP blobs are unchanged from
the replayed base.

## Provenance and status hazards excluded

- The degree-17 verifier does not directly assert the optional congruence
  \(g\equiv(T-2)^{17}\pmod {17}\); the common theorem uses only the directly
  asserted unique-\(f=1\) prime.
- Older prose saying that the degree-17 or degree-41 endpoint was not yet
  maintained in Lean is not status authority.  The maintained theorem
  locators in the table are current at this branch base.
- The degree-41 certificate’s later maintained-Lean section supersedes its
  historical “remaining formal boundary” paragraph.
- No archived report hash is used to authenticate the present files.  The
  replays consume the current checked-out scripts directly.

## Claim ceiling

This table supports exactly the two fixed fields.  It does not prove a
detector-construction theorem, a result for every odd prime or degree, a
uniform \(SS_p\), independent certificate provenance, or a Hilbert-symbol
Lean formalisation.  It has no terminal, canonical, or Ledger effect.
