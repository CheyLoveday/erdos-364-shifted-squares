import Erdos364.SquareMiddle.FlankKernelAllocation
import Erdos364.SquareMiddle.PairPellComplete

namespace Erdos364

/-!
# Source-facing square-middle normalization witnesses

`ValidNormalizedWitness X` is the concrete payload which a future source
normalizer must construct from a proof of `SquareMiddle X`.  It intentionally
contains the source proof and all reconstruction equalities.  Consequently it
is useful to the branch compiler without turning the still-unproved existence
of such a witness into an interface assumption.

The lower Pell datum is kept as `PairPellIndexData`: it supplies the kernel,
the canonical index parameter, and the fundamental-unit parity admissibility.
The two flank normal forms are retained separately because later routing needs
their individual kernels, not only their product.
-/

/-- A source-preserving normal-form witness for a square-middle centre.

This is data *conditional on construction*: the file provides no theorem that
every `SquareMiddle X` has such a witness.  That construction is exactly the
remaining source-normalization obligation. -/
structure ValidNormalizedWitness (X : Nat) where
  /-- The original source proposition, retained rather than reconstructed by
  an unverified converse. -/
  source : SquareMiddle X
  /-- The canonical lower-Pell kernel and odd-index parameter. -/
  pell : PairPellIndexData
  /-- The parity conditions which make the Pell datum admissible. -/
  pellAdmissible : pell.Admissible
  /-- Exact reconstruction of the source centre from the canonical Pell
  centre. -/
  center_eq : X = canonicalPellCenter pell.D pell.kernel pell.k
  /-- Canonical normal forms of the two linear flanks. -/
  flanks : SquareMiddleFlankNormalForms X
  /-- The lower and upper flank kernels multiply to the lower-Pell kernel. -/
  kernel_product : flanks.lowerKernel * flanks.upperKernel = pell.D

namespace ValidNormalizedWitness

/-- The discriminant/kernel carried by the Pell component. -/
abbrev D {X : Nat} (w : ValidNormalizedWitness X) : Nat := w.pell.D

/-- The nonnegative odd-index parameter carried by the Pell component. -/
abbrev k {X : Nat} (w : ValidNormalizedWitness X) : Nat := w.pell.k

/-- The Pell kernel certificate carried by the witness. -/
abbrev pellKernel {X : Nat} (w : ValidNormalizedWitness X) : PellKernel w.D :=
  w.pell.kernel

/-- Rebuild the centre solely from the stored Pell data. -/
noncomputable def reconstructCenter {X : Nat} (w : ValidNormalizedWitness X) : Nat :=
  canonicalPellCenter w.D w.pellKernel w.k

/-- The stored centre equality, oriented from the reconstructed value back to
the source coordinate. -/
theorem reconstructCenter_eq_source {X : Nat} (w : ValidNormalizedWitness X) :
    w.reconstructCenter = X := by
  exact w.center_eq.symm

/-- Reconstructing the centre preserves the full square-middle source
predicate. -/
theorem reconstructCenter_squareMiddle {X : Nat} (w : ValidNormalizedWitness X) :
    SquareMiddle w.reconstructCenter := by
  rw [w.reconstructCenter_eq_source]
  exact w.source

/-- The stored Pell data represents precisely the original source centre. -/
theorem pell_represents_source {X : Nat} (w : ValidNormalizedWitness X) :
    w.pell.Represents X := by
  exact ⟨w.pellAdmissible, w.center_eq⟩

/-- A square-middle witness always supplies the lower-pair source required by
the Pell normalization theorem. -/
theorem lower_source {X : Nat} (w : ValidNormalizedWitness X) :
    SquareMiddleLowerSource X := by
  exact ⟨w.source.1, w.source.center_even, w.source.2.1⟩

/-- The source centre is nontrivial. -/
theorem source_one_lt {X : Nat} (w : ValidNormalizedWitness X) : 1 < X :=
  w.source.1

/-- The source centre is even. -/
theorem source_even {X : Nat} (w : ValidNormalizedWitness X) : Even X :=
  w.source.center_even

/-- The left square-neighbour is powerful. -/
theorem lower_powerful {X : Nat} (w : ValidNormalizedWitness X) :
    PowerfulPos (X ^ 2 - 1) :=
  w.source.2.1

/-- The right square-neighbour is powerful. -/
theorem upper_powerful {X : Nat} (w : ValidNormalizedWitness X) :
    PowerfulPos (X ^ 2 + 1) :=
  w.source.2.2

/-- The explicit lower flank normal form. -/
theorem lower_form {X : Nat} (w : ValidNormalizedWitness X) :
    SquareCubeNormalForm (X - 1) w.flanks.lowerSquare w.flanks.lowerKernel :=
  w.flanks.lowerForm

/-- The explicit upper flank normal form. -/
theorem upper_form {X : Nat} (w : ValidNormalizedWitness X) :
    SquareCubeNormalForm (X + 1) w.flanks.upperSquare w.flanks.upperKernel :=
  w.flanks.upperForm

/-- The two flank kernels are coprime. -/
theorem flank_kernels_coprime {X : Nat} (w : ValidNormalizedWitness X) :
    Nat.Coprime w.flanks.lowerKernel w.flanks.upperKernel :=
  w.flanks.kernels_coprime w.source

/-- The stored product relation is the link from the two-flank allocation to
the lower Pell kernel. -/
theorem flank_kernel_product {X : Nat} (w : ValidNormalizedWitness X) :
    w.flanks.lowerKernel * w.flanks.upperKernel = w.D :=
  w.kernel_product

/-- The discriminant is odd, as recorded by Pell admissibility. -/
theorem kernel_odd {X : Nat} (w : ValidNormalizedWitness X) : Odd w.D :=
  w.pellAdmissible.1

/-- The fundamental Pell x-coordinate has the required even parity. -/
theorem fundamentalX_even {X : Nat} (w : ValidNormalizedWitness X) :
    Even (fundamentalX w.D w.pellKernel) :=
  w.pellAdmissible.2

end ValidNormalizedWitness

end Erdos364
