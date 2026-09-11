import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype

namespace Erdos364

/-!
# Square-middle leaf vocabulary

This module records only the finite names used by the eventual square-middle
compiler.  In particular, it does **not** define a classifier, state source
coverage, or connect a residue label to a natural number.  Those arithmetic
claims belong to the later normalization and allocation theorems.
-/

/-- The two mod-eight branches named by the square-middle allocation. -/
inductive SquareMiddleTopBranch : Type
  | d3mod8
  | d7mod8
  deriving DecidableEq, Repr

/-- The four even residue labels used by the six-leaf allocation. -/
inductive SquareMiddleResidue8 : Type
  | r0
  | r2
  | r4
  | r6
  deriving DecidableEq, Repr

/-- Whether a leaf name records a square flank or two nontrivial kernels. -/
inductive SquareMiddleKernelKind : Type
  | squareFlank
  | twoKernel
  deriving DecidableEq, Repr

/-- Which flank is square in a leaf whose kernel kind is `squareFlank`. -/
inductive SquareMiddleFlank : Type
  | lower
  | upper
  deriving DecidableEq, Repr

/-- The six named leaves in the proposed square-middle allocation.

These constructors are labels only.  The later arithmetic compiler must prove
that a normalized source belongs to one of them, and that it belongs to no
other leaf. -/
inductive SquareMiddleLeaf : Type
  | sm0UpperSquare
  | sm0TwoKernel
  | sm2LowerSquare
  | sm2TwoKernel
  | sm4TwoKernel
  | sm6TwoKernel
  deriving DecidableEq, Repr, Fintype

/-- The top branch attached to each leaf name. -/
def SquareMiddleLeaf.topBranch : SquareMiddleLeaf → SquareMiddleTopBranch
  | .sm0UpperSquare | .sm0TwoKernel | .sm4TwoKernel => .d7mod8
  | .sm2LowerSquare | .sm2TwoKernel | .sm6TwoKernel => .d3mod8

/-- The kernel shape named by each leaf. -/
def SquareMiddleLeaf.kernelKind : SquareMiddleLeaf → SquareMiddleKernelKind
  | .sm0UpperSquare | .sm2LowerSquare => .squareFlank
  | .sm0TwoKernel | .sm2TwoKernel | .sm4TwoKernel | .sm6TwoKernel => .twoKernel

/-- The named square flank, when the leaf has one. -/
def SquareMiddleLeaf.squareFlank? : SquareMiddleLeaf → Option SquareMiddleFlank
  | .sm0UpperSquare => some .upper
  | .sm2LowerSquare => some .lower
  | .sm0TwoKernel | .sm2TwoKernel | .sm4TwoKernel | .sm6TwoKernel => none

/-- The six-leaf vocabulary has exactly six constructors. -/
theorem squareMiddleLeaf_card : Fintype.card SquareMiddleLeaf = 6 := by
  decide

end Erdos364
