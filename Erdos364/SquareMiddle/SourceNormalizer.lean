import Erdos364.SquareMiddle.SourceLeafCompiler
import Erdos364.SquareMiddle.FixedPellFlankAllocation
import Erdos364.SquareMiddle.TopBranchCompiler

namespace Erdos364

/-!
# Concrete square-middle source normalizer

This is the source-facing endpoint of `PAIR-PELL-COMPLETE`.  A full
`SquareMiddle X` supplies its lower powerful-pair source; the proved
normalizer yields the unique canonical Pell datum, while the flank layer
supplies the two canonical normal forms used by the six-leaf compiler.

No shifted-flank elimination appears here.  The original right-powerful proof
is retained in `ValidNormalizedWitness.source` for that later theorem.
-/

/-- Every square-middle source produces its concrete, source-preserving
canonical Pell and flank-normal-form witness. -/
noncomputable def normalizeSquareMiddle {X : Nat}
    (h : SquareMiddle X) : ValidNormalizedWitness X := by
  have hlower : SquareMiddleLowerSource X :=
    ⟨h.1, h.center_even, h.2.1⟩
  let hdataExists : ∃! data : PairPellIndexData, data.Represents X :=
    (pairPellComplete X).mp hlower
  let data : PairPellIndexData := Classical.choose hdataExists
  have hdata : data.Represents X := (Classical.choose_spec hdataExists).1
  let flanks : SquareMiddleFlankNormalForms X :=
    Classical.choice h.exists_flankNormalForms
  let hformExists : ∃ Z : Nat,
      SquareCubeNormalForm (X ^ 2 - 1) Z data.D :=
    hdata.exists_squareSubOne_normalForm
  let Z : Nat := Classical.choose hformExists
  have hsourceForm : SquareCubeNormalForm (X ^ 2 - 1) Z data.D :=
    Classical.choose_spec hformExists
  refine
    { source := h
      pell := data
      pellAdmissible := hdata.1
      center_eq := hdata.2
      flanks := flanks
      kernel_product := ?_ }
  exact flanks.kernel_product_eq h hsourceForm

/-- The normalizer keeps the original centre exactly, not merely up to a
Pell-coordinate projection. -/
theorem normalizeSquareMiddle_reconstructCenter_eq {X : Nat}
    (h : SquareMiddle X) :
    (normalizeSquareMiddle h).reconstructCenter = X :=
  (normalizeSquareMiddle h).reconstructCenter_eq_source

/-- Source preservation for the full square-middle predicate. -/
theorem normalizeSquareMiddle_sourcePreserving {X : Nat}
    (h : SquareMiddle X) :
    SquareMiddle (normalizeSquareMiddle h).reconstructCenter :=
  (normalizeSquareMiddle h).reconstructCenter_squareMiddle

/-- The normalizer gives a genuine source-facing six-leaf cover. -/
theorem squareMiddle_sixLeafCover_from_source {X : Nat}
    (h : SquareMiddle X) :
    ∃ leaf : SquareMiddleLeaf,
      SquareMiddleLeafPred leaf (normalizeSquareMiddle h) :=
  squareMiddle_sixLeafCover (normalizeSquareMiddle h)

/-- The source-facing compiler remains deterministic. -/
theorem squareMiddleCompilerDeterministic_from_source {X : Nat}
    (h : SquareMiddle X) :
    ∃! leaf : SquareMiddleLeaf,
      SquareMiddleLeafPred leaf (normalizeSquareMiddle h) :=
  squareMiddleCompilerDeterministic (normalizeSquareMiddle h)

/-- The two top branches cover every original square-middle source after
normalization. -/
theorem squareMiddle_topBranchCover_from_source {X : Nat}
    (h : SquareMiddle X) :
    ∃ branch : SquareMiddleTopBranch,
      SquareMiddleTopBranchPred branch (normalizeSquareMiddle h) :=
  squareMiddle_topBranchCover (normalizeSquareMiddle h)

/-- The two top branches are disjoint for a source-normalized witness. -/
theorem squareMiddle_topBranchDisjoint_from_source {X : Nat}
    (h : SquareMiddle X) {left right : SquareMiddleTopBranch}
    (hleft : SquareMiddleTopBranchPred left (normalizeSquareMiddle h))
    (hright : SquareMiddleTopBranchPred right (normalizeSquareMiddle h)) :
    left = right :=
  squareMiddle_topBranchDisjoint (normalizeSquareMiddle h) hleft hright

/-- Distinct source-facing leaf claims cannot both hold for the normalized
witness constructed from a single source. -/
theorem squareMiddle_sixLeafDisjoint_from_source {X : Nat}
    (h : SquareMiddle X) {left right : SquareMiddleLeaf}
    (hleft : SquareMiddleLeafPred left (normalizeSquareMiddle h))
    (hright : SquareMiddleLeafPred right (normalizeSquareMiddle h)) :
    left = right :=
  squareMiddle_sixLeafDisjoint (normalizeSquareMiddle h) hleft hright

/-- The two flank kernels of a normalized source are fixed by the fundamental
Pell unit alone; they do not vary with the odd canonical index parameter. -/
theorem normalizeSquareMiddle_fixed_fundamental_allocation {X : Nat}
    (h : SquareMiddle X) :
    (normalizeSquareMiddle h).flanks.lowerKernel =
        fundamentalLowerKernel (normalizeSquareMiddle h).D
          (normalizeSquareMiddle h).pellKernel ∧
      (normalizeSquareMiddle h).flanks.upperKernel =
        fundamentalUpperKernel (normalizeSquareMiddle h).D
          (normalizeSquareMiddle h).pellKernel :=
  (normalizeSquareMiddle h).fixed_fundamental_allocation

end Erdos364
