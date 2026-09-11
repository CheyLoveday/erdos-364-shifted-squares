import Erdos364.SquareMiddle.Normalization
import Erdos364.SquareMiddle.LeafCompiler

namespace Erdos364

/-!
# Source-facing six-leaf compiler

Unlike the historical label-only vocabulary, this module routes a concrete
`ValidNormalizedWitness`.  Each leaf predicate retains the actual mod-eight
and flank-kernel conditions; the cover theorem therefore says something about
a square-middle source witness, rather than merely that a total function has
an output.

This compiler is deliberately independent of the still-open shifted `+1`
eliminator.  It classifies the lower powerful-pair data only.
-/

/-- The arithmetic predicate attached to each of the six square-middle leaf
names.  The two named square leaves use literal kernel equality to `1`; the
remaining leaves retain the nontrivial-kernel condition. -/
def SquareMiddleLeafPred {X : Nat}
    (leaf : SquareMiddleLeaf) (w : ValidNormalizedWitness X) : Prop :=
  match leaf with
  | .sm0UpperSquare =>
      X % 8 = 0 ∧ w.flanks.lowerKernel % 8 = 7 ∧
        w.flanks.upperKernel = 1
  | .sm0TwoKernel =>
      X % 8 = 0 ∧ w.flanks.lowerKernel % 8 = 7 ∧
        1 < w.flanks.upperKernel ∧ w.flanks.upperKernel % 8 = 1
  | .sm2LowerSquare =>
      X % 8 = 2 ∧ w.flanks.lowerKernel = 1 ∧
        w.flanks.upperKernel % 8 = 3
  | .sm2TwoKernel =>
      X % 8 = 2 ∧ 1 < w.flanks.lowerKernel ∧
        w.flanks.lowerKernel % 8 = 1 ∧ w.flanks.upperKernel % 8 = 3
  | .sm4TwoKernel =>
      X % 8 = 4 ∧ w.flanks.lowerKernel % 8 = 3 ∧
        w.flanks.upperKernel % 8 = 5
  | .sm6TwoKernel =>
      X % 8 = 6 ∧ w.flanks.lowerKernel % 8 = 5 ∧
        w.flanks.upperKernel % 8 = 7

/-- The executable finite routing function on an already-valid source
normalization.  The final fallback is reached only at the `6 mod 8` source
case, as proved by `compileSquareMiddleLeaf_spec`. -/
def compileSquareMiddleLeaf {X : Nat}
    (w : ValidNormalizedWitness X) : SquareMiddleLeaf :=
  if X % 8 = 0 then
    if w.flanks.upperKernel = 1 then .sm0UpperSquare else .sm0TwoKernel
  else if X % 8 = 2 then
    if w.flanks.lowerKernel = 1 then .sm2LowerSquare else .sm2TwoKernel
  else if X % 8 = 4 then .sm4TwoKernel else .sm6TwoKernel

private theorem upper_kernel_one_or_one_lt {X : Nat}
    (w : ValidNormalizedWitness X) :
    w.flanks.upperKernel = 1 ∨ 1 < w.flanks.upperKernel := by
  by_cases h : w.flanks.upperKernel = 1
  · exact Or.inl h
  · right
    have hpos : 0 < w.flanks.upperKernel := w.upper_form.2.1
    omega

private theorem lower_kernel_one_or_one_lt {X : Nat}
    (w : ValidNormalizedWitness X) :
    w.flanks.lowerKernel = 1 ∨ 1 < w.flanks.lowerKernel := by
  by_cases h : w.flanks.lowerKernel = 1
  · exact Or.inl h
  · right
    have hpos : 0 < w.flanks.lowerKernel := w.lower_form.2.1
    omega

/-- The compiler output satisfies its literal arithmetic leaf predicate. -/
theorem compileSquareMiddleLeaf_spec {X : Nat}
    (w : ValidNormalizedWitness X) :
    SquareMiddleLeafPred (compileSquareMiddleLeaf w) w := by
  rcases w.flanks.kernel_mod_eight_table w.source with h0 | h2 | h4 | h6
  · rcases upper_kernel_one_or_one_lt w with hu | hu
    · simp [compileSquareMiddleLeaf, h0.1, hu, SquareMiddleLeafPred,
        h0.2.1]
    · simp [compileSquareMiddleLeaf, h0.1, hu, SquareMiddleLeafPred,
        h0.2.1, h0.2.2, show w.flanks.upperKernel ≠ 1 by omega]
  · rcases lower_kernel_one_or_one_lt w with hl | hl
    · simp [compileSquareMiddleLeaf, h2.1, hl, SquareMiddleLeafPred,
        h2.2.2]
    · simp [compileSquareMiddleLeaf, h2.1, hl, SquareMiddleLeafPred,
        h2.2.1, h2.2.2, show w.flanks.lowerKernel ≠ 1 by omega]
  · simp [compileSquareMiddleLeaf, h4.1, SquareMiddleLeafPred,
      h4.2.1, h4.2.2]
  · simp [compileSquareMiddleLeaf, h6.1, SquareMiddleLeafPred,
      h6.2.1, h6.2.2]

/-- Any satisfied leaf predicate is exactly the compiler output.  This is the
non-definitional half of the exhaustive/disjoint compiler result. -/
theorem compileSquareMiddleLeaf_eq_of_pred {X : Nat}
    (w : ValidNormalizedWitness X) {leaf : SquareMiddleLeaf}
    (h : SquareMiddleLeafPred leaf w) :
    compileSquareMiddleLeaf w = leaf := by
  cases leaf with
  | sm0UpperSquare =>
      simp only [SquareMiddleLeafPred] at h
      simp [compileSquareMiddleLeaf, h.1, h.2.2]
  | sm0TwoKernel =>
      simp only [SquareMiddleLeafPred] at h
      have hne : w.flanks.upperKernel ≠ 1 := by omega
      simp [compileSquareMiddleLeaf, h.1, hne]
  | sm2LowerSquare =>
      simp only [SquareMiddleLeafPred] at h
      simp [compileSquareMiddleLeaf, h.1, h.2.1]
  | sm2TwoKernel =>
      simp only [SquareMiddleLeafPred] at h
      have hne : w.flanks.lowerKernel ≠ 1 := by omega
      simp [compileSquareMiddleLeaf, h.1, hne]
  | sm4TwoKernel =>
      simp only [SquareMiddleLeafPred] at h
      simp [compileSquareMiddleLeaf, h.1]
  | sm6TwoKernel =>
      simp only [SquareMiddleLeafPred] at h
      have hnot0 : X % 8 ≠ 0 := by omega
      have hnot2 : X % 8 ≠ 2 := by omega
      have hnot4 : X % 8 ≠ 4 := by omega
      simp [compileSquareMiddleLeaf, hnot0, hnot2, hnot4]

/-- Every valid normalized square-middle source enters a six-leaf predicate. -/
theorem squareMiddle_sixLeafCover {X : Nat}
    (w : ValidNormalizedWitness X) :
    ∃ leaf : SquareMiddleLeaf, SquareMiddleLeafPred leaf w :=
  ⟨compileSquareMiddleLeaf w, compileSquareMiddleLeaf_spec w⟩

/-- The six source-facing leaf predicates are disjoint. -/
theorem squareMiddle_sixLeafDisjoint {X : Nat}
    (w : ValidNormalizedWitness X) {left right : SquareMiddleLeaf}
    (hleft : SquareMiddleLeafPred left w)
    (hright : SquareMiddleLeafPred right w) :
    left = right := by
  have hleft' := compileSquareMiddleLeaf_eq_of_pred w hleft
  have hright' := compileSquareMiddleLeaf_eq_of_pred w hright
  exact hleft'.symm.trans hright'

/-- Routing is deterministic as an immediate source-facing consequence of
cover plus disjointness. -/
theorem squareMiddleCompilerDeterministic {X : Nat}
    (w : ValidNormalizedWitness X) :
    ∃! leaf : SquareMiddleLeaf, SquareMiddleLeafPred leaf w := by
  refine ⟨compileSquareMiddleLeaf w, compileSquareMiddleLeaf_spec w, ?_⟩
  intro other hother
  exact (compileSquareMiddleLeaf_eq_of_pred w hother).symm

/-- The compiler preserves the original square-middle source through the
stored normalized witness, so routing cannot silently change the centre. -/
theorem squareMiddleCompilerSourcePreserving {X : Nat}
    (w : ValidNormalizedWitness X) :
    SquareMiddle w.reconstructCenter :=
  w.reconstructCenter_squareMiddle

/-- The top branch inferred from the compiler agrees with the declared leaf
metadata. -/
theorem compileSquareMiddleLeaf_topBranch {X : Nat}
    (w : ValidNormalizedWitness X) :
    (compileSquareMiddleLeaf w).topBranch =
      match X % 8 with
      | 0 | 4 => .d7mod8
      | _ => .d3mod8 := by
  rcases w.flanks.kernel_mod_eight_table w.source with h0 | h2 | h4 | h6
  · rcases upper_kernel_one_or_one_lt w with hu | hu
    · simp [compileSquareMiddleLeaf, h0.1, hu, SquareMiddleLeaf.topBranch]
    · have hne : w.flanks.upperKernel ≠ 1 := by omega
      simp [compileSquareMiddleLeaf, h0.1, hne, SquareMiddleLeaf.topBranch]
  · rcases lower_kernel_one_or_one_lt w with hl | hl
    · simp [compileSquareMiddleLeaf, h2.1, hl, SquareMiddleLeaf.topBranch]
    · have hne : w.flanks.lowerKernel ≠ 1 := by omega
      simp [compileSquareMiddleLeaf, h2.1, hne, SquareMiddleLeaf.topBranch]
  · simp [compileSquareMiddleLeaf, h4.1, SquareMiddleLeaf.topBranch]
  · simp [compileSquareMiddleLeaf, h6.1, SquareMiddleLeaf.topBranch]

end Erdos364
