import Erdos364.SquareMiddle.SourceLeafCompiler

namespace Erdos364

/-!
# Source-facing top-branch compiler

The six-leaf compiler refines two genuine arithmetic top branches.  This
module exports their predicates, cover, disjointness, and the corresponding
kernel residues, rather than leaving those facts implicit in the leaf table.
-/

/-- The two coarse branches, retaining both the center residue and the
canonical lower-Pell kernel residue. -/
def SquareMiddleTopBranchPred {X : Nat}
    (branch : SquareMiddleTopBranch) (w : ValidNormalizedWitness X) : Prop :=
  match branch with
  | .d3mod8 =>
      (X % 8 = 2 ∨ X % 8 = 6) ∧ w.D % 8 = 3
  | .d7mod8 =>
      (X % 8 = 0 ∨ X % 8 = 4) ∧ w.D % 8 = 7

/-- The coarse branch obtained from the source-facing six-leaf compiler. -/
def compileSquareMiddleTopBranch {X : Nat}
    (w : ValidNormalizedWitness X) : SquareMiddleTopBranch :=
  (compileSquareMiddleLeaf w).topBranch

private theorem kernel_mod_eight_from_product {X : Nat}
    (w : ValidNormalizedWitness X)
    {r s t : Nat} (hlower : w.flanks.lowerKernel % 8 = r)
    (hupper : w.flanks.upperKernel % 8 = s)
    (ht : (r * s) % 8 = t) :
    w.D % 8 = t := by
  rw [← w.flank_kernel_product, Nat.mul_mod, hlower, hupper]
  exact ht

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

/-- The compiler output satisfies its two-branch arithmetic predicate. -/
theorem compileSquareMiddleTopBranch_spec {X : Nat}
    (w : ValidNormalizedWitness X) :
    SquareMiddleTopBranchPred (compileSquareMiddleTopBranch w) w := by
  rcases w.flanks.kernel_mod_eight_table w.source with h0 | h2 | h4 | h6
  · have hDmod : w.D % 8 = 7 :=
      kernel_mod_eight_from_product w h0.2.1 h0.2.2 (by decide)
    rcases upper_kernel_one_or_one_lt w with hu | hu
    · simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h0.1, hu,
        SquareMiddleTopBranchPred, SquareMiddleLeaf.topBranch, hDmod]
    · have hne : w.flanks.upperKernel ≠ 1 := by omega
      simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h0.1, hne,
        SquareMiddleTopBranchPred, SquareMiddleLeaf.topBranch, hDmod]
  · have hDmod : w.D % 8 = 3 :=
      kernel_mod_eight_from_product w h2.2.1 h2.2.2 (by decide)
    rcases lower_kernel_one_or_one_lt w with hl | hl
    · simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h2.1, hl,
        SquareMiddleTopBranchPred, SquareMiddleLeaf.topBranch, hDmod]
    · have hne : w.flanks.lowerKernel ≠ 1 := by omega
      simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h2.1, hne,
        SquareMiddleTopBranchPred, SquareMiddleLeaf.topBranch, hDmod]
  · have hDmod : w.D % 8 = 7 :=
      kernel_mod_eight_from_product w h4.2.1 h4.2.2 (by decide)
    simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h4.1,
      SquareMiddleTopBranchPred, SquareMiddleLeaf.topBranch, hDmod]
  · have hDmod : w.D % 8 = 3 :=
      kernel_mod_eight_from_product w h6.2.1 h6.2.2 (by decide)
    simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h6.1,
      SquareMiddleTopBranchPred, SquareMiddleLeaf.topBranch, hDmod]

/-- Any satisfied top-branch predicate equals the compiler output. -/
theorem compileSquareMiddleTopBranch_eq_of_pred {X : Nat}
    (w : ValidNormalizedWitness X) {branch : SquareMiddleTopBranch}
    (h : SquareMiddleTopBranchPred branch w) :
    compileSquareMiddleTopBranch w = branch := by
  cases branch with
  | d3mod8 =>
      simp only [SquareMiddleTopBranchPred] at h
      rcases h.1 with h2 | h6
      · rcases lower_kernel_one_or_one_lt w with hl | hl
        · simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h2, hl,
            SquareMiddleLeaf.topBranch]
        · have hne : w.flanks.lowerKernel ≠ 1 := by omega
          simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h2, hne,
            SquareMiddleLeaf.topBranch]
      · simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h6,
          SquareMiddleLeaf.topBranch]
  | d7mod8 =>
      simp only [SquareMiddleTopBranchPred] at h
      rcases h.1 with h0 | h4
      · rcases upper_kernel_one_or_one_lt w with hu | hu
        · simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h0, hu,
            SquareMiddleLeaf.topBranch]
        · have hne : w.flanks.upperKernel ≠ 1 := by omega
          simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h0, hne,
            SquareMiddleLeaf.topBranch]
      · simp [compileSquareMiddleTopBranch, compileSquareMiddleLeaf, h4,
          SquareMiddleLeaf.topBranch]

/-- The two source-facing top branches cover every valid normalized witness. -/
theorem squareMiddle_topBranchCover {X : Nat}
    (w : ValidNormalizedWitness X) :
    ∃ branch : SquareMiddleTopBranch, SquareMiddleTopBranchPred branch w :=
  ⟨compileSquareMiddleTopBranch w, compileSquareMiddleTopBranch_spec w⟩

/-- The two source-facing top branches are disjoint. -/
theorem squareMiddle_topBranchDisjoint {X : Nat}
    (w : ValidNormalizedWitness X) {left right : SquareMiddleTopBranch}
    (hleft : SquareMiddleTopBranchPred left w)
    (hright : SquareMiddleTopBranchPred right w) :
    left = right := by
  have hleft' := compileSquareMiddleTopBranch_eq_of_pred w hleft
  have hright' := compileSquareMiddleTopBranch_eq_of_pred w hright
  exact hleft'.symm.trans hright'

/-- The top-branch compiler is deterministic. -/
theorem squareMiddleTopBranchCompilerDeterministic {X : Nat}
    (w : ValidNormalizedWitness X) :
    ∃! branch : SquareMiddleTopBranch, SquareMiddleTopBranchPred branch w := by
  refine ⟨compileSquareMiddleTopBranch w, compileSquareMiddleTopBranch_spec w, ?_⟩
  intro other hother
  exact (compileSquareMiddleTopBranch_eq_of_pred w hother).symm

/-- Named residue consequences for consumers which need only the top branch. -/
theorem squareMiddle_d3mod8_kernel_residue {X : Nat}
    (w : ValidNormalizedWitness X)
    (h : SquareMiddleTopBranchPred .d3mod8 w) :
    w.D % 8 = 3 :=
  h.2

theorem squareMiddle_d7mod8_kernel_residue {X : Nat}
    (w : ValidNormalizedWitness X)
    (h : SquareMiddleTopBranchPred .d7mod8 w) :
    w.D % 8 = 7 :=
  h.2

end Erdos364
