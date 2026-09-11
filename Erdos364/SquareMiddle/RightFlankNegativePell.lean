import Erdos364.SquareMiddle.NormalForm

namespace Erdos364

/-!
# Right-flank negative-Pell conversion

This module records only the algebraic conversion forced by a powerful right
flank.  It does not classify solutions of a negative Pell equation and does
not assert that the right flank is impossible.

The equation is written additively as `K * W ^ 2 = X ^ 2 + 1`.  This avoids
truncated subtraction in `Nat`, while retaining the usual equation
`X ^ 2 - K * W ^ 2 = -1` after passage to the integers.
-/

/-- A positive natural solution of the right-flank negative-Pell equation,
carrying exactly the squarefree-kernel and divisibility data supplied by an
`A²K³` normal form. -/
structure DivisibleNatNegativePell (K X W : Nat) : Prop where
  X_one_lt : 1 < X
  W_pos : 0 < W
  K_pos : 0 < K
  K_squarefree : _root_.Squarefree K
  equation : K * W ^ 2 = X ^ 2 + 1
  K_dvd_W : K ∣ W

/-- Forward algebraic conversion.  The upper normal form
`X² + 1 = V²K³` produces the negative-Pell ordinate `W = KV` and retains
both `K ∣ W` and the canonical squarefree kernel. -/
theorem squareAddOne_normalForm_to_divisibleNatNegativePell
    {X V K : Nat} (hX : 1 < X)
    (hform : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    DivisibleNatNegativePell K X (K * V) := by
  refine
    { X_one_lt := hX
      W_pos := Nat.mul_pos hform.2.1 hform.1
      K_pos := hform.2.1
      K_squarefree := hform.kernel_squarefree
      equation := ?_
      K_dvd_W := ⟨V, rfl⟩ }
  calc
    K * (K * V) ^ 2 = V ^ 2 * K ^ 3 := by ring
    _ = X ^ 2 + 1 := hform.2.2.1.symm

/-- Reverse algebraic conversion.  A positive squarefree negative-Pell
solution with `K ∣ W` has a unique positive quotient `V` and reconstructs
the same upper `A²K³` normal form. -/
theorem DivisibleNatNegativePell.existsUnique_squareAddOne_normalForm_factor
    {K X W : Nat} (h : DivisibleNatNegativePell K X W) :
    ∃! V : Nat,
      W = K * V ∧ SquareCubeNormalForm (X ^ 2 + 1) V K := by
  obtain ⟨V, hW⟩ := h.K_dvd_W
  have hV_pos : 0 < V := by
    by_contra hnot
    have hV_zero : V = 0 := Nat.eq_zero_of_not_pos hnot
    have hW_zero : W = 0 := by
      simpa [hV_zero] using hW
    exact (Nat.ne_of_gt h.W_pos) hW_zero
  have hvalue : X ^ 2 + 1 = V ^ 2 * K ^ 3 := by
    calc
      X ^ 2 + 1 = K * W ^ 2 := h.equation.symm
      _ = K * (K * V) ^ 2 := by rw [hW]
      _ = V ^ 2 * K ^ 3 := by ring
  have hform : SquareCubeNormalForm (X ^ 2 + 1) V K :=
    squareCubeNormalForm_of_eq_sq_mul_cube
      hV_pos h.K_pos hvalue h.K_squarefree
  refine ⟨V, ⟨hW, hform⟩, ?_⟩
  intro V' hV'
  apply Nat.eq_of_mul_eq_mul_left h.K_pos
  calc
    K * V' = W := hV'.1.symm
    _ = K * V := hW

/-- Exact direct equivalence for a retained quotient `V`.  This is the
subtraction-safe right-flank conversion interface used by canonical
counterexample packages. -/
theorem squareAddOne_normalForm_iff_divisibleNatNegativePell
    (X K V : Nat) :
    (1 < X ∧ SquareCubeNormalForm (X ^ 2 + 1) V K) ↔
      DivisibleNatNegativePell K X (K * V) := by
  constructor
  · rintro ⟨hX, hform⟩
    exact squareAddOne_normalForm_to_divisibleNatNegativePell hX hform
  · intro hnegative
    refine ⟨hnegative.X_one_lt, ?_⟩
    obtain ⟨V', hV', _hunique⟩ :=
      hnegative.existsUnique_squareAddOne_normalForm_factor
    have hV'_eq : V' = V := by
      apply Nat.eq_of_mul_eq_mul_left hnegative.K_pos
      exact hV'.1.symm
    simpa [hV'_eq] using hV'.2

end Erdos364
