import Erdos364.SquareMiddle.NormalForm
import Mathlib.Algebra.Ring.Int.Parity

namespace Erdos364

/-- A positive natural Pell solution carrying exactly the divisibility and
kernel hypotheses produced by the square-middle lower normal form. -/
structure DivisibleNatPell (D X Y : Nat) : Prop where
  X_one_lt : 1 < X
  Y_pos : 0 < Y
  D_one_lt : 1 < D
  D_squarefree : _root_.Squarefree D
  equation : X ^ 2 = D * Y ^ 2 + 1
  D_dvd_Y : D ∣ Y

/-- A squarefree natural greater than one cannot itself be a square. -/
theorem not_isSquare_of_squarefree_one_lt {D : Nat}
    (hD_squarefree : _root_.Squarefree D) (hD : 1 < D) :
    ¬ IsSquare D := by
  rintro ⟨r, hr⟩
  have hr_unit : IsUnit r := hD_squarefree r (by rw [hr])
  have hr_one : r = 1 := Nat.isUnit_iff.mp hr_unit
  rw [hr_one] at hr
  simp at hr
  omega

/-- The preceding nonsquare result in the integer coefficient type expected
by Mathlib's Pell API. -/
theorem not_isSquare_intCast_of_squarefree_one_lt {D : Nat}
    (hD_squarefree : _root_.Squarefree D) (hD : 1 < D) :
    ¬ IsSquare (D : Int) := by
  simpa only [Int.isSquare_natCast_iff] using
    not_isSquare_of_squarefree_one_lt hD_squarefree hD

/-- The squarefree kernel in a normal form for `X ^ 2 - 1` is nontrivial
when `X` is greater than one. -/
theorem squareSubOne_normalForm_kernel_one_lt {X Z D : Nat}
    (hX : 1 < X)
    (hform : SquareCubeNormalForm (X ^ 2 - 1) Z D) :
    1 < D := by
  have hD_ne_one : D ≠ 1 := by
    intro hD
    have hsub : X ^ 2 - 1 = Z ^ 2 := by
      simpa [hD] using hform.2.2.1
    have hX_pos : 0 < X := by omega
    have hsquare_pos : 0 < X ^ 2 := pow_pos hX_pos 2
    have heq : X ^ 2 = Z ^ 2 + 1 := by omega
    have hZ_lt_X : Z < X := by
      by_contra hnot
      have hX_le_Z : X ≤ Z := Nat.le_of_not_gt hnot
      have hpowers : X ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left hX_le_Z 2
      omega
    have hZ_succ_le_X : Z + 1 ≤ X := by omega
    have hpowers : (Z + 1) ^ 2 ≤ X ^ 2 :=
      Nat.pow_le_pow_left hZ_succ_le_X 2
    nlinarith
  have hD_pos : 0 < D := hform.2.1
  omega

/-- Forward algebraic conversion. The canonical lower normal form
`X² - 1 = Z²D³` produces the Pell ordinate `Y = DZ`, and retains both
`D ∣ Y` and the canonical squarefree kernel. -/
theorem squareSubOne_normalForm_to_divisibleNatPell {X Z D : Nat}
    (hX : 1 < X)
    (hform : SquareCubeNormalForm (X ^ 2 - 1) Z D) :
    DivisibleNatPell D X (D * Z) := by
  have hD_one_lt : 1 < D := squareSubOne_normalForm_kernel_one_lt hX hform
  refine
    { X_one_lt := hX
      Y_pos := Nat.mul_pos hform.2.1 hform.1
      D_one_lt := hD_one_lt
      D_squarefree := hform.kernel_squarefree
      equation := ?_
      D_dvd_Y := ⟨Z, rfl⟩ }
  have hX_pos : 0 < X := by omega
  have hsquare_pos : 0 < X ^ 2 := pow_pos hX_pos 2
  calc
    X ^ 2 = (X ^ 2 - 1) + 1 := by omega
    _ = Z ^ 2 * D ^ 3 + 1 := by rw [hform.2.2.1]
    _ = D * (D * Z) ^ 2 + 1 := by ring

/-- Reverse algebraic conversion. A positive squarefree Pell solution with
`D ∣ Y` has a unique positive quotient `Z` and reconstructs the canonical
lower normal form `X² - 1 = Z²D³`. -/
theorem DivisibleNatPell.existsUnique_squareSubOne_normalForm_factor
    {D X Y : Nat} (h : DivisibleNatPell D X Y) :
    ∃! Z : Nat,
      Y = D * Z ∧ SquareCubeNormalForm (X ^ 2 - 1) Z D := by
  obtain ⟨Z, hY⟩ := h.D_dvd_Y
  have hZ_pos : 0 < Z := by
    have hY_pos := h.Y_pos
    by_contra hnot
    have hZ_zero : Z = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hZ_zero, mul_zero] at hY
    omega
  have hvalue : X ^ 2 - 1 = Z ^ 2 * D ^ 3 := by
    have hequation := h.equation
    calc
      X ^ 2 - 1 = D * Y ^ 2 := by omega
      _ = D * (D * Z) ^ 2 := by rw [hY]
      _ = Z ^ 2 * D ^ 3 := by ring
  have hform : SquareCubeNormalForm (X ^ 2 - 1) Z D :=
    squareCubeNormalForm_of_eq_sq_mul_cube
      hZ_pos (by exact Nat.zero_lt_of_lt h.D_one_lt) hvalue h.D_squarefree
  refine ⟨Z, ⟨hY, hform⟩, ?_⟩
  intro W hW
  apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt h.D_one_lt)
  calc
    D * W = Y := hW.1.symm
    _ = D * Z := hY

/-- Exact direct equivalence for a fixed quotient `Z`. This is the algebraic
SM-03 interface consumed by later Pell-coordinate work. -/
theorem squareSubOne_normalForm_iff_divisibleNatPell (X D Z : Nat) :
    (1 < X ∧ SquareCubeNormalForm (X ^ 2 - 1) Z D) ↔
      DivisibleNatPell D X (D * Z) := by
  constructor
  · rintro ⟨hX, hform⟩
    exact squareSubOne_normalForm_to_divisibleNatPell hX hform
  · intro hpell
    refine ⟨hpell.X_one_lt, ?_⟩
    obtain ⟨W, hW, _hunique⟩ :=
      hpell.existsUnique_squareSubOne_normalForm_factor
    have hW_eq : W = Z := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hpell.D_one_lt)
      exact hW.1.symm
    simpa [hW_eq] using hW.2

end Erdos364
