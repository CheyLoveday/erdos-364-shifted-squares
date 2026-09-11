import Erdos364.SquareMiddle.PellConversion
import Erdos364.SquareMiddle.PellParity

namespace Erdos364

/-!
# Positive canonical Pell coordinates

These are the two directions that turn the selected Mathlib Pell powers into
the natural-number data used by the square-middle normalizer.  They contain
no source classification: their role is only to keep the integer-coordinate
Pell API and the positive `A²D³` normal form connected by explicit equalities.
-/

/-- The selected Pell coordinates satisfy the addition-form natural Pell
equation at every nonnegative index. -/
theorem pellX_square_eq_one_add_mul_pellY_sq
    (D : Nat) (hD : PellKernel D) (n : Nat) :
    pellX D hD n ^ 2 = 1 + D * pellY D hD n ^ 2 := by
  have h := (pellSolution D hD n).prop_x
  rw [← pellX_intCast D hD n, ← pellY_intCast D hD n] at h
  exact_mod_cast h

/-- Away from the identity exponent, the natural Pell ordinate is positive. -/
theorem pellY_pos_of_pos_index
    (D : Nat) (hD : PellKernel D) {n : Nat} (hn : 0 < n) :
    0 < pellY D hD n := by
  obtain ⟨m, hm⟩ :=
    Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [hm]
  have hy := pellSolution_y_succ_pos D hD m
  rw [← pellY_intCast D hD (m + 1)] at hy
  exact_mod_cast hy

/-- A positive ordinate forces the corresponding canonical x-coordinate to
be strictly larger than one. -/
theorem pellX_one_lt_of_pellY_pos
    (D : Nat) (hD : PellKernel D) (n : Nat)
    (hy : 0 < pellY D hD n) :
    1 < pellX D hD n := by
  have heq := pellX_square_eq_one_add_mul_pellY_sq D hD n
  have hD_pos : 0 < D := Nat.zero_lt_of_lt hD.1
  have hterm_pos : 0 < D * pellY D hD n ^ 2 :=
    Nat.mul_pos hD_pos (pow_pos hy 2)
  have hx_sq : 1 < pellX D hD n ^ 2 := by
    rw [heq]
    omega
  have hx_pos_int := pellSolution_x_pos D hD n
  rw [← pellX_intCast D hD n] at hx_pos_int
  have hx_pos : 0 < pellX D hD n := by exact_mod_cast hx_pos_int
  nlinarith

/-- A positive canonical index together with kernel divisibility produces
exactly the natural Pell data needed for the reverse normal-form conversion. -/
theorem pellCoordinates_divisibleNatPell
    (D : Nat) (hD : PellKernel D) (n : Nat)
    (hn : 0 < n) (hdiv : D ∣ pellY D hD n) :
    DivisibleNatPell D (pellX D hD n) (pellY D hD n) := by
  have hy : 0 < pellY D hD n := pellY_pos_of_pos_index D hD hn
  refine
    { X_one_lt := pellX_one_lt_of_pellY_pos D hD n hy
      Y_pos := hy
      D_one_lt := hD.1
      D_squarefree := hD.2
      equation := ?_
      D_dvd_Y := hdiv }
  simpa [Nat.add_comm] using pellX_square_eq_one_add_mul_pellY_sq D hD n

/-- The lower flank of a positive canonical Pell point is powerful whenever
the kernel divides its ordinate. -/
theorem powerfulPos_pellX_square_sub_one
    (D : Nat) (hD : PellKernel D) (n : Nat)
    (hn : 0 < n) (hdiv : D ∣ pellY D hD n) :
    PowerfulPos (pellX D hD n ^ 2 - 1) := by
  let hpell := pellCoordinates_divisibleNatPell D hD n hn hdiv
  obtain ⟨Z, hZ, _hunique⟩ :=
    hpell.existsUnique_squareSubOne_normalForm_factor
  exact powerfulPos_of_squareCubeNormalForm hZ.2

/-- A positive natural Pell datum is represented by a unique selected
fundamental-unit power at the coordinate level.  The exponent uniqueness is
provided separately by `pellX_injective`; this theorem deliberately exposes
the two concrete coordinate equalities used by source normalization. -/
theorem DivisibleNatPell.exists_pellCoordinates
    {D X Y : Nat} (h : DivisibleNatPell D X Y) :
    ∃ n : Nat,
      X = pellX D ⟨h.D_one_lt, h.D_squarefree⟩ n ∧
        Y = pellY D ⟨h.D_one_lt, h.D_squarefree⟩ n := by
  let hD : PellKernel D := ⟨h.D_one_lt, h.D_squarefree⟩
  have hxyInt :
      (X : Int) ^ 2 - (D : Int) * (Y : Int) ^ 2 = 1 := by
    have heqInt : (X : Int) ^ 2 = (D : Int) * (Y : Int) ^ 2 + 1 := by
      exact_mod_cast h.equation
    linarith
  obtain ⟨n, hn⟩ :=
    pell_positive_solution_eq_fundamental_pow hD
      (x := (X : Int)) (y := (Y : Int))
      (by exact_mod_cast (Nat.zero_lt_of_lt h.X_one_lt))
      (by exact_mod_cast h.Y_pos.le)
      hxyInt
  have hxInt := congrArg Pell.Solution₁.x hn
  have hyInt := congrArg Pell.Solution₁.y hn
  simp only [Pell.Solution₁.x_mk] at hxInt
  simp only [Pell.Solution₁.y_mk] at hyInt
  rw [← pellX_intCast D hD n] at hxInt
  rw [← pellY_intCast D hD n] at hyInt
  refine ⟨n, ?_, ?_⟩
  · exact_mod_cast hxInt
  · exact_mod_cast hyInt

end Erdos364
