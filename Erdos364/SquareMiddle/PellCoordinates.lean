import Erdos364.SquareMiddle.NormalForm
import Mathlib.NumberTheory.Pell

namespace Erdos364

/-- The kernel conditions needed to invoke Mathlib's norm-one Pell theory. -/
def PellKernel (D : Nat) : Prop :=
  1 < D ∧ _root_.Squarefree D

/-- A squarefree natural strictly larger than one is not a square. -/
theorem pellKernel_not_isSquare_nat {D : Nat} (hD : PellKernel D) :
    ¬ IsSquare D := by
  rintro ⟨s, hs⟩
  have hus : IsUnit s := hD.2 s (by
    simp [← hs])
  have hs_one : s = 1 := Nat.isUnit_iff.mp hus
  rw [hs_one] at hs
  have hD_one : D = 1 := by simpa using hs
  exact (Nat.ne_of_gt hD.1) hD_one

/-- The integer cast of a Pell kernel is nonsquare. -/
theorem pellKernel_not_isSquare_int {D : Nat} (hD : PellKernel D) :
    ¬ IsSquare (D : Int) := by
  rw [Int.isSquare_natCast_iff]
  exact pellKernel_not_isSquare_nat hD

/-- A selected positive fundamental norm-one Pell solution for a kernel. -/
noncomputable def fundamentalPell (D : Nat) (hD : PellKernel D) :
    Pell.Solution₁ (D : Int) :=
  Classical.choose <|
    Pell.IsFundamental.exists_of_not_isSquare
      (by exact_mod_cast (Nat.zero_lt_of_lt hD.1))
      (pellKernel_not_isSquare_int hD)

/-- The selected solution really is fundamental. -/
theorem fundamentalPell_isFundamental (D : Nat) (hD : PellKernel D) :
    Pell.IsFundamental (fundamentalPell D hD) :=
  Classical.choose_spec <|
    Pell.IsFundamental.exists_of_not_isSquare
      (by exact_mod_cast (Nat.zero_lt_of_lt hD.1))
      (pellKernel_not_isSquare_int hD)

/-- The positive natural coordinates of the fundamental unit. -/
noncomputable def fundamentalX (D : Nat) (hD : PellKernel D) : Nat :=
  Int.toNat (fundamentalPell D hD).x

noncomputable def fundamentalY (D : Nat) (hD : PellKernel D) : Nat :=
  Int.toNat (fundamentalPell D hD).y

theorem fundamentalX_intCast (D : Nat) (hD : PellKernel D) :
    (fundamentalX D hD : Int) = (fundamentalPell D hD).x := by
  unfold fundamentalX
  exact Int.toNat_of_nonneg (fundamentalPell_isFundamental D hD).x_pos.le

theorem fundamentalY_intCast (D : Nat) (hD : PellKernel D) :
    (fundamentalY D hD : Int) = (fundamentalPell D hD).y := by
  unfold fundamentalY
  exact Int.toNat_of_nonneg (fundamentalPell_isFundamental D hD).2.1.le

theorem fundamentalX_one_lt (D : Nat) (hD : PellKernel D) :
    1 < fundamentalX D hD := by
  have h := (fundamentalPell_isFundamental D hD).1
  rw [← fundamentalX_intCast D hD] at h
  exact_mod_cast h

theorem fundamentalY_pos (D : Nat) (hD : PellKernel D) :
    0 < fundamentalY D hD := by
  have h := (fundamentalPell_isFundamental D hD).2.1
  rw [← fundamentalY_intCast D hD] at h
  exact_mod_cast h

/-- The fundamental coordinates satisfy the positive natural Pell equation. -/
theorem fundamental_pell_equation (D : Nat) (hD : PellKernel D) :
    fundamentalX D hD ^ 2 - D * fundamentalY D hD ^ 2 = 1 := by
  have h := (fundamentalPell D hD).prop_x
  rw [← fundamentalX_intCast D hD, ← fundamentalY_intCast D hD] at h
  have hnat : fundamentalX D hD ^ 2 = 1 + D * fundamentalY D hD ^ 2 := by
    exact_mod_cast h
  omega

/-- Natural nonnegative powers of the selected fundamental solution, kept in
integer coordinates so that the Mathlib Pell API remains directly usable. -/
noncomputable def pellSolution (D : Nat) (hD : PellKernel D) (n : Nat) :
    Pell.Solution₁ (D : Int) :=
  fundamentalPell D hD ^ n

/-- The canonical Pell `x` coordinate. -/
noncomputable def pellX (D : Nat) (hD : PellKernel D) (n : Nat) : Nat :=
  Int.toNat (pellSolution D hD n).x

/-- The canonical Pell `y` coordinate. -/
noncomputable def pellY (D : Nat) (hD : PellKernel D) (n : Nat) : Nat :=
  Int.toNat (pellSolution D hD n).y

/-- Powers of a positive fundamental solution have positive `x` coordinate. -/
theorem pellSolution_x_pos (D : Nat) (hD : PellKernel D) (n : Nat) :
    0 < (pellSolution D hD n).x := by
  exact Pell.Solution₁.x_pow_pos (fundamentalPell_isFundamental D hD).x_pos n

/-- Natural powers of the positive fundamental solution have nonnegative
`y` coordinate; it is positive away from the identity power. -/
theorem pellSolution_y_nonneg (D : Nat) (hD : PellKernel D) (n : Nat) :
    0 ≤ (pellSolution D hD n).y := by
  cases n with
  | zero => simp [pellSolution]
  | succ n =>
      exact (Pell.Solution₁.y_pow_succ_pos
        (fundamentalPell_isFundamental D hD).x_pos
        (fundamentalPell_isFundamental D hD).2.1 n).le

theorem pellSolution_y_succ_pos (D : Nat) (hD : PellKernel D) (n : Nat) :
    0 < (pellSolution D hD (n + 1)).y := by
  simpa [pellSolution] using
    Pell.Solution₁.y_pow_succ_pos
      (fundamentalPell_isFundamental D hD).x_pos
      (fundamentalPell_isFundamental D hD).2.1 n

/-- The integer and natural versions of the `x` coordinate agree. -/
theorem pellX_intCast (D : Nat) (hD : PellKernel D) (n : Nat) :
    (pellX D hD n : Int) = (pellSolution D hD n).x := by
  unfold pellX
  exact Int.toNat_of_nonneg (pellSolution_x_pos D hD n).le

/-- The integer and natural versions of the `y` coordinate agree. -/
theorem pellY_intCast (D : Nat) (hD : PellKernel D) (n : Nat) :
    (pellY D hD n : Int) = (pellSolution D hD n).y := by
  unfold pellY
  exact Int.toNat_of_nonneg (pellSolution_y_nonneg D hD n)

/-- The zeroth Pell coordinates are the identity solution. -/
theorem pellX_zero (D : Nat) (hD : PellKernel D) : pellX D hD 0 = 1 := by
  unfold pellX pellSolution
  simp

/-- The zeroth Pell `y` coordinate vanishes. -/
theorem pellY_zero (D : Nat) (hD : PellKernel D) : pellY D hD 0 = 0 := by
  unfold pellY pellSolution
  simp

/-- Every positive Pell solution is a nonnegative power of the selected
fundamental solution. This pins the exact Mathlib completeness interface used
by the source normalizer. -/
theorem pell_positive_solution_eq_fundamental_pow {D : Nat} (hD : PellKernel D)
    {x y : Int} (hx : 0 < x) (hy : 0 ≤ y)
    (hxy : x ^ 2 - (D : Int) * y ^ 2 = 1) :
    ∃ n : Nat, Pell.Solution₁.mk x y hxy = pellSolution D hD n := by
  exact (fundamentalPell_isFundamental D hD).eq_pow_of_nonneg hx hy

/-- Distinct nonnegative exponents have distinct Pell `y` coordinates. -/
theorem pellSolution_y_strictMono (D : Nat) (hD : PellKernel D) :
    StrictMono fun n : Nat => (pellSolution D hD n).y := by
  intro m n hmn
  have hmn_int : (m : Int) < (n : Int) := by exact_mod_cast hmn
  simpa [pellSolution, zpow_natCast] using
    (fundamentalPell_isFundamental D hD).y_strictMono
      hmn_int

/-- The canonical x-coordinate is injective on nonnegative powers. The proof
uses the Pell equation to recover the nonnegative y-coordinate and then
Mathlib's strict monotonicity of that coordinate. -/
theorem pellX_injective (D : Nat) (hD : PellKernel D) :
    Function.Injective (pellX D hD) := by
  intro m n hmn
  have hx : (pellSolution D hD m).x = (pellSolution D hD n).x := by
    rw [← pellX_intCast D hD m, ← pellX_intCast D hD n]
    exact_mod_cast hmn
  have hm := (pellSolution D hD m).prop_x
  have hn := (pellSolution D hD n).prop_x
  rw [hx] at hm
  have hD_pos : (0 : Int) < D := by
    exact_mod_cast (Nat.zero_lt_of_lt hD.1)
  have hy_sq : (pellSolution D hD m).y ^ 2 = (pellSolution D hD n).y ^ 2 := by
    nlinarith
  have hym_nonneg := pellSolution_y_nonneg D hD m
  have hyn_nonneg := pellSolution_y_nonneg D hD n
  have hy : (pellSolution D hD m).y = (pellSolution D hD n).y := by
    nlinarith
  exact (pellSolution_y_strictMono D hD).injective hy

end Erdos364
