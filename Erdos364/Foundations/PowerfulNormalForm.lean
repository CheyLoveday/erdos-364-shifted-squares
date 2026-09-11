import Erdos364.Foundations.PowerfulValuation
import Mathlib.Data.Nat.Squarefree

namespace Erdos364

/-- A positive square-cube representation with an explicitly squarefree cube factor. -/
def SquareCubeNormalForm (n a b : Nat) : Prop :=
  0 < a ∧
    0 < b ∧
      n = a ^ 2 * b ^ 3 ∧
        ∀ p : Nat, Nat.Prime p → ¬ p ^ 2 ∣ b

/-- Mathlib squarefreeness implies the prime-square condition in the target statement. -/
private theorem primeSquarefree_of_mathlibSquarefree {n : Nat}
    (h : _root_.Squarefree n) :
    ∀ p : Nat, Nat.Prime p → ¬ p ^ 2 ∣ n := by
  intro p hp hp_square
  exact (Nat.squarefree_iff_prime_squarefree.mp h) p hp (by simpa [pow_two] using hp_square)

/-- In `squareFactor² * kernel = n`, a squarefree kernel divides the square factor
when `n` is positive and powerful. -/
private theorem squarefree_part_dvd_square_factor_of_powerfulPos
    {n kernel squareFactor : Nat}
    (hpowerful : PowerfulPos n)
    (hkernel_ne : kernel ≠ 0)
    (hsquarefree : _root_.Squarefree kernel)
    (hdecomp : squareFactor ^ 2 * kernel = n) :
    kernel ∣ squareFactor := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hpowerful.1
  have hkernel_dvd_n : kernel ∣ n := by
    rw [← hdecomp]
    exact dvd_mul_left kernel (squareFactor ^ 2)
  have hkernel_sq_dvd_n : kernel * kernel ∣ n := by
    refine (Nat.factorization_le_iff_dvd (mul_ne_zero hkernel_ne hkernel_ne) hn_ne).mp ?_
    intro p
    by_cases hp : Nat.Prime p
    · have hkernel_fac_le : kernel.factorization p ≤ 1 :=
        (Nat.squarefree_iff_factorization_le_one hkernel_ne).mp hsquarefree p
      by_cases hkernel_fac_zero : kernel.factorization p = 0
      · rw [Nat.factorization_mul hkernel_ne hkernel_ne]
        simp [hkernel_fac_zero]
      · have hkernel_fac_pos : 1 ≤ kernel.factorization p :=
          Nat.succ_le_of_lt (Nat.pos_of_ne_zero hkernel_fac_zero)
        have hp_dvd_kernel : p ∣ kernel :=
          (hp.dvd_iff_one_le_factorization hkernel_ne).mpr hkernel_fac_pos
        have hp_dvd_n : p ∣ n := dvd_trans hp_dvd_kernel hkernel_dvd_n
        have hn_fac_two : 2 ≤ n.factorization p := by
          rcases (powerfulPos_iff_factorization n).mp hpowerful |>.2 p hp with hn_zero | hn_two
          · have hn_positive := hp.factorization_pos_of_dvd hn_ne hp_dvd_n
            omega
          · exact hn_two
        have hkernel_fac_one : kernel.factorization p = 1 :=
          le_antisymm hkernel_fac_le hkernel_fac_pos
        rw [Nat.factorization_mul hkernel_ne hkernel_ne]
        simp [Finsupp.add_apply, hkernel_fac_one]
        exact hn_fac_two
    · have hfac_zero : kernel.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_prime kernel hp
      rw [Nat.factorization_mul hkernel_ne hkernel_ne]
      simp [Finsupp.add_apply, hfac_zero]
  have hkernel_sq_dvd_decomp :
      kernel * kernel ∣ kernel * (squareFactor ^ 2) := by
    rw [← hdecomp] at hkernel_sq_dvd_n
    simpa [mul_comm, mul_left_comm, mul_assoc] using hkernel_sq_dvd_n
  have hkernel_dvd_square : kernel ∣ squareFactor ^ 2 :=
    hsquarefree.dvd_of_squarefree_of_mul_dvd_mul_right hkernel_sq_dvd_decomp
  exact (hsquarefree.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hkernel_dvd_square

/-- The boundary witness required by the target: `1 = 1² * 1³`. -/
theorem squareCubeNormalForm_one : SquareCubeNormalForm 1 1 1 := by
  refine ⟨by decide, by decide, by norm_num, ?_⟩
  intro p hp hp_square
  have hp_ge : 2 ≤ p := hp.two_le
  have hp_sq_le : p ^ 2 ≤ 1 := Nat.le_of_dvd (by decide) hp_square
  nlinarith

/-- Every positive powerful natural has a positive square-cube normal-form witness. -/
theorem exists_squareCubeNormalForm_of_powerfulPos {n : Nat}
    (hpowerful : PowerfulPos n) :
    ∃ a b : Nat, SquareCubeNormalForm n a b := by
  obtain ⟨kernel, squareFactor, hkernel_pos, hsquareFactor_pos, hdecomp, hsquarefree⟩ :=
    Nat.sq_mul_squarefree_of_pos hpowerful.1
  have hkernel_ne : kernel ≠ 0 := Nat.ne_of_gt hkernel_pos
  have hkernel_dvd : kernel ∣ squareFactor :=
    squarefree_part_dvd_square_factor_of_powerfulPos
      hpowerful hkernel_ne hsquarefree hdecomp
  have hkernel_le : kernel ≤ squareFactor := Nat.le_of_dvd hsquareFactor_pos hkernel_dvd
  have hquotient_pos : 0 < squareFactor / kernel := Nat.div_pos hkernel_le hkernel_pos
  refine ⟨squareFactor / kernel, kernel, hquotient_pos, hkernel_pos, ?_, ?_⟩
  · calc
      n = squareFactor ^ 2 * kernel := hdecomp.symm
      _ = ((squareFactor / kernel) * kernel) ^ 2 * kernel := by
        rw [Nat.div_mul_cancel hkernel_dvd]
      _ = (squareFactor / kernel) ^ 2 * kernel ^ 3 := by ring
  · exact primeSquarefree_of_mathlibSquarefree hsquarefree

/-- The repository's prime-square condition on a normal-form kernel is exactly
Mathlib squarefreeness. -/
theorem SquareCubeNormalForm.kernel_squarefree {n a D : Nat}
    (hform : SquareCubeNormalForm n a D) :
    _root_.Squarefree D := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hp_square
  exact hform.2.2.2 p hp (by simpa [pow_two] using hp_square)

/-- Build the repository normal form from a positive square factor, a positive
Mathlib-squarefree kernel, and the defining equality. -/
theorem squareCubeNormalForm_of_eq_sq_mul_cube {n a D : Nat}
    (ha : 0 < a) (hD : 0 < D)
    (hvalue : n = a ^ 2 * D ^ 3)
    (hD_squarefree : _root_.Squarefree D) :
    SquareCubeNormalForm n a D := by
  refine ⟨ha, hD, hvalue, ?_⟩
  intro p hp hp_square
  exact
    (Nat.squarefree_iff_prime_squarefree.mp hD_squarefree) p hp
      (by simpa [pow_two] using hp_square)

/-- Positive powerful naturals are closed under multiplication. No coprimality
hypothesis is needed in this direction. -/
theorem powerfulPos_mul {m n : Nat}
    (hm : PowerfulPos m) (hn : PowerfulPos n) :
    PowerfulPos (m * n) := by
  refine ⟨Nat.mul_pos hm.1 hn.1, ?_⟩
  intro p hp hp_dvd
  rcases hp.dvd_mul.mp hp_dvd with hpm | hpn
  · exact dvd_mul_of_dvd_left (hm.2 p hp hpm) n
  · exact dvd_mul_of_dvd_right (hn.2 p hp hpn) m

/-- Any positive square-cube normal form represents a positive powerful
natural. -/
theorem powerfulPos_of_squareCubeNormalForm {n a D : Nat}
    (hform : SquareCubeNormalForm n a D) :
    PowerfulPos n := by
  rw [hform.2.2.1]
  refine ⟨Nat.mul_pos (pow_pos hform.1 2) (pow_pos hform.2.1 3), ?_⟩
  intro p hp hp_dvd
  rcases hp.dvd_mul.mp hp_dvd with hpa | hD
  · have hp_a : p ∣ a := hp.dvd_of_dvd_pow hpa
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp_a 2) (D ^ 3)
  · have hp_D : p ∣ D := hp.dvd_of_dvd_pow hD
    exact
      dvd_mul_of_dvd_right
        (pow_dvd_pow_of_dvd_of_le hp_D (by decide : 2 ≤ 3)) (a ^ 2)

/-- Existence of a positive square-cube normal form is equivalent to
powerfulness on the repository's positive domain. -/
theorem powerfulPos_iff_exists_squareCubeNormalForm (n : Nat) :
    PowerfulPos n ↔ ∃ a D : Nat, SquareCubeNormalForm n a D := by
  constructor
  · exact exists_squareCubeNormalForm_of_powerfulPos
  · rintro ⟨a, D, hform⟩
    exact powerfulPos_of_squareCubeNormalForm hform

end Erdos364
