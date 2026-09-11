import Erdos364.Foundations.ConsecutiveConstraints
import Erdos364.Foundations.PowerfulNormalForm

namespace Erdos364

/-- The cube kernel in a square-cube normal form divides the represented value. -/
theorem squareCubeNormalForm_kernel_dvd_value {n a b : Nat}
    (hform : SquareCubeNormalForm n a b) :
    b ∣ n := by
  refine ⟨a ^ 2 * b ^ 2, ?_⟩
  calc
    n = a ^ 2 * b ^ 3 := hform.2.2.1
    _ = b * (a ^ 2 * b ^ 2) := by ring

/-- Kernels of normal forms for coprime values are coprime. -/
theorem squareCubeNormalForm_kernels_coprime_of_values_coprime
    {m n a b c d : Nat}
    (hcop : Nat.Coprime m n)
    (hm : SquareCubeNormalForm m a b)
    (hn : SquareCubeNormalForm n c d) :
    Nat.Coprime b d := by
  have hbn : Nat.Coprime b n :=
    Nat.Coprime.coprime_dvd_left
      (squareCubeNormalForm_kernel_dvd_value hm) hcop
  exact
    Nat.Coprime.coprime_dvd_right
      (squareCubeNormalForm_kernel_dvd_value hn) hbn

/-- Normal-form kernels attached to a powerful consecutive triple are pairwise coprime. -/
theorem PowerfulTripleAt.normalForm_kernels_pairwise_coprime
    {n a0 b0 a1 b1 a2 b2 : Nat}
    (htriple : PowerfulTripleAt n)
    (h0 : SquareCubeNormalForm n a0 b0)
    (h1 : SquareCubeNormalForm (n + 1) a1 b1)
    (h2 : SquareCubeNormalForm (n + 2) a2 b2) :
    Nat.Coprime b0 b1 ∧
      Nat.Coprime b1 b2 ∧
        Nat.Coprime b0 b2 := by
  have hvalues := htriple.pairwise_coprime
  exact
    ⟨squareCubeNormalForm_kernels_coprime_of_values_coprime hvalues.1 h0 h1,
      squareCubeNormalForm_kernels_coprime_of_values_coprime hvalues.2.1 h1 h2,
      squareCubeNormalForm_kernels_coprime_of_values_coprime hvalues.2.2 h0 h2⟩

/-- A value congruent to three modulo four has a kernel in the same residue class. -/
theorem squareCubeNormalForm_kernel_mod_four_of_value_mod_four_eq_three
    {n a b : Nat}
    (hform : SquareCubeNormalForm n a b)
    (hmod : n % 4 = 3) :
    b % 4 = 3 := by
  have hvalue : (a ^ 2 * b ^ 3) % 4 = 3 := by
    rw [← hform.2.2.1]
    exact hmod
  have halt : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hblt : b % 4 < 4 := Nat.mod_lt b (by decide)
  have ha_cases :
      a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
    omega
  have hb_cases :
      b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
    omega
  rcases ha_cases with ha | ha | ha | ha <;>
    rcases hb_cases with hb | hb | hb | hb <;>
      try omega
  all_goals
    simp [Nat.pow_mod, Nat.mul_mod, ha, hb] at hvalue

/-- A value congruent to one modulo four has a kernel in the same residue class. -/
theorem squareCubeNormalForm_kernel_mod_four_of_value_mod_four_eq_one
    {n a b : Nat}
    (hform : SquareCubeNormalForm n a b)
    (hmod : n % 4 = 1) :
    b % 4 = 1 := by
  have hvalue : (a ^ 2 * b ^ 3) % 4 = 1 := by
    rw [← hform.2.2.1]
    exact hmod
  have halt : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hblt : b % 4 < 4 := Nat.mod_lt b (by decide)
  have ha_cases :
      a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by
    omega
  have hb_cases :
      b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by
    omega
  rcases ha_cases with ha | ha | ha | ha <;>
    rcases hb_cases with hb | hb | hb | hb <;>
      try omega
  all_goals
    simp [Nat.pow_mod, Nat.mul_mod, ha, hb] at hvalue

/-- The two outer normal-form kernels have the forced mod-four orientations. -/
theorem PowerfulTripleAt.normalForm_outer_kernels_mod_four
    {n a0 b0 a2 b2 : Nat}
    (htriple : PowerfulTripleAt n)
    (h0 : SquareCubeNormalForm n a0 b0)
    (h2 : SquareCubeNormalForm (n + 2) a2 b2) :
    b0 % 4 = 3 ∧ b2 % 4 = 1 := by
  have hstart : n % 4 = 3 := htriple.start_mod_four_eq_three
  have hright : (n + 2) % 4 = 1 := by omega
  exact
    ⟨squareCubeNormalForm_kernel_mod_four_of_value_mod_four_eq_three h0 hstart,
      squareCubeNormalForm_kernel_mod_four_of_value_mod_four_eq_one h2 hright⟩

end Erdos364
