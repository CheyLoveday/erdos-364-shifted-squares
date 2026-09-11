import Erdos364.Foundations.PowerfulNormalForm

namespace Erdos364

/-- Prime-exponent identity for a positive square-cube value. -/
private theorem factorization_sq_mul_cube {a b : Nat}
    (ha : a ≠ 0) (hb : b ≠ 0) (p : Nat) :
    (a ^ 2 * b ^ 3).factorization p =
      2 * a.factorization p + 3 * b.factorization p := by
  have hreassociate : a ^ 2 * b ^ 3 = (a * a) * ((b * b) * b) := by ring
  rw [hreassociate,
    Nat.factorization_mul (mul_ne_zero ha ha)
      (mul_ne_zero (mul_ne_zero hb hb) hb),
    Nat.factorization_mul ha ha,
    Nat.factorization_mul (mul_ne_zero hb hb) hb,
    Nat.factorization_mul hb hb]
  simp only [Finsupp.add_apply]
  ring

/-- A kernel satisfying the target's prime-square condition has prime exponent at most one. -/
private theorem normalForm_kernel_factorization_le_one
    {n a b p : Nat}
    (hform : SquareCubeNormalForm n a b)
    (hp : Nat.Prime p) :
    b.factorization p ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ b.factorization p := by omega
  have hb_ne : b ≠ 0 := Nat.ne_of_gt hform.2.1
  have hp_square_dvd : p ^ 2 ∣ b :=
    (hp.pow_dvd_iff_le_factorization hb_ne).mpr htwo
  exact hform.2.2.2 p hp hp_square_dvd

/-- Two positive square-cube normal forms for the same value have the same cube kernel. -/
theorem squareCubeNormalForm_kernel_unique
    {n a b c d : Nat}
    (_hn_pos : 0 < n)
    (hab : SquareCubeNormalForm n a b)
    (hcd : SquareCubeNormalForm n c d) :
    b = d := by
  have ha_ne : a ≠ 0 := Nat.ne_of_gt hab.1
  have hb_ne : b ≠ 0 := Nat.ne_of_gt hab.2.1
  have hc_ne : c ≠ 0 := Nat.ne_of_gt hcd.1
  have hd_ne : d ≠ 0 := Nat.ne_of_gt hcd.2.1
  have hfactorizations : ∀ p : Nat, b.factorization p = d.factorization p := by
    intro p
    by_cases hp : Nat.Prime p
    · have hab_factorization := factorization_sq_mul_cube ha_ne hb_ne p
      have hcd_factorization := factorization_sq_mul_cube hc_ne hd_ne p
      rw [← hab.2.2.1] at hab_factorization
      rw [← hcd.2.2.1] at hcd_factorization
      have hb_le := normalForm_kernel_factorization_le_one hab hp
      have hd_le := normalForm_kernel_factorization_le_one hcd hp
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime b hp,
        Nat.factorization_eq_zero_of_not_prime d hp]
  have hbd : b ∣ d := by
    refine (Nat.factorization_le_iff_dvd hb_ne hd_ne).mp ?_
    intro p
    exact le_of_eq (hfactorizations p)
  have hdb : d ∣ b := by
    refine (Nat.factorization_le_iff_dvd hd_ne hb_ne).mp ?_
    intro p
    exact le_of_eq (hfactorizations p).symm
  exact Nat.dvd_antisymm hbd hdb

/-- The square part is unique as well, so the complete normal-form witness is unique. -/
theorem squareCubeNormalForm_pair_unique
    {n a b c d : Nat}
    (hn_pos : 0 < n)
    (hab : SquareCubeNormalForm n a b)
    (hcd : SquareCubeNormalForm n c d) :
    a = c ∧ b = d := by
  have hkernel : b = d := squareCubeNormalForm_kernel_unique hn_pos hab hcd
  have hvalue : a ^ 2 * b ^ 3 = c ^ 2 * d ^ 3 :=
    hab.2.2.1.symm.trans hcd.2.2.1
  rw [← hkernel] at hvalue
  have hkernel_cube_pos : 0 < b ^ 3 := pow_pos hab.2.1 3
  have hsquares : a ^ 2 = c ^ 2 :=
    Nat.eq_of_mul_eq_mul_right hkernel_cube_pos hvalue
  exact ⟨Nat.pow_left_injective (by omega) hsquares, hkernel⟩

end Erdos364
