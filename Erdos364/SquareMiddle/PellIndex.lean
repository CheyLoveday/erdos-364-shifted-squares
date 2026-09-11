import Mathlib.Algebra.Ring.Parity

namespace Erdos364

/-!
# Odd quotient index arithmetic

The Pell-specific layers supply a positive odd rank `R` and establish
`R ∣ n`.  This file contains only the elementary natural-number fact that an
odd multiple is parametrised uniquely as `R * (2*k + 1)`.  Keeping it
separate prevents the source normalizer from hiding this parity step inside a
large Pell proof.
-/

/-- A positive odd divisor of an odd natural has a unique odd quotient. -/
theorem odd_dvd_iff_existsUnique_twice_mul_add_one
    {r n : Nat} (hr_pos : 0 < r) (hr_odd : Odd r) :
    (r ∣ n ∧ Odd n) ↔
      ∃! k : Nat, n = r * (2 * k + 1) := by
  constructor
  · rintro ⟨hr_dvd_n, hn_odd⟩
    obtain ⟨m, hm⟩ := hr_dvd_n
    have hm_odd : Odd m := by
      rw [hm] at hn_odd
      exact (Nat.odd_mul.mp hn_odd).2
    obtain ⟨k, hk⟩ := hm_odd.exists_bit1
    refine ⟨k, ?_, ?_⟩
    · rw [hm, hk]
    · intro l hl
      rw [hm, hk] at hl
      have hquotient : 2 * k + 1 = 2 * l + 1 :=
        Nat.eq_of_mul_eq_mul_left hr_pos hl
      omega
  · rintro ⟨k, hk, _⟩
    constructor
    · exact ⟨2 * k + 1, hk⟩
    · rw [hk]
      exact hr_odd.mul (odd_two_mul_add_one k)

/-- The same parametrisation with the equality oriented as a canonical-index
definition normally is. -/
theorem existsUnique_twice_mul_add_one_iff_odd_dvd
    {r n : Nat} (hr_pos : 0 < r) (hr_odd : Odd r) :
    (∃! k : Nat, r * (2 * k + 1) = n) ↔
      (r ∣ n ∧ Odd n) := by
  constructor
  · rintro ⟨k, hk, _⟩
    constructor
    · exact ⟨2 * k + 1, hk.symm⟩
    · rw [← hk]
      exact hr_odd.mul (odd_two_mul_add_one k)
  · intro h
    obtain ⟨k, hk, hunique⟩ :=
      (odd_dvd_iff_existsUnique_twice_mul_add_one hr_pos hr_odd).mp h
    refine ⟨k, hk.symm, ?_⟩
    intro l hl
    exact hunique l hl.symm

end Erdos364
