import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Erdos364

/-- A positive natural number is powerful when every prime divisor occurs at
least to second order. Positivity is part of the predicate, so zero is not a
powerful number in the lab. -/
def PowerfulPos (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- The defining equivalence retained from canonical target revision 1. -/
theorem powerfulPos_iff (n : Nat) :
    PowerfulPos n ↔ 0 < n ∧ ∀ p : Nat, Nat.Prime p → p ∣ n → p ^ 2 ∣ n :=
  Iff.rfl

/-- The explicit positive-domain boundary excludes zero. -/
theorem not_powerfulPos_zero : ¬ PowerfulPos 0 := by
  simp [PowerfulPos]

/-- The multiplicative unit is positive and has no prime divisors. -/
theorem powerfulPos_one : PowerfulPos 1 := by
  constructor
  · norm_num
  · intro p hp hp_dvd
    exact (hp.ne_one (Nat.dvd_one.mp hp_dvd)).elim

/-- A prime occurring to exponent one is not powerful. -/
theorem not_powerfulPos_two : ¬ PowerfulPos 2 := by
  intro h
  have hsq := h.2 2 (by norm_num) (by norm_num)
  norm_num at hsq

/-- The first prime square is powerful. -/
theorem powerfulPos_four : PowerfulPos 4 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hp_dvd
  have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp_dvd
  interval_cases p <;> norm_num [Nat.Prime] at *

/-- The first prime cube is powerful. -/
theorem powerfulPos_eight : PowerfulPos 8 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hp_dvd
  have hp_le : p ≤ 8 := Nat.le_of_dvd (by norm_num) hp_dvd
  interval_cases p <;> norm_num [Nat.Prime] at *

/-- Twelve fails because three divides it but nine does not. -/
theorem not_powerfulPos_twelve : ¬ PowerfulPos 12 := by
  intro h
  have hsq := h.2 3 (by norm_num) (by norm_num)
  norm_num at hsq

/-- Seventy-two is the first declared mixed powerful control. -/
theorem powerfulPos_seventyTwo : PowerfulPos 72 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hp_dvd
  have hp_le : p ≤ 72 := Nat.le_of_dvd (by norm_num) hp_dvd
  interval_cases p <;> norm_num [Nat.Prime] at *

end Erdos364
