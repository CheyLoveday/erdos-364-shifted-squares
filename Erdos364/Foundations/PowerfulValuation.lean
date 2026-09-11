import Erdos364.Foundations.PowerfulPos
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos364

/-- A positive natural number is powerful exactly when no prime occurs to exponent one. -/
theorem powerfulPos_iff_factorization (n : Nat) :
    PowerfulPos n ↔
      0 < n ∧
        ∀ p : Nat, Nat.Prime p →
          n.factorization p = 0 ∨ 2 ≤ n.factorization p := by
  constructor
  · rintro ⟨hn_pos, hpowerful⟩
    refine ⟨hn_pos, ?_⟩
    intro p hp
    by_cases hp_dvd : p ∣ n
    · right
      exact
        (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hn_pos)).mp
          (hpowerful p hp hp_dvd)
    · left
      exact Nat.factorization_eq_zero_of_not_dvd hp_dvd
  · rintro ⟨hn_pos, hvaluation⟩
    refine ⟨hn_pos, ?_⟩
    intro p hp hp_dvd
    rcases hvaluation p hp with hp_zero | hp_two
    · have hp_positive :=
        hp.factorization_pos_of_dvd (Nat.ne_of_gt hn_pos) hp_dvd
      omega
    · exact
        (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hn_pos)).mpr hp_two

/-- A prime occurring to exact exponent one prevents powerfulness. -/
theorem not_powerfulPos_of_prime_factorization_eq_one {n p : Nat}
    (hp : Nat.Prime p) (hp_one : n.factorization p = 1) :
    ¬ PowerfulPos n := by
  intro hpowerful
  rcases (powerfulPos_iff_factorization n).mp hpowerful |>.2 p hp with hp_zero | hp_two
  · omega
  · omega

/-- The target-local existential valuation-one corollary, with explicit positivity. -/
theorem not_powerfulPos_of_exists_prime_factorization_eq_one {n : Nat}
    (_hn_pos : 0 < n)
    (hprime : ∃ p : Nat, Nat.Prime p ∧ n.factorization p = 1) :
    ¬ PowerfulPos n := by
  obtain ⟨p, hp, hp_one⟩ := hprime
  exact not_powerfulPos_of_prime_factorization_eq_one hp hp_one

end Erdos364
