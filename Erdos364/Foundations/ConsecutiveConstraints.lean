import Erdos364.Foundations.PowerfulTriple
import Mathlib.Data.Nat.GCD.Basic

namespace Erdos364

/-- A natural congruent to two modulo four has a single factor of two and is not powerful. -/
theorem not_powerfulPos_of_mod_four_eq_two {n : Nat}
    (hmod : n % 4 = 2) :
    ¬ PowerfulPos n := by
  intro hpowerful
  have htwo_dvd : 2 ∣ n := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hfour_dvd : 4 ∣ n := by
    simpa using hpowerful.2 2 Nat.prime_two htwo_dvd
  have hzero : n % 4 = 0 := Nat.mod_eq_zero_of_dvd hfour_dvd
  omega

/-- Residues three and six modulo nine have a single factor of three and are not powerful. -/
theorem not_powerfulPos_of_mod_nine_eq_three_or_six {n : Nat}
    (hmod : n % 9 = 3 ∨ n % 9 = 6) :
    ¬ PowerfulPos n := by
  intro hpowerful
  have hthree_dvd : 3 ∣ n := by
    apply Nat.dvd_of_mod_eq_zero
    rcases hmod with hthree | hsix <;> omega
  have hnine_dvd : 9 ∣ n := by
    simpa using hpowerful.2 3 (by decide) hthree_dvd
  have hzero : n % 9 = 0 := Nat.mod_eq_zero_of_dvd hnine_dvd
  rcases hmod with hthree | hsix <;> omega

/-- Two powerful naturals at distance two cannot have an even left endpoint. -/
theorem no_even_powerfulPos_pair_difference_two (a : Nat)
    (ha : PowerfulPos a)
    (ha_two : PowerfulPos (a + 2))
    (ha_even : a % 2 = 0) :
    False := by
  have htwo_dvd : 2 ∣ a := Nat.dvd_of_mod_eq_zero ha_even
  have hfour_dvd : 4 ∣ a := by
    simpa using ha.2 2 Nat.prime_two htwo_dvd
  have ha_mod_four : a % 4 = 0 := Nat.mod_eq_zero_of_dvd hfour_dvd
  have ha_two_mod_four : (a + 2) % 4 = 2 := by omega
  exact (not_powerfulPos_of_mod_four_eq_two ha_two_mod_four) ha_two

/-- A powerful consecutive triple starts in residue three modulo four. -/
theorem PowerfulTripleAt.start_mod_four_eq_three {n : Nat}
    (htriple : PowerfulTripleAt n) :
    n % 4 = 3 := by
  have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
  have hnot_zero : n % 4 ≠ 0 := by
    intro hmod
    have hright_mod : (n + 2) % 4 = 2 := by omega
    exact (not_powerfulPos_of_mod_four_eq_two hright_mod) htriple.2.2
  have hnot_one : n % 4 ≠ 1 := by
    intro hmod
    have hmiddle_mod : (n + 1) % 4 = 2 := by omega
    exact (not_powerfulPos_of_mod_four_eq_two hmiddle_mod) htriple.2.1
  have hnot_two : n % 4 ≠ 2 := by
    intro hmod
    exact (not_powerfulPos_of_mod_four_eq_two hmod) htriple.1
  omega

/-- The two flanks of a powerful consecutive triple are odd. -/
theorem PowerfulTripleAt.outer_terms_odd {n : Nat}
    (htriple : PowerfulTripleAt n) :
    n % 2 = 1 ∧ (n + 2) % 2 = 1 := by
  have hmod := htriple.start_mod_four_eq_three
  constructor <;> omega

/-- Equivalently, the middle of a powerful consecutive triple is divisible by four. -/
theorem PowerfulTripleAt.middle_mod_four_eq_zero {n : Nat}
    (htriple : PowerfulTripleAt n) :
    (n + 1) % 4 = 0 := by
  have hmod := htriple.start_mod_four_eq_three
  omega

/-- A powerful consecutive triple starts in residue zero, seven, or eight modulo nine. -/
theorem PowerfulTripleAt.start_mod_nine {n : Nat}
    (htriple : PowerfulTripleAt n) :
    n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
  have hlt : n % 9 < 9 := Nat.mod_lt n (by decide)
  have hnot_one : n % 9 ≠ 1 := by
    intro hmod
    have hright_mod : (n + 2) % 9 = 3 := by omega
    exact
      (not_powerfulPos_of_mod_nine_eq_three_or_six (Or.inl hright_mod))
        htriple.2.2
  have hnot_two : n % 9 ≠ 2 := by
    intro hmod
    have hmiddle_mod : (n + 1) % 9 = 3 := by omega
    exact
      (not_powerfulPos_of_mod_nine_eq_three_or_six (Or.inl hmiddle_mod))
        htriple.2.1
  have hnot_three : n % 9 ≠ 3 := by
    intro hmod
    exact
      (not_powerfulPos_of_mod_nine_eq_three_or_six (Or.inl hmod))
        htriple.1
  have hnot_four : n % 9 ≠ 4 := by
    intro hmod
    have hright_mod : (n + 2) % 9 = 6 := by omega
    exact
      (not_powerfulPos_of_mod_nine_eq_three_or_six (Or.inr hright_mod))
        htriple.2.2
  have hnot_five : n % 9 ≠ 5 := by
    intro hmod
    have hmiddle_mod : (n + 1) % 9 = 6 := by omega
    exact
      (not_powerfulPos_of_mod_nine_eq_three_or_six (Or.inr hmiddle_mod))
        htriple.2.1
  have hnot_six : n % 9 ≠ 6 := by
    intro hmod
    exact
      (not_powerfulPos_of_mod_nine_eq_three_or_six (Or.inr hmod))
        htriple.1
  omega

/-- Combining the mod-four and mod-nine gates gives the exact three start classes modulo 36. -/
theorem PowerfulTripleAt.start_mod_thirtySix {n : Nat}
    (htriple : PowerfulTripleAt n) :
    n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  have hlt : n % 36 < 36 := Nat.mod_lt n (by decide)
  have hfour : n % 4 = 3 := htriple.start_mod_four_eq_three
  have hnine : n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8 := htriple.start_mod_nine
  omega

/-- Any two consecutive naturals are coprime. -/
theorem consecutive_coprime (n : Nat) :
    Nat.Coprime n (n + 1) := by
  exact
    (Nat.coprime_self_add_right (m := n) (n := 1)).mpr
      (Nat.coprime_one_right n)

/-- Naturals at distance two are coprime when the left endpoint is three modulo four. -/
theorem outer_coprime_of_mod_four_eq_three {n : Nat}
    (hmod : n % 4 = 3) :
    Nat.Coprime n (n + 2) := by
  unfold Nat.Coprime
  have hgcd_dvd_two : Nat.gcd n (n + 2) ∣ 2 := by
    have hright : Nat.gcd n (n + 2) ∣ n + 2 := Nat.gcd_dvd_right n (n + 2)
    have hleft : Nat.gcd n (n + 2) ∣ n := Nat.gcd_dvd_left n (n + 2)
    have hsub : Nat.gcd n (n + 2) ∣ (n + 2) - n := Nat.dvd_sub hright hleft
    have hdiff : (n + 2) - n = 2 := by omega
    simpa [hdiff] using hsub
  have hgcd_dvd_n : Nat.gcd n (n + 2) ∣ n := Nat.gcd_dvd_left n (n + 2)
  have hn_odd : ¬ 2 ∣ n := by
    intro htwo
    have hzero : n % 2 = 0 := Nat.mod_eq_zero_of_dvd htwo
    omega
  have hle : Nat.gcd n (n + 2) ≤ 2 := Nat.le_of_dvd (by decide) hgcd_dvd_two
  have hpos : 0 < Nat.gcd n (n + 2) := Nat.gcd_pos_of_pos_right n (by omega)
  interval_cases Nat.gcd n (n + 2)
  · rfl
  · exfalso
    have htwo : 2 ∣ n := by simpa using hgcd_dvd_n
    exact hn_odd htwo

/-- The three terms of a powerful consecutive triple are pairwise coprime. -/
theorem PowerfulTripleAt.pairwise_coprime {n : Nat}
    (htriple : PowerfulTripleAt n) :
    Nat.Coprime n (n + 1) ∧
      Nat.Coprime (n + 1) (n + 2) ∧
        Nat.Coprime n (n + 2) := by
  refine ⟨consecutive_coprime n, ?_, ?_⟩
  · simpa [Nat.add_assoc] using consecutive_coprime (n + 1)
  · exact outer_coprime_of_mod_four_eq_three htriple.start_mod_four_eq_three

/-- No four consecutive positive naturals are all powerful. -/
theorem no_four_consecutive_powerfulPos (n : Nat) :
    ¬ (PowerfulPos n ∧
      PowerfulPos (n + 1) ∧
      PowerfulPos (n + 2) ∧
      PowerfulPos (n + 3)) := by
  intro hfour
  have hcase :
      n % 4 = 2 ∨
        (n + 1) % 4 = 2 ∨
          (n + 2) % 4 = 2 ∨
            (n + 3) % 4 = 2 := by
    omega
  rcases hcase with hmod | hmod | hmod | hmod
  · exact (not_powerfulPos_of_mod_four_eq_two hmod) hfour.1
  · exact (not_powerfulPos_of_mod_four_eq_two hmod) hfour.2.1
  · exact (not_powerfulPos_of_mod_four_eq_two hmod) hfour.2.2.1
  · exact (not_powerfulPos_of_mod_four_eq_two hmod) hfour.2.2.2

end Erdos364
