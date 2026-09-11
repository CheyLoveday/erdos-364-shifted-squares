import Erdos364.SquareMiddle.RightFlankNormOneModNine
import Mathlib.Data.Nat.Periodic

namespace Erdos364

open Pell

/-!
# A symbolic modulo-1089 exact-one obstruction

This module records two symbolic finite-witness certificates.  The input is
an arbitrary positive fundamental norm-one solution whose real coordinate is
`894` or `195` modulo `1089`; no numerical kernel instance is bundled here.
-/

/-- The real coordinate and normalized ordinate coefficient of a power,
computed only from the real coordinate of the generator. -/
def normOnePowerStateMod1089 (a : ZMod 1089) :
    Nat → ZMod 1089 × ZMod 1089
  | 0 => (1, 0)
  | n + 1 =>
      let s := normOnePowerStateMod1089 a n
      (a * s.1 + (a ^ 2 - 1) * s.2, s.1 + a * s.2)

/-- The symbolic recurrence indeed computes the two coordinates of a Pell
power modulo `1089`; the second component is the coefficient of `e.y`. -/
private theorem pellSolution_pow_state_mod1089
    {K : Nat} (e : Pell.Solution₁ (K : Int)) (n : Nat) :
    ((e ^ n).x : ZMod 1089) =
        (normOnePowerStateMod1089 (e.x : ZMod 1089) n).1 ∧
      ((e ^ n).y : ZMod 1089) =
        (normOnePowerStateMod1089 (e.x : ZMod 1089) n).2 *
          (e.y : ZMod 1089) := by
  have hnorm :
      (K : ZMod 1089) * (e.y : ZMod 1089) ^ 2 =
        (e.x : ZMod 1089) ^ 2 - 1 := by
    have h := congrArg (fun z : Int => (z : ZMod 1089)) e.prop
    push_cast at h
    linear_combination -h
  induction n with
  | zero =>
      simp [normOnePowerStateMod1089]
  | succ n ih =>
      constructor
      · rw [pow_succ, Pell.Solution₁.x_mul]
        push_cast
        rw [ih.1, ih.2]
        simp only [normOnePowerStateMod1089]
        linear_combination
          (normOnePowerStateMod1089 (e.x : ZMod 1089) n).2 * hnorm
      · rw [pow_succ, Pell.Solution₁.y_mul]
        push_cast
        rw [ih.1, ih.2]
        simp only [normOnePowerStateMod1089]
        ring

/-- The symbolic state selected by the `894` class returns to the identity
after twelve steps modulo `1089 = 3² * 11²`. -/
private theorem normOnePowerStateMod1089_twelve :
    normOnePowerStateMod1089 (894 : ZMod 1089) 12 = (1, 0) := by
  decide

/-- The selected real-coordinate condition forces a full oriented period
of twelve for the Pell powers modulo `1089`. -/
private theorem pellSolution_pow_mod1089_periodic
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 894) :
    Function.Periodic
      (fun n : Nat =>
        (((e ^ n).x : ZMod 1089), ((e ^ n).y : ZMod 1089))) 12 := by
  have hstate := pellSolution_pow_state_mod1089 e 12
  rw [hx, normOnePowerStateMod1089_twelve] at hstate
  have htwelve :
      ((e ^ 12).x : ZMod 1089) = 1 ∧
        ((e ^ 12).y : ZMod 1089) = 0 := by
    simpa using hstate
  intro n
  apply Prod.ext
  · change ((e ^ (n + 12)).x : ZMod 1089) =
      ((e ^ n).x : ZMod 1089)
    rw [pow_add, Pell.Solution₁.x_mul]
    push_cast
    rw [htwelve.1, htwelve.2]
    ring
  · change ((e ^ (n + 12)).y : ZMod 1089) =
      ((e ^ n).y : ZMod 1089)
    rw [pow_add, Pell.Solution₁.y_mul]
    push_cast
    rw [htwelve.1, htwelve.2]
    ring

/-- Odd classes `3,5,7,9 (mod 12)` give the two real-coordinate residues
which will force an exact factor of three. -/
private theorem pellSolution_pow_x_mod1089_three_classes
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 894) {n : Nat}
    (hn : n % 12 = 3 ∨ n % 12 = 5 ∨
      n % 12 = 7 ∨ n % 12 = 9) :
    (((e ^ n).x : ZMod 1089) = 0 ∨
      ((e ^ n).x : ZMod 1089) = 195) := by
  have hperiod := (pellSolution_pow_mod1089_periodic e hx).map_mod_nat n
  have hperiodX := congrArg Prod.fst hperiod
  simp only at hperiodX
  have hstate := pellSolution_pow_state_mod1089 e (n % 12)
  rw [hx] at hstate
  rw [← hperiodX, hstate.1]
  rcases hn with h3 | h5 | h7 | h9
  · rw [h3]
    decide
  · rw [h5]
    decide
  · rw [h7]
    decide
  · rw [h9]
    decide

/-- Odd classes `1,11 (mod 12)` retain real coordinate `894`; these are the
classes which will force an exact factor of eleven. -/
private theorem pellSolution_pow_x_mod1089_eleven_classes
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 894) {n : Nat}
    (hn : n % 12 = 1 ∨ n % 12 = 11) :
    ((e ^ n).x : ZMod 1089) = 894 := by
  have hperiod := (pellSolution_pow_mod1089_periodic e hx).map_mod_nat n
  have hperiodX := congrArg Prod.fst hperiod
  simp only at hperiodX
  have hstate := pellSolution_pow_state_mod1089 e (n % 12)
  rw [hx] at hstate
  rw [← hperiodX, hstate.1]
  rcases hn with h1 | h11
  · rw [h1]
    decide
  · rw [h11]
    decide

/-- A square congruent to four modulo nine gives exact three-adic depth one
in `X² - 1`. -/
private theorem three_exactly_dvd_square_sub_one_of_mod_nine_four
    {X : Nat} (hX : 0 < X)
    (hmod : ((X ^ 2 : Nat) : ZMod 9) = 4) :
    3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1 := by
  have hmodNine : X ^ 2 ≡ 4 [MOD 9] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
  have hxOne : 1 ≤ X ^ 2 := by nlinarith
  constructor
  · apply (Nat.modEq_iff_dvd' hxOne).mp
    exact
      ((hmodNine.of_dvd (by decide : 3 ∣ 9)).trans
        (by decide : 4 ≡ 1 [MOD 3])).symm
  · intro hnine
    have hone : 1 ≡ X ^ 2 [MOD 9] :=
      (Nat.modEq_iff_dvd' hxOne).mpr (by
        norm_num at hnine ⊢
        exact hnine)
    have hbad : 1 ≡ 4 [MOD 9] := hone.trans hmodNine
    norm_num [Nat.ModEq] at hbad

/-- A square congruent to seven modulo nine gives the other exact-three
residue in `X² - 1`. -/
private theorem three_exactly_dvd_square_sub_one_of_mod_nine_seven
    {X : Nat} (hX : 0 < X)
    (hmod : ((X ^ 2 : Nat) : ZMod 9) = 7) :
    3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1 := by
  have hmodNine : X ^ 2 ≡ 7 [MOD 9] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
  have hxOne : 1 ≤ X ^ 2 := by nlinarith
  constructor
  · apply (Nat.modEq_iff_dvd' hxOne).mp
    exact
      ((hmodNine.of_dvd (by decide : 3 ∣ 9)).trans
        (by decide : 7 ≡ 1 [MOD 3])).symm
  · intro hnine
    have hone : 1 ≡ X ^ 2 [MOD 9] :=
      (Nat.modEq_iff_dvd' hxOne).mpr (by
        norm_num at hnine ⊢
        exact hnine)
    have hbad : 1 ≡ 7 [MOD 9] := hone.trans hmodNine
    norm_num [Nat.ModEq] at hbad

/-- The square residue twenty-three modulo `121` gives exact eleven-adic
depth one in `X² - 1`. -/
private theorem eleven_exactly_dvd_square_sub_one_of_mod_121
    {X : Nat} (hX : 0 < X)
    (hmod : ((X ^ 2 : Nat) : ZMod 121) = 23) :
    11 ∣ X ^ 2 - 1 ∧ ¬ 11 ^ 2 ∣ X ^ 2 - 1 := by
  have hmod121 : X ^ 2 ≡ 23 [MOD 121] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hmod
  have hxOne : 1 ≤ X ^ 2 := by nlinarith
  constructor
  · apply (Nat.modEq_iff_dvd' hxOne).mp
    exact
      ((hmod121.of_dvd (by decide : 11 ∣ 121)).trans
        (by decide : 23 ≡ 1 [MOD 11])).symm
  · intro h121
    have hone : 1 ≡ X ^ 2 [MOD 121] :=
      (Nat.modEq_iff_dvd' hxOne).mpr (by
        norm_num at h121 ⊢
        exact h121)
    have hbad : 1 ≡ 23 [MOD 121] := hone.trans hmod121
    norm_num [Nat.ModEq] at hbad

/-- Real coordinate of the squared negative-Pell solution, in the form used
by the modular extraction below. -/
private theorem negativePellSquareSolution_x_eq_twice_square_add_one
    {K X W : Nat} (hPell : X ^ 2 + 1 = K * W ^ 2) :
    (negativePellSquareSolution hPell).x =
      2 * (X : Int) ^ 2 + 1 := by
  simp only [negativePellSquareSolution, Pell.Solution₁.x_mk]
  have hz : (X : Int) ^ 2 + 1 = K * (W : Int) ^ 2 := by
    exact_mod_cast hPell
  linarith

/-- At a fixed norm-one exponent, the four middle odd classes modulo twelve
give exact factor three and the two remaining odd classes give exact factor
eleven. -/
theorem negativePell_exactOne_of_normOne_mod1089_by_exponent
    {K X W n : Nat}
    (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 894)
    (hX : 0 < X)
    (hPell : X ^ 2 + 1 = K * W ^ 2)
    (hn : negativePellSquareSolution hPell = e ^ n) :
    ((n % 12 = 3 ∨ n % 12 = 5 ∨
        n % 12 = 7 ∨ n % 12 = 9) →
      (3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1)) ∧
    ((n % 12 = 1 ∨ n % 12 = 11) →
      (11 ∣ X ^ 2 - 1 ∧ ¬ 11 ^ 2 ∣ X ^ 2 - 1)) := by
  have hzX :=
    negativePellSquareSolution_x_eq_twice_square_add_one hPell
  constructor
  · intro hclass
    have hpow :=
      pellSolution_pow_x_mod1089_three_classes e hx hclass
    have hzmod :
        ((negativePellSquareSolution hPell).x : ZMod 1089) = 0 ∨
          ((negativePellSquareSolution hPell).x : ZMod 1089) = 195 := by
      rw [hn]
      exact hpow
    rcases hzmod with hzero | h195
    · have hraw :
          (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 1089)) = 0 := by
        rw [← hzX]
        exact hzero
      have hsmall := congrArg
        (ZMod.castHom (by decide : 9 ∣ 1089) (ZMod 9)) hraw
      have hsmall' : 2 * (X : ZMod 9) ^ 2 + 1 = 0 := by
        norm_num at hsmall
        exact hsmall
      have htwice : 2 * (X : ZMod 9) ^ 2 = -1 := by
        linear_combination hsmall'
      have hxSquare : ((X ^ 2 : Nat) : ZMod 9) = 4 := by
        simp only [Nat.cast_pow]
        calc
          (X : ZMod 9) ^ 2 = 10 * (X : ZMod 9) ^ 2 := by
            rw [show (10 : ZMod 9) = 1 by decide]
            ring
          _ = 5 * (2 * (X : ZMod 9) ^ 2) := by ring
          _ = 5 * (-1) := by rw [htwice]
          _ = 4 := by decide
      exact three_exactly_dvd_square_sub_one_of_mod_nine_four hX hxSquare
    · have hraw :
          (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 1089)) = 195 := by
        rw [← hzX]
        exact h195
      have hsmall := congrArg
        (ZMod.castHom (by decide : 9 ∣ 1089) (ZMod 9)) hraw
      have hsmall' : 2 * (X : ZMod 9) ^ 2 + 1 = 6 := by
        norm_num at hsmall
        exact hsmall
      have htwice : 2 * (X : ZMod 9) ^ 2 = 5 := by
        linear_combination hsmall'
      have hxSquare : ((X ^ 2 : Nat) : ZMod 9) = 7 := by
        simp only [Nat.cast_pow]
        calc
          (X : ZMod 9) ^ 2 = 10 * (X : ZMod 9) ^ 2 := by
            rw [show (10 : ZMod 9) = 1 by decide]
            ring
          _ = 5 * (2 * (X : ZMod 9) ^ 2) := by ring
          _ = 5 * 5 := by rw [htwice]
          _ = 7 := by decide
      exact three_exactly_dvd_square_sub_one_of_mod_nine_seven hX hxSquare
  · intro hclass
    have hpow :=
      pellSolution_pow_x_mod1089_eleven_classes e hx hclass
    have hzmod :
        ((negativePellSquareSolution hPell).x : ZMod 1089) = 894 := by
      rw [hn]
      exact hpow
    have hraw :
        (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 1089)) = 894 := by
      rw [← hzX]
      exact hzmod
    have hsmall := congrArg
      (ZMod.castHom (by decide : 121 ∣ 1089) (ZMod 121)) hraw
    have hsmall' : 2 * (X : ZMod 121) ^ 2 + 1 = 47 := by
      norm_num at hsmall
      exact hsmall
    have htwice : 2 * (X : ZMod 121) ^ 2 = 46 := by
      linear_combination hsmall'
    have hxSquare : ((X ^ 2 : Nat) : ZMod 121) = 23 := by
      simp only [Nat.cast_pow]
      calc
        (X : ZMod 121) ^ 2 = 122 * (X : ZMod 121) ^ 2 := by
          rw [show (122 : ZMod 121) = 1 by decide]
          ring
        _ = 61 * (2 * (X : ZMod 121) ^ 2) := by ring
        _ = 61 * 46 := by rw [htwice]
        _ = 23 := by decide
    exact eleven_exactly_dvd_square_sub_one_of_mod_121 hX hxSquare

/-- Every positive negative-Pell solution is obstructed by one of the two
exact-depth witnesses.  Oddness is derived from the source equation and the
fundamental-unit classification, then the six odd classes modulo twelve are
covered exactly. -/
theorem three_or_eleven_exactly_dvd_lower_of_negativePell_of_normOne_mod1089
    {K X W : Nat} (hK : 2 < K)
    (e : Pell.Solution₁ (K : Int)) (hfund : Pell.IsFundamental e)
    (hx : (e.x : ZMod 1089) = 894)
    (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = K * W ^ 2) :
    (3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1) ∨
      (11 ∣ X ^ 2 - 1 ∧ ¬ 11 ^ 2 ∣ X ^ 2 - 1) := by
  obtain ⟨n, hnOdd, hn, _hSign⟩ :=
    negativePell_eq_fundamental_odd_power_and_x_mod_kernel
      hK e hfund hX hW hPell
  have hclassified :=
    negativePell_exactOne_of_normOne_mod1089_by_exponent
      e hx hX hPell hn
  have hnTwo : n % 2 = 1 := Nat.odd_iff.mp hnOdd
  have hnTwelveTwo : n % 12 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 12)]
    exact hnTwo
  have hnLt : n % 12 < 12 := Nat.mod_lt _ (by decide)
  have hclasses :
      (n % 12 = 3 ∨ n % 12 = 5 ∨
        n % 12 = 7 ∨ n % 12 = 9) ∨
      (n % 12 = 1 ∨ n % 12 = 11) := by
    omega
  rcases hclasses with hthree | heleven
  · exact Or.inl (hclassified.1 hthree)
  · exact Or.inr (hclassified.2 heleven)

/-- Complete canonical upper-fibre eliminator for the symbolic
`894 (mod 1089)` certificate. -/
theorem no_pairPellCounterexample_upperKernel_of_normOne_mod1089
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hfund : Pell.IsFundamental e)
    (hx : (e.x : ZMod 1089) = 894)
    (data : PairPellCounterexampleData) (hupper : data.upperKernel = K) :
    False := by
  have hK : 2 < K := by
    have hKOne : 1 < K := by
      simpa [hupper] using data.upperKernel_one_lt
    have hKNeTwo : K ≠ 2 := by
      intro hKTwo
      have htwoDvd : 2 ∣ data.upperKernel * data.upperSquarePart := by
        rw [hupper, hKTwo]
        exact dvd_mul_right 2 data.upperSquarePart
      have hmod :=
        data.upperSupport_prime_mod_four_eq_one Nat.prime_two htwoDvd
      norm_num at hmod
    omega
  have hnegative := data.upper_negativePell
  have hPell :
      data.center ^ 2 + 1 =
        K * (data.upperKernel * data.upperSquarePart) ^ 2 := by
    simpa [hupper] using hnegative.equation.symm
  have hexact :=
    three_or_eleven_exactly_dvd_lower_of_negativePell_of_normOne_mod1089
      hK e hfund hx
      (Nat.zero_lt_of_lt data.center_one_lt)
      hnegative.W_pos hPell
  have hlowerPowerful : PowerfulPos (data.center ^ 2 - 1) :=
    powerfulPos_of_squareCubeNormalForm data.lowerNormalForm
  rcases hexact with hthree | heleven
  · exact hthree.2
      (hlowerPowerful.2 3 Nat.prime_three hthree.1)
  · exact heleven.2
      (hlowerPowerful.2 11 (by norm_num) heleven.1)

/-! ## The symmetric real-coordinate class `195 = -894 (mod 1089)` -/

private theorem normOnePowerStateMod1089_twelve_of_195 :
    normOnePowerStateMod1089 (195 : ZMod 1089) 12 = (1, 0) := by
  decide

private theorem pellSolution_pow_mod1089_periodic_of_x_eq_195
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 195) :
    Function.Periodic
      (fun n : Nat =>
        (((e ^ n).x : ZMod 1089), ((e ^ n).y : ZMod 1089))) 12 := by
  have hstate := pellSolution_pow_state_mod1089 e 12
  rw [hx, normOnePowerStateMod1089_twelve_of_195] at hstate
  have htwelve :
      ((e ^ 12).x : ZMod 1089) = 1 ∧
        ((e ^ 12).y : ZMod 1089) = 0 := by
    simpa using hstate
  intro n
  apply Prod.ext
  · change ((e ^ (n + 12)).x : ZMod 1089) =
      ((e ^ n).x : ZMod 1089)
    rw [pow_add, Pell.Solution₁.x_mul]
    push_cast
    rw [htwelve.1, htwelve.2]
    ring
  · change ((e ^ (n + 12)).y : ZMod 1089) =
      ((e ^ n).y : ZMod 1089)
    rw [pow_add, Pell.Solution₁.y_mul]
    push_cast
    rw [htwelve.1, htwelve.2]
    ring

private theorem pellSolution_pow_x_mod1089_three_classes_of_x_eq_195
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 195) {n : Nat}
    (hn : n % 12 = 1 ∨ n % 12 = 3 ∨
      n % 12 = 9 ∨ n % 12 = 11) :
    (((e ^ n).x : ZMod 1089) = 0 ∨
      ((e ^ n).x : ZMod 1089) = 195) := by
  have hperiod :=
    (pellSolution_pow_mod1089_periodic_of_x_eq_195 e hx).map_mod_nat n
  have hperiodX := congrArg Prod.fst hperiod
  simp only at hperiodX
  have hstate := pellSolution_pow_state_mod1089 e (n % 12)
  rw [hx] at hstate
  rw [← hperiodX, hstate.1]
  rcases hn with h1 | h3 | h9 | h11
  · rw [h1]
    decide
  · rw [h3]
    decide
  · rw [h9]
    decide
  · rw [h11]
    decide

private theorem pellSolution_pow_x_mod1089_eleven_classes_of_x_eq_195
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 195) {n : Nat}
    (hn : n % 12 = 5 ∨ n % 12 = 7) :
    ((e ^ n).x : ZMod 1089) = 894 := by
  have hperiod :=
    (pellSolution_pow_mod1089_periodic_of_x_eq_195 e hx).map_mod_nat n
  have hperiodX := congrArg Prod.fst hperiod
  simp only at hperiodX
  have hstate := pellSolution_pow_state_mod1089 e (n % 12)
  rw [hx] at hstate
  rw [← hperiodX, hstate.1]
  rcases hn with h5 | h7
  · rw [h5]
    decide
  · rw [h7]
    decide

/-- Symmetric exponent classifier for the real-coordinate input
`195 = -894 (mod 1089)`. -/
theorem negativePell_exactOne_of_normOne_mod1089_x_eq_195_by_exponent
    {K X W n : Nat}
    (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 1089) = 195)
    (hX : 0 < X)
    (hPell : X ^ 2 + 1 = K * W ^ 2)
    (hn : negativePellSquareSolution hPell = e ^ n) :
    ((n % 12 = 1 ∨ n % 12 = 3 ∨
        n % 12 = 9 ∨ n % 12 = 11) →
      (3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1)) ∧
    ((n % 12 = 5 ∨ n % 12 = 7) →
      (11 ∣ X ^ 2 - 1 ∧ ¬ 11 ^ 2 ∣ X ^ 2 - 1)) := by
  have hzX :=
    negativePellSquareSolution_x_eq_twice_square_add_one hPell
  constructor
  · intro hclass
    have hpow :=
      pellSolution_pow_x_mod1089_three_classes_of_x_eq_195 e hx hclass
    have hzmod :
        ((negativePellSquareSolution hPell).x : ZMod 1089) = 0 ∨
          ((negativePellSquareSolution hPell).x : ZMod 1089) = 195 := by
      rw [hn]
      exact hpow
    rcases hzmod with hzero | h195
    · have hraw :
          (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 1089)) = 0 := by
        rw [← hzX]
        exact hzero
      have hsmall := congrArg
        (ZMod.castHom (by decide : 9 ∣ 1089) (ZMod 9)) hraw
      have hsmall' : 2 * (X : ZMod 9) ^ 2 + 1 = 0 := by
        norm_num at hsmall
        exact hsmall
      have htwice : 2 * (X : ZMod 9) ^ 2 = -1 := by
        linear_combination hsmall'
      have hxSquare : ((X ^ 2 : Nat) : ZMod 9) = 4 := by
        simp only [Nat.cast_pow]
        calc
          (X : ZMod 9) ^ 2 = 10 * (X : ZMod 9) ^ 2 := by
            rw [show (10 : ZMod 9) = 1 by decide]
            ring
          _ = 5 * (2 * (X : ZMod 9) ^ 2) := by ring
          _ = 5 * (-1) := by rw [htwice]
          _ = 4 := by decide
      exact three_exactly_dvd_square_sub_one_of_mod_nine_four hX hxSquare
    · have hraw :
          (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 1089)) = 195 := by
        rw [← hzX]
        exact h195
      have hsmall := congrArg
        (ZMod.castHom (by decide : 9 ∣ 1089) (ZMod 9)) hraw
      have hsmall' : 2 * (X : ZMod 9) ^ 2 + 1 = 6 := by
        norm_num at hsmall
        exact hsmall
      have htwice : 2 * (X : ZMod 9) ^ 2 = 5 := by
        linear_combination hsmall'
      have hxSquare : ((X ^ 2 : Nat) : ZMod 9) = 7 := by
        simp only [Nat.cast_pow]
        calc
          (X : ZMod 9) ^ 2 = 10 * (X : ZMod 9) ^ 2 := by
            rw [show (10 : ZMod 9) = 1 by decide]
            ring
          _ = 5 * (2 * (X : ZMod 9) ^ 2) := by ring
          _ = 5 * 5 := by rw [htwice]
          _ = 7 := by decide
      exact three_exactly_dvd_square_sub_one_of_mod_nine_seven hX hxSquare
  · intro hclass
    have hpow :=
      pellSolution_pow_x_mod1089_eleven_classes_of_x_eq_195 e hx hclass
    have hzmod :
        ((negativePellSquareSolution hPell).x : ZMod 1089) = 894 := by
      rw [hn]
      exact hpow
    have hraw :
        (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 1089)) = 894 := by
      rw [← hzX]
      exact hzmod
    have hsmall := congrArg
      (ZMod.castHom (by decide : 121 ∣ 1089) (ZMod 121)) hraw
    have hsmall' : 2 * (X : ZMod 121) ^ 2 + 1 = 47 := by
      norm_num at hsmall
      exact hsmall
    have htwice : 2 * (X : ZMod 121) ^ 2 = 46 := by
      linear_combination hsmall'
    have hxSquare : ((X ^ 2 : Nat) : ZMod 121) = 23 := by
      simp only [Nat.cast_pow]
      calc
        (X : ZMod 121) ^ 2 = 122 * (X : ZMod 121) ^ 2 := by
          rw [show (122 : ZMod 121) = 1 by decide]
          ring
        _ = 61 * (2 * (X : ZMod 121) ^ 2) := by ring
        _ = 61 * 46 := by rw [htwice]
        _ = 23 := by decide
    exact eleven_exactly_dvd_square_sub_one_of_mod_121 hX hxSquare

theorem three_or_eleven_exactly_dvd_lower_of_negativePell_of_normOne_mod1089_x_eq_195
    {K X W : Nat} (hK : 2 < K)
    (e : Pell.Solution₁ (K : Int)) (hfund : Pell.IsFundamental e)
    (hx : (e.x : ZMod 1089) = 195)
    (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = K * W ^ 2) :
    (3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1) ∨
      (11 ∣ X ^ 2 - 1 ∧ ¬ 11 ^ 2 ∣ X ^ 2 - 1) := by
  obtain ⟨n, hnOdd, hn, _hSign⟩ :=
    negativePell_eq_fundamental_odd_power_and_x_mod_kernel
      hK e hfund hX hW hPell
  have hclassified :=
    negativePell_exactOne_of_normOne_mod1089_x_eq_195_by_exponent
      e hx hX hPell hn
  have hnTwo : n % 2 = 1 := Nat.odd_iff.mp hnOdd
  have hnTwelveTwo : n % 12 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 12)]
    exact hnTwo
  have hnLt : n % 12 < 12 := Nat.mod_lt _ (by decide)
  have hclasses :
      (n % 12 = 1 ∨ n % 12 = 3 ∨
        n % 12 = 9 ∨ n % 12 = 11) ∨
      (n % 12 = 5 ∨ n % 12 = 7) := by
    omega
  rcases hclasses with hthree | heleven
  · exact Or.inl (hclassified.1 hthree)
  · exact Or.inr (hclassified.2 heleven)

theorem no_pairPellCounterexample_upperKernel_of_normOne_mod1089_x_eq_195
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hfund : Pell.IsFundamental e)
    (hx : (e.x : ZMod 1089) = 195)
    (data : PairPellCounterexampleData) (hupper : data.upperKernel = K) :
    False := by
  have hK : 2 < K := by
    have hKOne : 1 < K := by
      simpa [hupper] using data.upperKernel_one_lt
    have hKNeTwo : K ≠ 2 := by
      intro hKTwo
      have htwoDvd : 2 ∣ data.upperKernel * data.upperSquarePart := by
        rw [hupper, hKTwo]
        exact dvd_mul_right 2 data.upperSquarePart
      have hmod :=
        data.upperSupport_prime_mod_four_eq_one Nat.prime_two htwoDvd
      norm_num at hmod
    omega
  have hnegative := data.upper_negativePell
  have hPell :
      data.center ^ 2 + 1 =
        K * (data.upperKernel * data.upperSquarePart) ^ 2 := by
    simpa [hupper] using hnegative.equation.symm
  have hexact :=
    three_or_eleven_exactly_dvd_lower_of_negativePell_of_normOne_mod1089_x_eq_195
      hK e hfund hx
      (Nat.zero_lt_of_lt data.center_one_lt)
      hnegative.W_pos hPell
  have hlowerPowerful : PowerfulPos (data.center ^ 2 - 1) :=
    powerfulPos_of_squareCubeNormalForm data.lowerNormalForm
  rcases hexact with hthree | heleven
  · exact hthree.2
      (hlowerPowerful.2 3 Nat.prime_three hthree.1)
  · exact heleven.2
      (hlowerPowerful.2 11 (by norm_num) heleven.1)

end Erdos364
