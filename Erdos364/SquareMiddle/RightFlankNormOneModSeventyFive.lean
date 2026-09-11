import Erdos364.SquareMiddle.RightFlankNormOneModNine
import Mathlib.Data.Nat.Periodic

namespace Erdos364

open Pell

/-!
# Generic modulo-75 right-flank obstruction

This module isolates the two-prime mechanism shared by the
`K = 617` and `K = 1913` candidates.  It uses every positive negative-Pell
solution, not a source-depth subsequence.
-/

private theorem pellSolution_cube_x
    {K : Nat} (e : Pell.Solution₁ (K : Int)) :
    (e ^ 3).x = 4 * e.x ^ 3 - 3 * e.x := by
  rw [show e ^ 3 = (e ^ 2) * e by
      rw [show (3 : Nat) = 2 + 1 by norm_num, pow_succ],
    Pell.Solution₁.x_mul, pow_two, Pell.Solution₁.x_mul,
    Pell.Solution₁.y_mul]
  linear_combination -3 * e.x * e.prop

private theorem pellSolution_cube_y
    {K : Nat} (e : Pell.Solution₁ (K : Int)) :
    (e ^ 3).y = (4 * e.x ^ 2 - 1) * e.y := by
  rw [show e ^ 3 = (e ^ 2) * e by
      rw [show (3 : Nat) = 2 + 1 by norm_num, pow_succ],
    Pell.Solution₁.y_mul, pow_two, Pell.Solution₁.x_mul,
    Pell.Solution₁.y_mul]
  linear_combination -e.y * e.prop

private theorem pellSolution_cube_mod_twentyFive_of_x_eq_thirteen
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 25) = 13) :
    (((e ^ 3).x : Int) : ZMod 25) = -1 ∧
      (((e ^ 3).y : Int) : ZMod 25) = 0 := by
  constructor
  · rw [pellSolution_cube_x]
    push_cast
    rw [hx]
    decide
  · rw [pellSolution_cube_y]
    push_cast
    rw [hx]
    norm_num
    rw [show (675 : ZMod 25) = 0 by decide]
    ring

private theorem pellSolution_pow_six_mod_twentyFive_of_x_eq_thirteen
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 25) = 13) :
    (((e ^ 6).x : Int) : ZMod 25) = 1 ∧
      (((e ^ 6).y : Int) : ZMod 25) = 0 := by
  have hcube :=
    pellSolution_cube_mod_twentyFive_of_x_eq_thirteen e hx
  rw [show e ^ 6 = (e ^ 3) * (e ^ 3) by
      rw [← pow_add],
    Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
  push_cast
  rw [hcube.1, hcube.2]
  constructor <;> ring

private theorem pellSolution_pow_x_mod_twentyFive_periodic
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 25) = 13) :
    Function.Periodic
      (fun n : Nat => (((e ^ n).x : Int) : ZMod 25)) 6 := by
  intro n
  change
    (((e ^ (n + 6)).x : Int) : ZMod 25) =
      (((e ^ n).x : Int) : ZMod 25)
  rw [pow_add, Pell.Solution₁.x_mul]
  push_cast
  rw [
    (pellSolution_pow_six_mod_twentyFive_of_x_eq_thirteen e hx).1,
    (pellSolution_pow_six_mod_twentyFive_of_x_eq_thirteen e hx).2]
  ring

private theorem pellSolution_pow_five_x_mod_twentyFive_of_x_eq_thirteen
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 25) = 13) :
    (((e ^ 5).x : Int) : ZMod 25) = 13 := by
  have hcube :=
    pellSolution_cube_mod_twentyFive_of_x_eq_thirteen e hx
  have heSqX : (((e ^ 2).x : Int) : ZMod 25) = 12 := by
    rw [pow_two, Pell.Solution₁.x_mul]
    push_cast
    have hprop := congrArg (fun value : Int => (value : ZMod 25)) e.prop
    push_cast at hprop
    rw [hx] at hprop ⊢
    have hKy :
        (K : ZMod 25) * (e.y : ZMod 25) ^ 2 = 18 := by
      calc
        (K : ZMod 25) * (e.y : ZMod 25) ^ 2 =
            13 ^ 2 - 1 := by linear_combination -hprop
        _ = 18 := by decide
    have hKy' :
        (K : ZMod 25) * ((e.y : ZMod 25) * (e.y : ZMod 25)) = 18 := by
      simpa [pow_two] using hKy
    rw [hKy']
    decide
  rw [show e ^ 5 = (e ^ 3) * (e ^ 2) by
      rw [← pow_add],
    Pell.Solution₁.x_mul]
  push_cast
  rw [hcube.1, hcube.2, heSqX]
  simp
  decide

private theorem pellSolution_pow_x_mod_twentyFive_of_odd_not_three_dvd
    {K n : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod 25) = 13)
    (hnOdd : Odd n) (hnThree : ¬ 3 ∣ n) :
    (((e ^ n).x : Int) : ZMod 25) = 13 := by
  have hperiod :=
    (pellSolution_pow_x_mod_twentyFive_periodic e hx).map_mod_nat n
  rw [← hperiod]
  have hnlt : n % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases hres : n % 6
  · have : ¬ Odd n := by
      rw [Nat.odd_iff]
      omega
    exact (this hnOdd).elim
  · simpa [hres] using hx
  · have : ¬ Odd n := by
      rw [Nat.odd_iff]
      omega
    exact (this hnOdd).elim
  · have : 3 ∣ n := by
      use n / 3
      have hdivision := Nat.mod_add_div n 3
      omega
    exact (hnThree this).elim
  · have : ¬ Odd n := by
      rw [Nat.odd_iff]
      omega
    exact (this hnOdd).elim
  · exact
      pellSolution_pow_five_x_mod_twentyFive_of_x_eq_thirteen e hx

private theorem pellSolution_cube_x_mod_nine_of_three_dvd_x
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (3 : Int) ∣ e.x) :
    (((e ^ 3).x : Int) : ZMod 9) = 0 := by
  obtain ⟨c, hc⟩ := hx
  rw [pellSolution_cube_x, hc]
  push_cast
  ring_nf
  rw [show (9 : ZMod 9) = 0 by decide,
    show (108 : ZMod 9) = 0 by decide]
  ring

private theorem three_exactly_dvd_of_square_real_mod_nine
    {X : Nat} (hX : 0 < X)
    (hreal : (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 9)) = 0) :
    3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1 := by
  have hleft : 2 * (X : ZMod 9) ^ 2 + 1 = 0 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_one, Int.cast_ofNat] using hreal
  have htwice : 2 * (X : ZMod 9) ^ 2 = -1 := by
    linear_combination hleft
  have hxSquare : ((X ^ 2 : Nat) : ZMod 9) = (4 : Nat) := by
    simp only [Nat.cast_pow]
    calc
      (X : ZMod 9) ^ 2 = 10 * (X : ZMod 9) ^ 2 := by
        rw [show (10 : ZMod 9) = 1 by decide]
        ring
      _ = 5 * (2 * (X : ZMod 9) ^ 2) := by ring
      _ = 5 * (-1) := by rw [htwice]
      _ = 4 := by decide
  have hmod : X ^ 2 ≡ 4 [MOD 9] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hxSquare
  have hxOne : 1 ≤ X ^ 2 := by nlinarith
  constructor
  · apply (Nat.modEq_iff_dvd' hxOne).mp
    have hfourOne : 4 ≡ 1 [MOD 3] := by decide
    exact ((hmod.of_dvd (by decide : 3 ∣ 9)).trans hfourOne).symm
  · intro hnine
    have hone : 1 ≡ X ^ 2 [MOD 9] :=
      (Nat.modEq_iff_dvd' hxOne).mpr (by
        norm_num at hnine ⊢
        exact hnine)
    have hbad : 1 ≡ 4 [MOD 9] := hone.trans hmod
    norm_num [Nat.ModEq] at hbad

private theorem five_exactly_dvd_of_square_real_mod_twentyFive
    {X : Nat} (hX : 0 < X)
    (hreal : (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 25)) = 13) :
    5 ∣ X ^ 2 - 1 ∧ ¬ 5 ^ 2 ∣ X ^ 2 - 1 := by
  have hleft : 2 * (X : ZMod 25) ^ 2 + 1 = 13 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_one, Int.cast_ofNat] using hreal
  have htwice : 2 * (X : ZMod 25) ^ 2 = 12 := by
    linear_combination hleft
  have hxSquare : ((X ^ 2 : Nat) : ZMod 25) = (6 : Nat) := by
    simp only [Nat.cast_pow]
    calc
      (X : ZMod 25) ^ 2 = 26 * (X : ZMod 25) ^ 2 := by
        rw [show (26 : ZMod 25) = 1 by decide]
        ring
      _ = 13 * (2 * (X : ZMod 25) ^ 2) := by ring
      _ = 13 * 12 := by rw [htwice]
      _ = 6 := by decide
  have hmod : X ^ 2 ≡ 6 [MOD 25] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hxSquare
  have hxOne : 1 ≤ X ^ 2 := by nlinarith
  constructor
  · apply (Nat.modEq_iff_dvd' hxOne).mp
    have hsixOne : 6 ≡ 1 [MOD 5] := by decide
    exact ((hmod.of_dvd (by decide : 5 ∣ 25)).trans hsixOne).symm
  · intro htwentyFive
    have hone : 1 ≡ X ^ 2 [MOD 25] :=
      (Nat.modEq_iff_dvd' hxOne).mpr (by
        norm_num at htwentyFive ⊢
        exact htwentyFive)
    have hbad : 1 ≡ 6 [MOD 25] := hone.trans hmod
    norm_num [Nat.ModEq] at hbad

/--
If the real coordinate of a positive fundamental norm-one solution is
`63 mod 75`, every positive negative-Pell solution has an exact-one witness
at `3` or `5`.
-/
theorem three_or_five_exactly_dvd_lower_of_negativePell_of_normOne_modSeventyFive
    {K X W : Nat} (hK : 2 < K)
    (e : Pell.Solution₁ (K : Int)) (hfund : Pell.IsFundamental e)
    (hsixtyThree : (e.x : ZMod 75) = 63)
    (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = K * W ^ 2) :
    (3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1) ∨
      (5 ∣ X ^ 2 - 1 ∧ ¬ 5 ^ 2 ∣ X ^ 2 - 1) := by
  obtain ⟨n, hnOdd, hn, _heSign⟩ :=
    negativePell_eq_fundamental_odd_power_and_x_mod_kernel
      hK e hfund hX hW hPell
  have hzX :
      (negativePellSquareSolution hPell).x =
        2 * (X : Int) ^ 2 + 1 := by
    simp only [negativePellSquareSolution, Pell.Solution₁.x_mk]
    have hz : (X : Int) ^ 2 + 1 = K * (W : Int) ^ 2 := by
      exact_mod_cast hPell
    linarith
  have hxTwentyFive : (e.x : ZMod 25) = 13 := by
    have h := congrArg
      (ZMod.castHom (by decide : 25 ∣ 75) (ZMod 25)) hsixtyThree
    norm_num at h ⊢
    exact h
  have hxThree : (e.x : ZMod 3) = 0 := by
    have h := congrArg
      (ZMod.castHom (by decide : 3 ∣ 75) (ZMod 3)) hsixtyThree
    norm_num at h ⊢
    exact h
  by_cases hnThree : 3 ∣ n
  · left
    obtain ⟨m, hm⟩ := hnThree
    have hmOdd : Odd m := by
      rw [hm] at hnOdd
      exact Nat.Odd.of_mul_right hnOdd
    have hthreeDvdX : (3 : Int) ∣ e.x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd e.x 3).mp hxThree
    have hcubeZero :
        (((e ^ 3).x : Int) : ZMod 9) = 0 :=
      pellSolution_cube_x_mod_nine_of_three_dvd_x e hthreeDvdX
    have hpowerZero :
        (((e ^ n).x : Int) : ZMod 9) = 0 := by
      rw [hm, pow_mul]
      exact
        pellSolution_pow_odd_x_mod_nine_of_x_eq_zero
          (e ^ 3) hcubeZero hmOdd
    apply three_exactly_dvd_of_square_real_mod_nine hX
    rw [← hzX, hn]
    exact hpowerZero
  · right
    have hpowerThirteen :
        (((e ^ n).x : Int) : ZMod 25) = 13 :=
      pellSolution_pow_x_mod_twentyFive_of_odd_not_three_dvd
        e hxTwentyFive hnOdd hnThree
    apply five_exactly_dvd_of_square_real_mod_twentyFive hX
    rw [← hzX, hn]
    exact hpowerThirteen

/--
Complete canonical fixed-upper-fibre eliminator for the modulo-75
fundamental-coordinate certificate.
-/
theorem no_pairPellCounterexample_upperKernel_of_normOne_modSeventyFive
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hfund : Pell.IsFundamental e)
    (hsixtyThree : (e.x : ZMod 75) = 63)
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
    three_or_five_exactly_dvd_lower_of_negativePell_of_normOne_modSeventyFive
      hK e hfund hsixtyThree
      (Nat.zero_lt_of_lt data.center_one_lt)
      hnegative.W_pos hPell
  have hlowerPowerful : PowerfulPos (data.center ^ 2 - 1) :=
    powerfulPos_of_squareCubeNormalForm data.lowerNormalForm
  rcases hexact with hthree | hfive
  · exact hthree.2
      (hlowerPowerful.2 3 Nat.prime_three hthree.1)
  · exact hfive.2
      (hlowerPowerful.2 5 (by norm_num) hfive.1)

end Erdos364
