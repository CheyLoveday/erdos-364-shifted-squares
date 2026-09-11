import Erdos364.SquareMiddle.PellDivisibilityPrime
import Erdos364.SquareMiddle.RightFlankConsequences

namespace Erdos364

open Pell

/-!
# Generic norm-one modulo-nine right-flank obstruction

This module extracts the arithmetic mechanism used by the proved `K = 5`
fibre.  Let `e = a + b * sqrt K` be any positive fundamental norm-one Pell
solution.  A positive solution of

`X ^ 2 + 1 = K * W ^ 2`

squares to a positive norm-one solution and hence to a power of `e`.  The
source equation forces that exponent to be odd when `2 < K`; no parity or
sign condition is accepted as certificate input.  If `a` is zero modulo
nine, every such odd power has real coordinate zero modulo nine, forcing
`3` to divide `X ^ 2 - 1` exactly once.

The final theorem excludes one complete canonical upper-kernel fibre at a
time.  It does not prove the universal `PellShiftClosed` assertion.
-/

/-- The norm-one Pell solution obtained by squaring a positive solution of
the negative-Pell equation `X² + 1 = K W²`. -/
def negativePellSquareSolution {K X W : Nat}
    (hPell : X ^ 2 + 1 = K * W ^ 2) :
    Pell.Solution₁ (K : Int) :=
  Pell.Solution₁.mk
    ((X : Int) ^ 2 + K * W ^ 2)
    (2 * X * W)
    (by
      have hz : (X : Int) ^ 2 + 1 = K * (W : Int) ^ 2 := by
        exact_mod_cast hPell
      have hnegative : (X : Int) ^ 2 - K * W ^ 2 = -1 := by
        linarith
      calc
        ((X : Int) ^ 2 + K * W ^ 2) ^ 2 -
              K * (2 * (X : Int) * W) ^ 2 =
            ((X : Int) ^ 2 - K * W ^ 2) ^ 2 := by ring
        _ = (-1 : Int) ^ 2 := by rw [hnegative]
        _ = 1 := by norm_num)

/-- The source equation derives both the odd power and the sign of the
fundamental real coordinate modulo `K`.  Neither fact is a certificate
field. -/
theorem negativePell_eq_fundamental_odd_power_and_x_mod_kernel
    {K X W : Nat} (hK : 2 < K)
    (e : Pell.Solution₁ (K : Int)) (hfund : Pell.IsFundamental e)
    (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = K * W ^ 2) :
    ∃ n : Nat,
      Odd n ∧
        negativePellSquareSolution hPell = e ^ n ∧
          (e.x : ZMod K) = -1 := by
  let z := negativePellSquareSolution hPell
  have hzx : 0 < z.x := by
    simp only [z, negativePellSquareSolution, Pell.Solution₁.x_mk]
    positivity
  have hzy : 0 ≤ z.y := by
    simp only [z, negativePellSquareSolution, Pell.Solution₁.y_mk]
    positivity
  obtain ⟨n, hn⟩ := hfund.eq_pow_of_nonneg hzx hzy
  have hsourceK : (X : ZMod K) ^ 2 + 1 = 0 := by
    have h := congrArg (fun value : Nat => (value : ZMod K)) hPell
    push_cast at h
    simpa only [ZMod.natCast_self, zero_mul] using h
  have hzK : (z.x : ZMod K) = -1 := by
    simp only [z, negativePellSquareSolution, Pell.Solution₁.x_mk]
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero]
    exact eq_neg_of_add_eq_zero_left hsourceK
  have hpowK : (e.x : ZMod K) ^ n = -1 := by
    calc
      (e.x : ZMod K) ^ n = ((e ^ n).x : ZMod K) :=
        (pellSolution_pow_mod_kernel_pair e n).1.symm
      _ = (z.x : ZMod K) := by rw [hn]
      _ = -1 := hzK
  have heSqK : (e.x : ZMod K) ^ 2 = 1 := by
    have h := congrArg (fun value : Int => (value : ZMod K)) e.prop
    push_cast at h
    simpa only [ZMod.natCast_self, zero_mul, sub_zero] using h
  have hnOdd : Odd n := by
    rcases n.even_or_odd with hnEven | hnOdd
    · obtain ⟨m, rfl⟩ := hnEven
      rw [show m + m = 2 * m by omega, pow_mul, heSqK, one_pow] at hpowK
      letI : Fact (2 < K) := ⟨hK⟩
      exact (ZMod.neg_one_ne_one hpowK.symm).elim
    · exact hnOdd
  have heSign : (e.x : ZMod K) = -1 := by
    have hoddPow : (e.x : ZMod K) ^ n = (e.x : ZMod K) := by
      obtain ⟨m, rfl⟩ := hnOdd
      rw [pow_add, pow_mul, heSqK]
      simp
    rw [← hoddPow]
    exact hpowK
  exact ⟨n, hnOdd, hn, heSign⟩

/-- If the real coordinate of a norm-one solution is zero modulo nine, then
the real coordinate of every odd power is zero modulo nine. -/
theorem pellSolution_pow_odd_x_mod_nine_of_x_eq_zero
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hzero : (e.x : ZMod 9) = 0) {n : Nat} (hn : Odd n) :
    ((e ^ n).x : ZMod 9) = 0 := by
  have hprop := congrArg (fun value : Int => (value : ZMod 9)) e.prop
  push_cast at hprop
  have hkernelY : (K : ZMod 9) * (e.y : ZMod 9) ^ 2 = -1 := by
    rw [hzero] at hprop
    linear_combination -hprop
  have heSqX : ((e ^ 2).x : ZMod 9) = -1 := by
    rw [pow_two, Pell.Solution₁.x_mul]
    push_cast
    rw [hzero]
    have hkernelY' :
        (K : ZMod 9) * ((e.y : ZMod 9) * (e.y : ZMod 9)) = -1 := by
      simpa [pow_two] using hkernelY
    rw [hkernelY']
    ring
  have heSqY : ((e ^ 2).y : ZMod 9) = 0 := by
    rw [pow_two, Pell.Solution₁.y_mul]
    push_cast
    rw [hzero]
    ring
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero =>
      simpa using hzero
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        pow_add, Pell.Solution₁.x_mul]
      push_cast
      rw [ih, heSqX, heSqY]
      ring

/-- Generic arithmetic engine: if a positive fundamental norm-one solution
has real coordinate zero modulo nine, every positive solution of
`X² + 1 = K W²` has exactly one factor of three in the opposite flank. -/
theorem three_exactly_dvd_lower_of_negativePell_of_normOne_modNine
    {K X W : Nat} (hK : 2 < K)
    (e : Pell.Solution₁ (K : Int)) (hfund : Pell.IsFundamental e)
    (hzero : (e.x : ZMod 9) = 0)
    (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = K * W ^ 2) :
    3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1 := by
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
  have hleftNineRaw :
      (((2 * (X : Int) ^ 2 + 1 : Int) : ZMod 9)) = 0 := by
    rw [← hzX, hn]
    exact pellSolution_pow_odd_x_mod_nine_of_x_eq_zero e hzero hnOdd
  have hleftNine : 2 * (X : ZMod 9) ^ 2 + 1 = 0 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_one, Int.cast_ofNat] using hleftNineRaw
  have htwiceNine : 2 * (X : ZMod 9) ^ 2 = -1 := by
    linear_combination hleftNine
  have hxSquareNine : ((X ^ 2 : Nat) : ZMod 9) = (4 : Nat) := by
    simp only [Nat.cast_pow]
    calc
      (X : ZMod 9) ^ 2 = 10 * (X : ZMod 9) ^ 2 := by
        rw [show (10 : ZMod 9) = 1 by decide]
        ring
      _ = 5 * (2 * (X : ZMod 9) ^ 2) := by ring
      _ = 5 * (-1) := by rw [htwiceNine]
      _ = 4 := by decide
  have hmodNine : X ^ 2 ≡ 4 [MOD 9] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hxSquareNine
  have hxOne : 1 ≤ X ^ 2 := by nlinarith
  constructor
  · apply (Nat.modEq_iff_dvd' hxOne).mp
    have hfourOne : 4 ≡ 1 [MOD 3] := by decide
    exact ((hmodNine.of_dvd (by decide : 3 ∣ 9)).trans hfourOne).symm
  · intro hnine
    have hone : 1 ≡ X ^ 2 [MOD 9] :=
      (Nat.modEq_iff_dvd' hxOne).mpr (by
        norm_num at hnine ⊢
        exact hnine)
    have hbad : 1 ≡ 4 [MOD 9] := hone.trans hmodNine
    norm_num [Nat.ModEq] at hbad

/-- Complete canonical fibre eliminator.  Its reusable certificate contains
only an explicit positive fundamental norm-one solution for the upper kernel
and the proof that its real coordinate is zero modulo nine. -/
theorem no_pairPellCounterexample_upperKernel_of_normOne_modNine
    {K : Nat} (e : Pell.Solution₁ (K : Int))
    (hfund : Pell.IsFundamental e) (hzero : (e.x : ZMod 9) = 0)
    (data : PairPellCounterexampleData) (hupper : data.upperKernel = K) :
    False := by
  have hK : 2 < K := by
    have hKOne : 1 < K := by simpa [hupper] using data.upperKernel_one_lt
    have hKNeTwo : K ≠ 2 := by
      intro hKTwo
      have htwoDvd : 2 ∣ data.upperKernel * data.upperSquarePart := by
        rw [hupper, hKTwo]
        exact dvd_mul_right 2 data.upperSquarePart
      have hmod := data.upperSupport_prime_mod_four_eq_one Nat.prime_two htwoDvd
      norm_num at hmod
    omega
  have hnegative := data.upper_negativePell
  have hPell :
      data.center ^ 2 + 1 =
        K * (data.upperKernel * data.upperSquarePart) ^ 2 := by
    simpa [hupper] using hnegative.equation.symm
  have hexact :=
    three_exactly_dvd_lower_of_negativePell_of_normOne_modNine
      hK e hfund hzero
      (Nat.zero_lt_of_lt data.center_one_lt)
      hnegative.W_pos hPell
  have hlowerPowerful : PowerfulPos (data.center ^ 2 - 1) :=
    powerfulPos_of_squareCubeNormalForm data.lowerNormalForm
  exact hexact.2 (hlowerPowerful.2 3 Nat.prime_three hexact.1)

end Erdos364
