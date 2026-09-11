import Erdos364.SquareMiddle.RightFlankNormOneModNine
import Erdos364.SquareMiddle.Sm2LowerSquareAllocation
import Mathlib.Data.Nat.Periodic

namespace Erdos364

open Pell

/-!
# The `sm2LowerSquare` cell at upper kernel one hundred and one

This module excludes the intersection of the `sm2LowerSquare` source leaf
with the canonical upper-kernel fibre `K = 101`.

The proof first places every divisible negative-Pell source at the exact
norm-one exponent `101 * (2 * s + 1)`.  The squared real coordinate then has
a period-three table modulo `607`.  Every table entry is incompatible with
the leaf equation `X - 1 = y²`.

This is a complete leaf-fibre cell exclusion.  It is not a complete
`K = 101` upper-fibre exclusion and does not close the leaf.
-/

/-- The positive fundamental norm-one Pell solution for discriminant
`101`. -/
def pellOneHundredOne : Pell.Solution₁ (101 : Int) :=
  Pell.Solution₁.mk 201 20 (by norm_num)

/-- `201 + 20 * sqrt 101` is the positive fundamental norm-one solution. -/
theorem pellOneHundredOne_isFundamental :
    Pell.IsFundamental pellOneHundredOne := by
  refine ⟨(by norm_num [pellOneHundredOne]),
    (by norm_num [pellOneHundredOne]), ?_⟩
  intro b hb
  simp only [pellOneHundredOne, Pell.Solution₁.x_mk]
  by_contra hnot
  have hbx_le : b.x ≤ 200 := by omega
  have hprop := b.prop
  have hfactor :
      (101 : Int) ∣ (b.x - 1) * (b.x + 1) := by
    refine ⟨b.y ^ 2, ?_⟩
    nlinarith
  rcases (by norm_num : Prime (101 : Int)).dvd_mul.mp hfactor with
      hminus | hplus
  · obtain ⟨k, hk⟩ := hminus
    have hkOne : k = 1 := by omega
    have hx : b.x = 102 := by omega
    have hySq : b.y ^ 2 = 103 := by
      rw [hx] at hprop
      nlinarith
    have hyLower : -10 ≤ b.y := by
      nlinarith [sq_nonneg (b.y + 11)]
    have hyUpper : b.y ≤ 10 := by
      nlinarith [sq_nonneg (b.y - 11)]
    interval_cases b.y <;> norm_num at hySq
  · obtain ⟨k, hk⟩ := hplus
    have hkOne : k = 1 := by omega
    have hx : b.x = 100 := by omega
    have hySq : b.y ^ 2 = 99 := by
      rw [hx] at hprop
      nlinarith
    have hyLower : -9 ≤ b.y := by
      nlinarith [sq_nonneg (b.y + 10)]
    have hyUpper : b.y ≤ 9 := by
      nlinarith [sq_nonneg (b.y - 10)]
    interval_cases b.y <;> norm_num at hySq

private theorem pellOneHundredOne_pow_y_strictMono :
    StrictMono fun n : Nat => (pellOneHundredOne ^ n).y := by
  intro m n hmn
  have hmnInt : (m : Int) < (n : Int) := by
    exact_mod_cast hmn
  simpa [zpow_natCast] using
    pellOneHundredOne_isFundamental.y_strictMono hmnInt

private theorem oneHundredOne_dvd_normOne_index
    {X W n : Nat} (hDiv : 101 ∣ W)
    (hPell : X ^ 2 + 1 = 101 * W ^ 2)
    (hn : negativePellSquareSolution hPell =
      pellOneHundredOne ^ n) :
    101 ∣ n := by
  obtain ⟨V, hW⟩ := hDiv
  have hzYDvd :
      (101 : Int) ∣ (negativePellSquareSolution hPell).y := by
    refine ⟨2 * (X : Int) * V, ?_⟩
    simp only [negativePellSquareSolution, Pell.Solution₁.y_mk]
    rw [hW]
    push_cast
    ring
  rw [hn] at hzYDvd
  have hproductInt :
      (101 : Int) ∣ (n : Int) * pellOneHundredOne.y :=
    (kernel_dvd_pellSolutionY_iff pellOneHundredOne).mp hzYDvd
  have hproductNat : 101 ∣ n * 20 := by
    have hy : pellOneHundredOne.y = 20 := rfl
    rw [hy] at hproductInt
    exact_mod_cast hproductInt
  exact
    (by norm_num : Nat.Coprime 101 20).dvd_of_dvd_mul_right hproductNat

/-- Complete source-depth recurrence for the divisible negative-Pell
`K = 101` fibre. -/
theorem negativePellOneHundredOne_normOne_recurrence
    {X W : Nat} (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = 101 * W ^ 2)
    (hDiv : 101 ∣ W) :
    ∃! s : Nat,
      negativePellSquareSolution hPell =
        pellOneHundredOne ^ (101 * (2 * s + 1)) := by
  obtain ⟨n, hnOdd, hn, _hSign⟩ :=
    negativePell_eq_fundamental_odd_power_and_x_mod_kernel
      (by norm_num : 2 < 101)
      pellOneHundredOne pellOneHundredOne_isFundamental
      hX hW hPell
  have hnDiv : 101 ∣ n :=
    oneHundredOne_dvd_normOne_index hDiv hPell hn
  obtain ⟨m, rfl⟩ := hnDiv
  have hmOdd : Odd m := Nat.Odd.of_mul_right hnOdd
  obtain ⟨s, rfl⟩ := hmOdd
  refine ⟨s, hn, ?_⟩
  intro s' hs'
  have hpowers :
      pellOneHundredOne ^ (101 * (2 * s + 1)) =
        pellOneHundredOne ^ (101 * (2 * s' + 1)) := by
    rw [← hn, hs']
  have hindices :
      101 * (2 * s + 1) = 101 * (2 * s' + 1) :=
    pellOneHundredOne_pow_y_strictMono.injective
      (congrArg Pell.Solution₁.y hpowers)
  omega

/-- Real coordinate of the exact norm-one source-depth subsequence. -/
def negativePellOneHundredOneNormOneX (s : Nat) : Int :=
  (pellOneHundredOne ^ (101 * (2 * s + 1))).x

private theorem pellOneHundredOne_period_sixHundredSeven :
    ((((pellOneHundredOne ^ 606).x : Int) : ZMod 607) = 1) ∧
      ((((pellOneHundredOne ^ 606).y : Int) : ZMod 607) = 0) := by
  set_option maxRecDepth 20000 in
    decide

/-- The exact source-depth real-coordinate sequence has period three modulo
`607`. -/
theorem negativePellOneHundredOneNormOneX_mod_sixHundredSeven_periodic :
    Function.Periodic
      (fun s : Nat =>
        (negativePellOneHundredOneNormOneX s : ZMod 607)) 3 := by
  intro s
  change
    (((pellOneHundredOne ^
      (101 * (2 * (s + 3) + 1))).x : Int) : ZMod 607) =
      (((pellOneHundredOne ^
        (101 * (2 * s + 1))).x : Int) : ZMod 607)
  rw [show 101 * (2 * (s + 3) + 1) =
      101 * (2 * s + 1) + 606 by omega]
  rw [pow_add, Pell.Solution₁.x_mul]
  push_cast
  rw [pellOneHundredOne_period_sixHundredSeven.1,
    pellOneHundredOne_period_sixHundredSeven.2]
  ring

/-- Complete period-three table for the source-depth norm-one real
coordinate modulo `607`. -/
theorem negativePellOneHundredOneNormOneX_state_mod_sixHundredSeven
    (s : Nat) :
    (s % 3 = 0 ∧
        (negativePellOneHundredOneNormOneX s : ZMod 607) = 303) ∨
      (s % 3 = 1 ∧
        (negativePellOneHundredOneNormOneX s : ZMod 607) = 1) ∨
      (s % 3 = 2 ∧
        (negativePellOneHundredOneNormOneX s : ZMod 607) = 303) := by
  have hx :=
    negativePellOneHundredOneNormOneX_mod_sixHundredSeven_periodic.map_mod_nat
      s
  rw [← hx]
  generalize hr : s % 3 = r
  have hrlt : r < 3 := by
    rw [← hr]
    exact Nat.mod_lt _ (by decide)
  set_option maxRecDepth 20000 in
    interval_cases r <;> decide

private instance primeSixHundredSevenFactK101 :
    Fact (Nat.Prime 607) :=
  ⟨by norm_num⟩

private theorem ninetyTwo_not_square_mod_sixHundredSeven :
    ¬ IsSquare (92 : ZMod 607) := by
  set_option maxRecDepth 20000 in
    decide

private theorem fiveHundredThirteen_not_square_mod_sixHundredSeven :
    ¬ IsSquare (513 : ZMod 607) := by
  set_option maxRecDepth 20000 in
    decide

private theorem negOne_not_square_mod_sixHundredSeven :
    ¬ IsSquare (-1 : ZMod 607) := by
  set_option maxRecDepth 20000 in
    decide

private theorem no_square_sub_one_of_normOne_real_threeHundredThree
    (x : ZMod 607) (h : 2 * x ^ 2 + 1 = 303) :
    ¬ IsSquare (x - 1) := by
  have htwo : 2 * x ^ 2 = 302 := by
    linear_combination h
  have hinv : (304 * 2 : ZMod 607) = 1 := by decide
  have hsq : x ^ 2 = 151 := by
    calc
      x ^ 2 = 1 * x ^ 2 := by ring
      _ = (304 * 2 : ZMod 607) * x ^ 2 := by rw [hinv]
      _ = 304 * (2 * x ^ 2) := by ring
      _ = 304 * 302 := by rw [htwo]
      _ = 151 := by decide
  have hfactor : (x - 93) * (x + 93) = 0 := by
    calc
      (x - 93) * (x + 93) = x ^ 2 - 93 ^ 2 := by ring
      _ = 0 := by rw [hsq]; decide
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · have hx : x = 93 := sub_eq_zero.mp hminus
    rw [hx]
    norm_num
    exact ninetyTwo_not_square_mod_sixHundredSeven
  · have hx : x = -93 := eq_neg_of_add_eq_zero_left hplus
    rw [hx]
    norm_num
    exact fiveHundredThirteen_not_square_mod_sixHundredSeven

private theorem no_square_sub_one_of_normOne_real_one
    (x : ZMod 607) (h : 2 * x ^ 2 + 1 = 1) :
    ¬ IsSquare (x - 1) := by
  have htwo : 2 * x ^ 2 = 0 := by
    linear_combination h
  have hinv : (304 * 2 : ZMod 607) = 1 := by decide
  have hsq : x ^ 2 = 0 := by
    calc
      x ^ 2 = 1 * x ^ 2 := by ring
      _ = (304 * 2 : ZMod 607) * x ^ 2 := by rw [hinv]
      _ = 304 * (2 * x ^ 2) := by ring
      _ = 304 * 0 := by rw [htwo]
      _ = 0 := by ring
  have hmul : x * x = 0 := by
    simpa [pow_two] using hsq
  have hx : x = 0 := (mul_eq_zero.mp hmul).elim id id
  rw [hx]
  norm_num
  exact negOne_not_square_mod_sixHundredSeven

/-- Every divisible negative-Pell `K = 101` source has a nonsquare
predecessor modulo `607`. -/
theorem
    divisibleNatNegativePell_oneHundredOne_center_sub_one_not_square
    {X W : Nat} (h : DivisibleNatNegativePell 101 X W) :
    ¬ IsSquare ((((X : Int) - 1 : Int) : ZMod 607)) := by
  have hPell : X ^ 2 + 1 = 101 * W ^ 2 := h.equation.symm
  obtain ⟨s, hrec, _hunique⟩ :=
    negativePellOneHundredOne_normOne_recurrence
      (Nat.zero_lt_of_lt h.X_one_lt) h.W_pos hPell h.K_dvd_W
  have hreal :
      (negativePellSquareSolution hPell).x =
        2 * (X : Int) ^ 2 + 1 := by
    simp only [negativePellSquareSolution, Pell.Solution₁.x_mk]
    have hz :
        (X : Int) ^ 2 + 1 = 101 * (W : Int) ^ 2 := by
      exact_mod_cast hPell
    linear_combination -hz
  have hcoord := congrArg Pell.Solution₁.x hrec
  have hcoordMod :=
    congrArg (fun z : Int => (z : ZMod 607)) hcoord
  rw [hreal] at hcoordMod
  push_cast at hcoordMod
  change
    (2 * (X : ZMod 607) ^ 2 + 1) =
      (negativePellOneHundredOneNormOneX s : ZMod 607) at hcoordMod
  push_cast
  change ¬ IsSquare ((X : ZMod 607) - 1)
  rcases
      negativePellOneHundredOneNormOneX_state_mod_sixHundredSeven s with
      hzero | hone | htwo
  · rw [hzero.2] at hcoordMod
    exact
      no_square_sub_one_of_normOne_real_threeHundredThree _ hcoordMod
  · rw [hone.2] at hcoordMod
    exact no_square_sub_one_of_normOne_real_one _ hcoordMod
  · rw [htwo.2] at hcoordMod
    exact
      no_square_sub_one_of_normOne_real_threeHundredThree _ hcoordMod

/-- The complete `sm2LowerSquare` leaf-fibre cell at canonical upper kernel
`101` is empty. -/
theorem Sm2LowerSquareAllocation.upperKernel_ne_oneHundredOne
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.upperKernel ≠ 101 := by
  intro hK
  have hnegative :
      DivisibleNatNegativePell 101 data.center
        (data.upperKernel * data.upperSquarePart) := by
    simpa [hK] using data.upper_negativePell
  have hnot :=
    divisibleNatNegativePell_oneHundredOne_center_sub_one_not_square
      hnegative
  apply hnot
  refine ⟨(allocation.y : ZMod 607), ?_⟩
  have hcenterInt :
      (data.center : Int) - 1 = (allocation.y : Int) ^ 2 := by
    rw [allocation.center_eq]
    push_cast
    ring
  have hcast :=
    congrArg (fun z : Int => (z : ZMod 607)) hcenterInt
  push_cast at hcast
  simpa [pow_two] using hcast

end Erdos364
