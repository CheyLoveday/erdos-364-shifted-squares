import Erdos364.SquareMiddle.RightFlankNormOneModNine

namespace Erdos364

open Pell

/-!
# A square-plus-one family of excluded upper kernels

For positive `t` and `K = t² + 1`, the explicit norm-one solution

`(2t² + 1) + 2t * sqrt K`

is fundamental.  When `t = 2` or `16` modulo `18`, its real coordinate is
zero modulo nine, so the generic right-flank obstruction excludes every
canonical package in this family.

This is a family of fixed upper-kernel fibre exclusions.  It does not close
an arbitrary upper kernel, a source leaf, `PellShiftClosed`, or the global
square-middle problem.
-/

/-- The square-plus-one discriminant selected by the family parameter. -/
def squarePlusOneKernel (t : Nat) : Nat :=
  t ^ 2 + 1

/-- The explicit norm-one Pell solution for the discriminant `t² + 1`. -/
def pellSquarePlusOne (t : Nat) :
    Pell.Solution₁ (squarePlusOneKernel t : Int) :=
  Pell.Solution₁.mk
    (2 * (t : Int) ^ 2 + 1)
    (2 * (t : Int))
    (by
      simp only [squarePlusOneKernel]
      push_cast
      ring)

/-- Elementary minimality inequality for the square-plus-one discriminant. -/
private theorem squarePlusOne_minimal
    {T x y : Int} (hT : 0 < T) (hx : 1 < x) (hy : 0 < y)
    (heq : x ^ 2 - (T ^ 2 + 1) * y ^ 2 = 1) :
    2 * T ^ 2 + 1 ≤ x := by
  have hxpos : 0 < x := lt_trans Int.zero_lt_one hx
  have hTy_nonneg : 0 ≤ T * y := mul_nonneg hT.le hy.le
  have hTy_lt_x : T * y < x := by
    apply (sq_lt_sq₀ hTy_nonneg hxpos.le).mp
    nlinarith
  have hstep : T * y + 1 ≤ x := by omega
  have hstep_nonneg : 0 ≤ T * y + 1 := by positivity
  have hsqle : (T * y + 1) ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ hstep_nonneg hxpos.le).mpr hstep
  have hy_lower : 2 * T ≤ y := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hy_lower hT.le
  nlinarith

/-- For positive `t`, the displayed square-plus-one Pell solution is
fundamental. -/
theorem pellSquarePlusOne_isFundamental {t : Nat} (ht : 0 < t) :
    Pell.IsFundamental (pellSquarePlusOne t) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [pellSquarePlusOne, Pell.Solution₁.x_mk]
    have htInt : 0 < (t : Int) := by exact_mod_cast ht
    nlinarith [sq_nonneg (t : Int)]
  · simp only [pellSquarePlusOne, Pell.Solution₁.y_mk]
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) ht
  · intro b hb
    simp only [pellSquarePlusOne, Pell.Solution₁.x_mk]
    let y : Int := |b.y|
    have hy : 0 < y := by
      dsimp [y]
      exact abs_pos.mpr (Pell.Solution₁.y_ne_zero_of_one_lt_x hb)
    have htInt : (0 : Int) < t := by exact_mod_cast ht
    have hySq : y ^ 2 = b.y ^ 2 := by
      dsimp [y]
      exact sq_abs b.y
    have heq :
        b.x ^ 2 - ((t : Int) ^ 2 + 1) * y ^ 2 = 1 := by
      rw [hySq]
      have hprop := b.prop
      simp only [squarePlusOneKernel] at hprop
      push_cast at hprop
      exact hprop
    exact squarePlusOne_minimal htInt hb hy heq

/-- In the selected residue classes, the real coordinate of the fundamental
solution is zero modulo nine. -/
theorem pellSquarePlusOne_x_mod_nine
    {t : Nat} (ht : t % 18 = 2 ∨ t % 18 = 16) :
    ((pellSquarePlusOne t).x : ZMod 9) = 0 := by
  simp only [pellSquarePlusOne, Pell.Solution₁.x_mk]
  push_cast
  rcases ht with ht | ht
  · have h18 : t ≡ 2 [MOD 18] := by
      simpa [Nat.ModEq] using ht
    have h9 : t ≡ 2 [MOD 9] :=
      h18.of_dvd (by decide : 9 ∣ 18)
    have htz : (t : ZMod 9) = 2 :=
      (ZMod.natCast_eq_natCast_iff t 2 9).mpr h9
    rw [htz]
    decide
  · have h18 : t ≡ 16 [MOD 18] := by
      simpa [Nat.ModEq] using ht
    have h9 : t ≡ 16 [MOD 9] :=
      h18.of_dvd (by decide : 9 ∣ 18)
    have htz : (t : ZMod 9) = 16 :=
      (ZMod.natCast_eq_natCast_iff t 16 9).mpr h9
    rw [htz]
    decide

/-- Every positive negative-Pell solution in the selected square-plus-one
family has exactly one factor of three in its opposite flank. -/
theorem three_exactly_dvd_lower_of_negativePellSquarePlusOne
    {t X W : Nat} (ht : t % 18 = 2 ∨ t % 18 = 16)
    (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = squarePlusOneKernel t * W ^ 2) :
    3 ∣ X ^ 2 - 1 ∧ ¬ 3 ^ 2 ∣ X ^ 2 - 1 := by
  have htTwo : 2 ≤ t := by
    rcases ht with h | h <;> omega
  have htPos : 0 < t := by omega
  have hK : 2 < squarePlusOneKernel t := by
    simp only [squarePlusOneKernel]
    nlinarith
  exact three_exactly_dvd_lower_of_negativePell_of_normOne_modNine
    hK (pellSquarePlusOne t) (pellSquarePlusOne_isFundamental htPos)
    (pellSquarePlusOne_x_mod_nine ht) hX hW hPell

/-- No canonical square-middle counterexample can have upper cube kernel
`t² + 1` in either selected residue class. -/
theorem no_pairPellCounterexample_upperKernel_squarePlusOne
    {t : Nat} (ht : t % 18 = 2 ∨ t % 18 = 16)
    (data : PairPellCounterexampleData)
    (hupper : data.upperKernel = squarePlusOneKernel t) :
    False := by
  have htPos : 0 < t := by
    rcases ht with h | h <;> omega
  exact no_pairPellCounterexample_upperKernel_of_normOne_modNine
    (pellSquarePlusOne t) (pellSquarePlusOne_isFundamental htPos)
    (pellSquarePlusOne_x_mod_nine ht) data hupper

/-- The square-plus-one family excludes the complete fixed upper-kernel
fibre `K = 1157`, obtained from `t = 34`. -/
theorem no_pairPellCounterexample_upperKernel_oneThousandOneHundredFiftySeven
    (data : PairPellCounterexampleData)
    (hupper : data.upperKernel = 1157) :
    False := by
  apply no_pairPellCounterexample_upperKernel_squarePlusOne
      (t := 34) (by decide) data
  simpa [squarePlusOneKernel] using hupper

end Erdos364
