import Erdos364.Foundations.ConsecutiveKernelConstraints
import Erdos364.SquareMiddle.NormalForm
import Erdos364.SquareMiddle.SourceArithmetic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace Erdos364

/-!
# Right-flank residue constraints

This module records elementary local restrictions on a hypothetical powerful
right flank `X ^ 2 + 1`.  They are deliberately stated without assuming the
unproved universal right-flank exclusion.
-/

private theorem odd_mod_eight_cases {n : Nat} (hn : Odd n) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  have hmod : n % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)]
    exact hn2
  omega

private theorem odd_square_mod_eight {n : Nat} (hn : Odd n) :
    n ^ 2 % 8 = 1 := by
  rcases odd_mod_eight_cases hn with h | h | h | h <;>
    simp [Nat.pow_mod, h]

private theorem odd_cube_mod_eight {n : Nat} (hn : Odd n) :
    n ^ 3 % 8 = n % 8 := by
  rcases odd_mod_eight_cases hn with h | h | h | h <;>
    simp [Nat.pow_mod, h]

/-- In any square-cube normal form of an odd value, the squarefree cube
kernel has the same residue modulo eight as the represented value. -/
theorem SquareCubeNormalForm.kernel_mod_eight_of_odd_value
    {n a K : Nat} (hform : SquareCubeNormalForm n a K) (hn : Odd n) :
    K % 8 = n % 8 := by
  have hvalue : Odd (a ^ 2 * K ^ 3) := by
    rw [← hform.2.2.1]
    exact hn
  have haPow : Odd (a ^ 2) := (Nat.odd_mul.mp hvalue).1
  have hKPow : Odd (K ^ 3) := (Nat.odd_mul.mp hvalue).2
  have ha : Odd a :=
    (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp haPow
  have hK : Odd K :=
    (Nat.odd_pow_iff (by decide : 3 ≠ 0)).mp hKPow
  rw [hform.2.2.1, Nat.mul_mod, odd_square_mod_eight ha,
    odd_cube_mod_eight hK]
  omega

private theorem square_mod_eight_of_mod_four_eq_zero {X : Nat}
    (hX : X % 4 = 0) :
    X ^ 2 % 8 = 0 := by
  have hdecomp : X % 4 + 4 * (X / 4) = X := Nat.mod_add_div X 4
  rw [hX] at hdecomp
  rw [← hdecomp]
  rw [show (0 + 4 * (X / 4)) ^ 2 = 8 * (2 * (X / 4) ^ 2) by ring]
  simp

private theorem square_mod_eight_of_mod_four_eq_two {X : Nat}
    (hX : X % 4 = 2) :
    X ^ 2 % 8 = 4 := by
  have hdecomp : X % 4 + 4 * (X / 4) = X := Nat.mod_add_div X 4
  rw [hX] at hdecomp
  rw [← hdecomp]
  rw [show (2 + 4 * (X / 4)) ^ 2 =
      8 * (2 * (X / 4) ^ 2 + 2 * (X / 4)) + 4 by ring]
  simp

private theorem square_sub_one_mod_eight_of_square_mod_eight_zero {X : Nat}
    (hX : 1 < X) (hsquare : X ^ 2 % 8 = 0) :
    (X ^ 2 - 1) % 8 = 7 := by
  have hmod : X ^ 2 ≡ 8 [MOD 8] := by
    change X ^ 2 % 8 = 8 % 8
    simpa using hsquare
  have hsub : X ^ 2 - 1 ≡ 8 - 1 [MOD 8] :=
    Nat.ModEq.sub (by nlinarith : 1 ≤ X ^ 2) (by decide : 1 ≤ 8)
      hmod Nat.ModEq.rfl
  change (X ^ 2 - 1) % 8 = (8 - 1) % 8 at hsub
  simpa using hsub

private theorem square_sub_one_mod_eight_of_square_mod_eight_four {X : Nat}
    (hX : 1 < X) (hsquare : X ^ 2 % 8 = 4) :
    (X ^ 2 - 1) % 8 = 3 := by
  have hmod : X ^ 2 ≡ 4 [MOD 8] := by
    change X ^ 2 % 8 = 4 % 8
    simpa using hsquare
  have hsub : X ^ 2 - 1 ≡ 4 - 1 [MOD 8] :=
    Nat.ModEq.sub (by nlinarith : 1 ≤ X ^ 2) (by decide : 1 ≤ 4)
      hmod Nat.ModEq.rfl
  change (X ^ 2 - 1) % 8 = (4 - 1) % 8 at hsub
  simpa using hsub

/-- An even centre makes its right square shift odd. -/
theorem square_add_one_odd_of_even {X : Nat} (hEven : Even X) :
    Odd (X ^ 2 + 1) := by
  have hsquareEven : Even (X ^ 2) :=
    Nat.even_pow.mpr ⟨hEven, by decide⟩
  exact hsquareEven.add_odd odd_one

/-- Every prime divisor of `X² + 1` at an even centre is one modulo four.
The evenness hypothesis is essential: for odd `X`, the prime `2` divides the
right shift. -/
theorem prime_mod_four_eq_one_of_dvd_square_add_one
    {X q : Nat} (hEven : Even X) (hq : q.Prime)
    (hqDvd : q ∣ X ^ 2 + 1) :
    q % 4 = 1 := by
  have hqNeTwo : q ≠ 2 := by
    intro hqTwo
    subst q
    exact (square_add_one_odd_of_even hEven).not_two_dvd_nat hqDvd
  letI : Fact q.Prime := ⟨hq⟩
  have hzero : ((X ^ 2 + 1 : Nat) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (X ^ 2 + 1) q).2 hqDvd
  have hadd : (X : ZMod q) ^ 2 + 1 = 0 := by
    simpa using hzero
  have hsquare : (X : ZMod q) ^ 2 = -1 := by
    exact eq_neg_of_add_eq_zero_left hadd
  have hnotThree : q % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_one hsquare
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (hq.odd_of_ne_two hqNeTwo)) with
    hOne | hThree
  · exact hOne
  · exact (hnotThree hThree).elim

/-- In particular, every prime in the squarefree cube kernel of a powerful
right flank is one modulo four. -/
theorem SquareCubeNormalForm.prime_mod_four_eq_one_of_dvd_right_kernel
    {X V K q : Nat} (hEven : Even X)
    (hform : SquareCubeNormalForm (X ^ 2 + 1) V K)
    (hq : q.Prime) (hqDvd : q ∣ K) :
    q % 4 = 1 := by
  apply prime_mod_four_eq_one_of_dvd_square_add_one hEven hq
  exact dvd_trans hqDvd (squareCubeNormalForm_kernel_dvd_value hform)

/-- The upper kernel is `1 (mod 8)` on the `X = 0 (mod 4)` top branch. -/
theorem SquareCubeNormalForm.rightKernel_mod_eight_of_center_mod_four_eq_zero
    {X V K : Nat} (hEven : Even X)
    (hform : SquareCubeNormalForm (X ^ 2 + 1) V K)
    (hXmod : X % 4 = 0) :
    K % 8 = 1 := by
  have hkernel := hform.kernel_mod_eight_of_odd_value
    (square_add_one_odd_of_even hEven)
  have hsquare := square_mod_eight_of_mod_four_eq_zero hXmod
  calc
    K % 8 = (X ^ 2 + 1) % 8 := hkernel
    _ = 1 := by simp [Nat.add_mod, hsquare]

/-- The upper kernel is `5 (mod 8)` on the `X = 2 (mod 4)` top branch. -/
theorem SquareCubeNormalForm.rightKernel_mod_eight_of_center_mod_four_eq_two
    {X V K : Nat} (hEven : Even X)
    (hform : SquareCubeNormalForm (X ^ 2 + 1) V K)
    (hXmod : X % 4 = 2) :
    K % 8 = 5 := by
  have hkernel := hform.kernel_mod_eight_of_odd_value
    (square_add_one_odd_of_even hEven)
  have hsquare := square_mod_eight_of_mod_four_eq_two hXmod
  calc
    K % 8 = (X ^ 2 + 1) % 8 := hkernel
    _ = 5 := by simp [Nat.add_mod, hsquare]

/-- Exact lower/upper cube-kernel pairing modulo eight for the two canonical
even-centre top branches. -/
theorem squareMiddle_twoKernel_mod_eight_pairing
    {X U D V K : Nat} (hX : 1 < X) (hEven : Even X)
    (hLower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hUpper : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    (X % 4 = 0 → D % 8 = 7 ∧ K % 8 = 1) ∧
      (X % 4 = 2 → D % 8 = 3 ∧ K % 8 = 5) := by
  have hsquareEven : Even (X ^ 2) :=
    Nat.even_pow.mpr ⟨hEven, by decide⟩
  have hLowerOdd : Odd (X ^ 2 - 1) :=
    Nat.Even.sub_odd (by nlinarith : 1 ≤ X ^ 2) hsquareEven odd_one
  have hLowerKernel := hLower.kernel_mod_eight_of_odd_value hLowerOdd
  constructor
  · intro hmod
    have hsquare := square_mod_eight_of_mod_four_eq_zero hmod
    have hleft := square_sub_one_mod_eight_of_square_mod_eight_zero hX hsquare
    exact ⟨hLowerKernel.trans hleft,
      hUpper.rightKernel_mod_eight_of_center_mod_four_eq_zero hEven hmod⟩
  · intro hmod
    have hsquare := square_mod_eight_of_mod_four_eq_two hmod
    have hleft := square_sub_one_mod_eight_of_square_mod_eight_four hX hsquare
    exact ⟨hLowerKernel.trans hleft,
      hUpper.rightKernel_mod_eight_of_center_mod_four_eq_two hEven hmod⟩

end Erdos364
