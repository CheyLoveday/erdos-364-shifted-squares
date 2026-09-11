import Erdos364.CubeMiddle.PowerfulFactorTransport
import Erdos364.Foundations.ConsecutiveConstraints
import Erdos364.SquareMiddle.NormalForm
import Erdos364.SquareMiddle.Source

namespace Erdos364

/-- Difference-of-squares factorization with the natural-subtraction boundary
made explicit. -/
theorem square_sub_one_eq_flank_mul {X : Nat} (hX : 0 < X) :
    X ^ 2 - 1 = (X - 1) * (X + 1) := by
  let Y := X - 1
  have hXY : X = Y + 1 := by
    dsimp [Y]
    omega
  calc
    X ^ 2 - 1 = (Y + 1) ^ 2 - 1 := by rw [hXY]
    _ = Y * (Y + 2) := by
      rw [tsub_eq_iff_eq_add_of_le (by nlinarith : 1 ≤ (Y + 1) ^ 2)]
      ring
    _ = (X - 1) * (X + 1) := by
      rw [hXY]
      simp [Y]

/-- The source conditions force an even square root. -/
theorem squareMiddle_even {X : Nat} (h : SquareMiddle X) :
    Even X := by
  have hmiddle := h.toPowerfulTripleAt.middle_mod_four_eq_zero
  rw [square_sub_one_add_one h.1] at hmiddle
  have hfour_dvd : 4 ∣ X ^ 2 := Nat.dvd_of_mod_eq_zero hmiddle
  have htwo_dvd_square : 2 ∣ X ^ 2 :=
    dvd_trans (by norm_num : 2 ∣ 4) hfour_dvd
  have hsquare_even : Even (X ^ 2) := even_iff_two_dvd.mpr htwo_dvd_square
  exact (Nat.even_pow.mp hsquare_even).1

/-- Method-form alias for source-facing proofs. -/
theorem SquareMiddle.center_even {X : Nat} (h : SquareMiddle X) :
    Even X :=
  squareMiddle_even h

/-- The two positive flanks around an even center are coprime. Positivity is
kept explicit because it rules out natural-subtraction boundary cases. -/
theorem squareMiddle_flanks_coprime_of_even {X : Nat}
    (hX : 1 < X) (hEven : Even X) :
    Nat.Coprime (X - 1) (X + 1) := by
  have htwo_not_dvd : ¬ 2 ∣ X - 1 := by
    rcases hEven with ⟨k, hk⟩
    rintro ⟨j, hj⟩
    omega
  have hcop_two : Nat.Coprime (X - 1) 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr htwo_not_dvd).symm
  have hcop_add : Nat.Coprime (X - 1) (2 + (X - 1)) :=
    Nat.coprime_add_self_right.mpr hcop_two
  have hright : 2 + (X - 1) = X + 1 := by omega
  rw [hright] at hcop_add
  exact hcop_add

/-- Source-specialized coprimality of the two flanks. -/
theorem SquareMiddle.flanks_coprime {X : Nat} (h : SquareMiddle X) :
    Nat.Coprime (X - 1) (X + 1) :=
  squareMiddle_flanks_coprime_of_even h.1 h.center_even

/-- For an even nontrivial center, powerfulness of `X² - 1` is equivalent
to powerfulness of the two coprime flanks separately. The evenness hypothesis
is essential. -/
theorem powerfulPos_square_sub_one_iff_flanks {X : Nat}
    (hX : 1 < X) (hEven : Even X) :
    PowerfulPos (X ^ 2 - 1) ↔
      PowerfulPos (X - 1) ∧ PowerfulPos (X + 1) := by
  rw [square_sub_one_eq_flank_mul (by omega)]
  constructor
  · exact powerfulPos_factors_of_coprime_mul
      (squareMiddle_flanks_coprime_of_even hX hEven)
  · rintro ⟨hminus, hplus⟩
    exact powerfulPos_mul hminus hplus

/-- Both source flanks are therefore positive powerful naturals. -/
theorem SquareMiddle.flanks_powerful {X : Nat} (h : SquareMiddle X) :
    PowerfulPos (X - 1) ∧ PowerfulPos (X + 1) :=
  (powerfulPos_square_sub_one_iff_flanks h.1 h.center_even).mp h.2.1

/-- Regression witness showing why the even-center hypothesis cannot be
dropped from the flank equivalence: `3² - 1 = 8` is powerful but `3 - 1 = 2`
is not. -/
theorem odd_center_flank_split_counterexample :
    PowerfulPos (3 ^ 2 - 1) ∧ ¬ PowerfulPos (3 - 1) := by
  constructor
  · simpa using powerfulPos_eight
  · simpa using not_powerfulPos_two

/-- The canonical cube kernel of `X² - 1` is odd when the center is even. -/
theorem SquareCubeNormalForm.kernel_odd_of_even_center
    {X a D : Nat} (hX : 1 < X) (hEven : Even X)
    (hform : SquareCubeNormalForm (X ^ 2 - 1) a D) :
    Odd D := by
  have hsquare_even : Even (X ^ 2) :=
    Nat.even_pow.mpr ⟨hEven, by decide⟩
  have hleft_odd : Odd (X ^ 2 - 1) :=
    Nat.Even.sub_odd (by nlinarith : 1 ≤ X ^ 2) hsquare_even odd_one
  have hD_dvd_cube : D ∣ D ^ 3 := dvd_pow_self D (by decide)
  have hD_dvd_left : D ∣ X ^ 2 - 1 := by
    rw [hform.2.2.1]
    exact dvd_mul_of_dvd_right hD_dvd_cube (a ^ 2)
  rw [← Nat.not_even_iff_odd]
  intro hD_even
  exact hleft_odd.not_two_dvd_nat
    (dvd_trans (even_iff_two_dvd.mp hD_even) hD_dvd_left)

/-- Source-facing oddness of the canonical lower kernel. -/
theorem SquareMiddle.lowerKernel_odd {X a D : Nat}
    (h : SquareMiddle X)
    (hform : SquareCubeNormalForm (X ^ 2 - 1) a D) :
    Odd D :=
  hform.kernel_odd_of_even_center h.1 h.center_even

/-- The squarefree cube kernel cannot be `1`: otherwise two positive squares
would differ by one. -/
theorem squareCubeNormalForm_kernel_ne_one_of_square_sub_one
    {X a D : Nat} (hX : 1 < X)
    (hform : SquareCubeNormalForm (X ^ 2 - 1) a D) :
    D ≠ 1 := by
  intro hD
  subst D
  have hvalue : X ^ 2 - 1 = a ^ 2 := by
    simpa using hform.2.2.1
  have heq : a ^ 2 + 1 = X ^ 2 := by
    rw [← hvalue]
    exact square_sub_one_add_one hX
  have ha_lt_X : a < X := by
    apply (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).lt_iff_lt.mp
    omega
  have hsucc_le : a + 1 ≤ X := by omega
  have hsquare_le : (a + 1) ^ 2 ≤ X ^ 2 :=
    Nat.pow_le_pow_left hsucc_le 2
  have ha_pos := hform.1
  nlinarith

/-- Source-facing lower-kernel exclusion. -/
theorem SquareMiddle.lowerKernel_ne_one {X a D : Nat}
    (h : SquareMiddle X)
    (hform : SquareCubeNormalForm (X ^ 2 - 1) a D) :
    D ≠ 1 :=
  squareCubeNormalForm_kernel_ne_one_of_square_sub_one h.1 hform

/-- Every source lower kernel is therefore strictly larger than one. -/
theorem SquareMiddle.lowerKernel_one_lt {X a D : Nat}
    (h : SquareMiddle X)
    (hform : SquareCubeNormalForm (X ^ 2 - 1) a D) :
    1 < D := by
  have hD_pos := hform.2.1
  have hD_ne := h.lowerKernel_ne_one hform
  omega

end Erdos364
