import Erdos364.SquareMiddle.SourceNormalizer

namespace Erdos364

/-!
# Polynomial source for the `sm2LowerSquare` leaf

This module gives an exact source-equivalent one-parameter description of the
maintained `sm2LowerSquare` leaf.  It is a representation theorem, not a leaf
exclusion.
-/

/-- A square-middle source whose canonical normalized witness lies in the
literal `sm2LowerSquare` compiler leaf. -/
def Sm2LowerSquareSource (X : Nat) : Prop :=
  ∃ h : SquareMiddle X,
    SquareMiddleLeafPred .sm2LowerSquare (normalizeSquareMiddle h)

/-- An odd natural square is `1 mod 8`, so adding one gives the centre residue
required by the `sm2LowerSquare` leaf. -/
private theorem odd_square_add_one_mod_eight {y : Nat} (hy : Odd y) :
    (y ^ 2 + 1) % 8 = 2 := by
  have hy_two : y % 2 = 1 := Nat.odd_iff.mp hy
  have hy_lt : y % 8 < 8 := Nat.mod_lt y (by decide)
  have hy_mod_two : y % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd y (by decide : 2 ∣ 8)]
    exact hy_two
  have hy_cases :
      y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by
    omega
  rcases hy_cases with h | h | h | h <;>
    simp [Nat.add_mod, Nat.pow_mod, h]

/-- The `sm2LowerSquare` source is exactly the one-parameter powerful
polynomial pair obtained by writing the lower linear flank as a square. -/
theorem sm2LowerSquareSource_iff_exists_odd_powerful_polynomial_pair
    (X : Nat) :
    Sm2LowerSquareSource X ↔
      ∃ y : Nat,
        0 < y ∧
        Odd y ∧
        X = y ^ 2 + 1 ∧
        PowerfulPos (y ^ 2 + 2) ∧
        PowerfulPos (y ^ 4 + 2 * y ^ 2 + 2) := by
  constructor
  · rintro ⟨hsource, hleaf⟩
    let w := normalizeSquareMiddle hsource
    have hleaf' :
        X % 8 = 2 ∧ w.flanks.lowerKernel = 1 ∧
          w.flanks.upperKernel % 8 = 3 := by
      simpa only [SquareMiddleLeafPred, w] using hleaf
    have hlower :
        X - 1 = w.flanks.lowerSquare ^ 2 := by
      simpa [hleaf'.2.1] using w.lower_form.2.2.1
    have hcenter :
        X = w.flanks.lowerSquare ^ 2 + 1 := by
      omega
    have hlower_odd : Odd (X - 1) :=
      Nat.Even.sub_odd (by omega : 1 ≤ X) hsource.center_even odd_one
    have hsquare_odd : Odd (w.flanks.lowerSquare ^ 2) := by
      rwa [← hlower]
    have hy_odd : Odd w.flanks.lowerSquare :=
      (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp hsquare_odd
    have hfirst := hsource.flanks_powerful.2
    have hsecond := hsource.2.2
    refine
      ⟨w.flanks.lowerSquare, w.lower_form.1, hy_odd, hcenter, ?_, ?_⟩
    · simpa [hcenter, Nat.add_assoc] using hfirst
    · have hpoly :
          X ^ 2 + 1 =
            w.flanks.lowerSquare ^ 4 +
              2 * w.flanks.lowerSquare ^ 2 + 2 := by
        calc
          X ^ 2 + 1 =
              (w.flanks.lowerSquare ^ 2 + 1) ^ 2 + 1 :=
            congrArg (fun n : Nat => n ^ 2 + 1) hcenter
          _ = w.flanks.lowerSquare ^ 4 +
                2 * w.flanks.lowerSquare ^ 2 + 2 := by
            ring
      rwa [hpoly] at hsecond
  · rintro ⟨y, hy_pos, hy_odd, hcenter, hfirst, hsecond⟩
    subst X
    have hleft_value :
        (y ^ 2 + 1) ^ 2 - 1 = y ^ 2 * (y ^ 2 + 2) := by
      rw [tsub_eq_iff_eq_add_of_le
        (by nlinarith : 1 ≤ (y ^ 2 + 1) ^ 2)]
      ring
    have hright_value :
        (y ^ 2 + 1) ^ 2 + 1 =
          y ^ 4 + 2 * y ^ 2 + 2 := by
      ring
    have hsource : SquareMiddle (y ^ 2 + 1) := by
      refine ⟨by nlinarith, ?_, ?_⟩
      · rw [hleft_value]
        exact powerfulPos_mul (powerfulPos_square hy_pos) hfirst
      · rwa [hright_value]
    let w := normalizeSquareMiddle hsource
    have hcanonical_lower :
        SquareCubeNormalForm ((y ^ 2 + 1) - 1) y 1 := by
      apply squareCubeNormalForm_of_eq_sq_mul_cube
      · exact hy_pos
      · norm_num
      · simp
      · norm_num
    have hlower_pos : 0 < (y ^ 2 + 1) - 1 := by
      simpa using pow_pos hy_pos 2
    have hlower_kernel : w.flanks.lowerKernel = 1 :=
      squareCubeNormalForm_kernel_unique
        hlower_pos w.lower_form hcanonical_lower
    have hcenter_mod : (y ^ 2 + 1) % 8 = 2 :=
      odd_square_add_one_mod_eight hy_odd
    have hupper_kernel_mod : w.flanks.upperKernel % 8 = 3 := by
      rcases w.flanks.kernel_mod_eight_table w.source with
        hzero | htwo | hfour | hsix
      · omega
      · exact htwo.2.2
      · omega
      · omega
    refine ⟨hsource, ?_⟩
    simpa only [SquareMiddleLeafPred, w] using
      (show
        (y ^ 2 + 1) % 8 = 2 ∧ w.flanks.lowerKernel = 1 ∧
          w.flanks.upperKernel % 8 = 3 from
        ⟨hcenter_mod, hlower_kernel, hupper_kernel_mod⟩)

end Erdos364
