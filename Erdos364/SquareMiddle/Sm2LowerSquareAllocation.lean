import Erdos364.Global.RootSplit
import Erdos364.SquareMiddle.RightFlankConsequences
import Erdos364.SquareMiddle.Sm2LowerSquarePolynomial

namespace Erdos364

/-!
# Canonical allocation for the `sm2LowerSquare` leaf

This module recompiles the exact odd-`y` polynomial source into the canonical
lower- and upper-kernel data already carried by `PairPellCounterexampleData`.
It also proves the immediate elementary structural shell.  No obstruction
certificate or leaf exclusion is used here.
-/

/-- The canonical source-typed allocation attached to an
`sm2LowerSquare` counterexample package.

Here `data.pell.D` is the cube kernel of `data.center ^ 2 - 1`, which is also
the cube kernel of the linear upper flank `y ^ 2 + 2` on this leaf.
`data.upperKernel` is the distinct cube kernel of
`y ^ 4 + 2 * y ^ 2 + 2 = data.center ^ 2 + 1`. -/
structure Sm2LowerSquareAllocation
    (data : PairPellCounterexampleData) where
  y : Nat
  linearUpperSquarePart : Nat
  y_pos : 0 < y
  y_odd : Odd y
  center_eq : data.center = y ^ 2 + 1
  linearUpperNormalForm :
    SquareCubeNormalForm
      (y ^ 2 + 2) linearUpperSquarePart data.pell.D
  upperPolynomialNormalForm :
    SquareCubeNormalForm
      (y ^ 4 + 2 * y ^ 2 + 2)
      data.upperSquarePart data.upperKernel
  lowerSquarePart_eq :
    data.lowerSquarePart = y * linearUpperSquarePart

namespace Sm2LowerSquareAllocation

/-- The lower square-neighbour is reconstructed from the allocated
polynomial value at the same centre. -/
theorem lower_value_eq {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.center ^ 2 - 1 =
      allocation.y ^ 2 * (allocation.y ^ 2 + 2) := by
  calc
    data.center ^ 2 - 1 =
        (allocation.y ^ 2 + 1) ^ 2 - 1 :=
      congrArg (fun n : Nat => n ^ 2 - 1) allocation.center_eq
    _ = allocation.y ^ 2 * (allocation.y ^ 2 + 2) := by
      rw [tsub_eq_iff_eq_add_of_le
        (by nlinarith :
          1 ≤ (allocation.y ^ 2 + 1) ^ 2)]
      ring

/-- The upper square-neighbour is the second allocated polynomial value. -/
theorem upper_value_eq {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.pell.shiftValue =
      allocation.y ^ 4 + 2 * allocation.y ^ 2 + 2 := by
  calc
    data.pell.shiftValue = data.center ^ 2 + 1 := rfl
    _ = (allocation.y ^ 2 + 1) ^ 2 + 1 :=
      congrArg (fun n : Nat => n ^ 2 + 1) allocation.center_eq
    _ = allocation.y ^ 4 + 2 * allocation.y ^ 2 + 2 := by
      ring

/-- An allocation reconstructs the exact maintained source leaf, not merely
the two polynomial identities. -/
theorem sm2LowerSquareSource {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Sm2LowerSquareSource data.center := by
  apply
    (sm2LowerSquareSource_iff_exists_odd_powerful_polynomial_pair
      data.center).2
  exact
    ⟨allocation.y, allocation.y_pos, allocation.y_odd,
      allocation.center_eq,
      powerfulPos_of_squareCubeNormalForm
        allocation.linearUpperNormalForm,
      powerfulPos_of_squareCubeNormalForm
        allocation.upperPolynomialNormalForm⟩

/-- The two source polynomial values are coprime. -/
theorem polynomials_coprime {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nat.Coprime
      (allocation.y ^ 2 + 2)
      (allocation.y ^ 4 + 2 * allocation.y ^ 2 + 2) := by
  have hy_two : allocation.y % 2 = 1 :=
    Nat.odd_iff.mp allocation.y_odd
  have hfirst_odd : Odd (allocation.y ^ 2 + 2) := by
    rw [Nat.odd_iff]
    simp [Nat.pow_mod, hy_two]
  have hrewrite :
      allocation.y ^ 4 + 2 * allocation.y ^ 2 + 2 =
        (allocation.y ^ 2 + 2) * allocation.y ^ 2 + 2 := by
    ring
  rw [hrewrite, Nat.coprime_mul_left_add_right]
  exact Nat.coprime_two_right.mpr hfirst_odd

/-- All support in the first polynomial value is coprime to all support in
the second polynomial value. -/
theorem polynomial_supports_coprime
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nat.Coprime
      (data.pell.D * allocation.linearUpperSquarePart)
      (data.upperKernel * data.upperSquarePart) := by
  have hvalues := allocation.polynomials_coprime
  apply hvalues.of_dvd
  · simpa [Nat.mul_comm] using
      allocation.linearUpperNormalForm.squareFactor_mul_kernel_dvd_value
  · simpa [Nat.mul_comm] using
      allocation.upperPolynomialNormalForm.squareFactor_mul_kernel_dvd_value

/-- The complete lower support, including the leaf square factor `y`, is
coprime to the complete upper support. -/
theorem source_supports_coprime
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nat.Coprime
      (data.pell.D *
        (allocation.y * allocation.linearUpperSquarePart))
      (data.upperKernel * data.upperSquarePart) := by
  simpa [allocation.lowerSquarePart_eq] using data.support_coprime

/-- In particular, the two canonical cube kernels are coprime. -/
theorem kernels_coprime {data : PairPellCounterexampleData}
    (_allocation : Sm2LowerSquareAllocation data) :
    Nat.Coprime data.pell.D data.upperKernel :=
  data.kernels_coprime

/-- The lower kernel already carries its maintained Pell-kernel certificate. -/
theorem lower_pellKernel {data : PairPellCounterexampleData}
    (_allocation : Sm2LowerSquareAllocation data) :
    PellKernel data.pell.D :=
  data.pell.kernel

/-- The upper polynomial kernel is also a genuine Pell kernel. -/
theorem upper_pellKernel {data : PairPellCounterexampleData}
    (_allocation : Sm2LowerSquareAllocation data) :
    PellKernel data.upperKernel :=
  ⟨data.upperKernel_one_lt,
    data.upperNormalForm.kernel_squarefree⟩

/-- The allocated centre retains the literal leaf residue. -/
theorem center_mod_eight {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.center % 8 = 2 := by
  rcases allocation.sm2LowerSquareSource with ⟨hsource, hleaf⟩
  simpa only [SquareMiddleLeafPred] using hleaf.1

end Sm2LowerSquareAllocation

/-- Construct the canonical allocation directly from the literal maintained
leaf predicate on a canonical counterexample package. -/
noncomputable def sm2LowerSquareAllocationOfLeaf
    (data : PairPellCounterexampleData)
    (hleaf :
      SquareMiddleLeafPred .sm2LowerSquare
        (normalizeSquareMiddle data.squareMiddle)) :
    Sm2LowerSquareAllocation data := by
  let w := normalizeSquareMiddle data.squareMiddle
  have hleaf' :
      data.center % 8 = 2 ∧
        w.flanks.lowerKernel = 1 ∧
          w.flanks.upperKernel % 8 = 3 := by
    simpa only [SquareMiddleLeafPred, w] using hleaf
  have hlower :
      data.center - 1 = w.flanks.lowerSquare ^ 2 := by
    simpa [hleaf'.2.1] using w.lower_form.2.2.1
  have hcenter :
      data.center = w.flanks.lowerSquare ^ 2 + 1 := by
    omega
  have hlower_odd : Odd (data.center - 1) :=
    Nat.Even.sub_odd
      (by omega : 1 ≤ data.center) data.center_even odd_one
  have hsquare_odd : Odd (w.flanks.lowerSquare ^ 2) := by
    rwa [← hlower]
  have hy_odd : Odd w.flanks.lowerSquare :=
    (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp hsquare_odd
  have hcombined :
      SquareCubeNormalForm
        (data.center ^ 2 - 1)
        (w.flanks.lowerSquare * w.flanks.upperSquare)
        w.flanks.upperKernel := by
    simpa [hleaf'.2.1] using
      w.flanks.product_normalForm data.squareMiddle
  have hcanonical :=
    squareCubeNormalForm_pair_unique
      data.squareMiddle.2.1.1 hcombined data.lowerNormalForm
  have hlowerPolynomial :
      SquareCubeNormalForm
        (w.flanks.lowerSquare ^ 2 + 2)
        w.flanks.upperSquare data.pell.D := by
    have hlinear :
        SquareCubeNormalForm
          (w.flanks.lowerSquare ^ 2 + 2)
          w.flanks.upperSquare w.flanks.upperKernel := by
      simpa [hcenter, Nat.add_assoc] using w.upper_form
    simpa [hcanonical.2] using hlinear
  have hupperValue :
      data.pell.shiftValue =
        w.flanks.lowerSquare ^ 4 +
          2 * w.flanks.lowerSquare ^ 2 + 2 := by
    calc
      data.pell.shiftValue = data.center ^ 2 + 1 := rfl
      _ = (w.flanks.lowerSquare ^ 2 + 1) ^ 2 + 1 :=
        congrArg (fun X : Nat => X ^ 2 + 1) hcenter
      _ = w.flanks.lowerSquare ^ 4 +
          2 * w.flanks.lowerSquare ^ 2 + 2 := by
        ring
  have hupperPolynomial :
      SquareCubeNormalForm
        (w.flanks.lowerSquare ^ 4 +
          2 * w.flanks.lowerSquare ^ 2 + 2)
        data.upperSquarePart data.upperKernel := by
    rw [← hupperValue]
    exact data.upperNormalForm
  exact
    { y := w.flanks.lowerSquare
      linearUpperSquarePart := w.flanks.upperSquare
      y_pos := w.lower_form.1
      y_odd := hy_odd
      center_eq := hcenter
      linearUpperNormalForm := hlowerPolynomial
      upperPolynomialNormalForm := hupperPolynomial
      lowerSquarePart_eq := hcanonical.1.symm }

/-- The Pell kernel is exactly the normalized linear upper-flank kernel on
the `sm2LowerSquare` leaf.  The field called `upperKernel` in
`PairPellCounterexampleData` is not this kernel. -/
theorem pairPellCounterexampleDataOfSquareMiddle_pellD_eq_linearUpperKernel
    {X : Nat} (hsource : SquareMiddle X)
    (hleaf :
      SquareMiddleLeafPred .sm2LowerSquare
        (normalizeSquareMiddle hsource)) :
    (pairPellCounterexampleDataOfSquareMiddle hsource).pell.D =
      (normalizeSquareMiddle hsource).flanks.upperKernel := by
  let w := normalizeSquareMiddle hsource
  let data := pairPellCounterexampleDataOfSquareMiddle hsource
  have hleaf' : w.flanks.lowerKernel = 1 := by
    simpa only [SquareMiddleLeafPred, w] using hleaf.2.1
  have hdata_represents : data.pell.Represents X :=
    pairPellCounterexampleDataOfSquareMiddle_represents hsource
  have hpell : data.pell = w.pell :=
    pairPellIndexData_unique
      hdata_represents w.pell_represents_source
  have hpellD : data.pell.D = w.pell.D :=
    congrArg (fun pell : PairPellIndexData => pell.D) hpell
  have hwUpperD : w.flanks.upperKernel = w.pell.D := by
    simpa [hleaf'] using w.flank_kernel_product
  exact hpellD.trans hwUpperD.symm

/-- At a fixed canonical package, the literal leaf predicate is equivalent to
the existence of its typed allocation. -/
theorem PairPellCounterexampleData.sm2LowerSquare_iff_nonempty_allocation
    (data : PairPellCounterexampleData) :
    SquareMiddleLeafPred .sm2LowerSquare
        (normalizeSquareMiddle data.squareMiddle) ↔
      Nonempty (Sm2LowerSquareAllocation data) := by
  constructor
  · intro hleaf
    exact ⟨sm2LowerSquareAllocationOfLeaf data hleaf⟩
  · rintro ⟨allocation⟩
    rcases allocation.sm2LowerSquareSource with
      ⟨hsource, hleaf⟩
    have hproof : hsource = data.squareMiddle :=
      Subsingleton.elim _ _
    simpa [hproof] using hleaf

/-- Exact source-to-allocation compiler bridge.  The shared centre is retained
by `data.pell.Represents X`; no raw polynomial or two-kernel converse is used. -/
theorem sm2LowerSquareSource_iff_exists_canonical_allocation
    (X : Nat) :
    Sm2LowerSquareSource X ↔
      ∃ data : PairPellCounterexampleData,
        data.pell.Represents X ∧
          Nonempty (Sm2LowerSquareAllocation data) := by
  constructor
  · rintro ⟨hsource, hleaf⟩
    let data := pairPellCounterexampleDataOfSquareMiddle hsource
    have hrep : data.pell.Represents X :=
      pairPellCounterexampleDataOfSquareMiddle_represents hsource
    have hXcenter : X = data.center := hrep.2
    have hcenterSource : Sm2LowerSquareSource data.center := by
      rw [← hXcenter]
      exact ⟨hsource, hleaf⟩
    rcases hcenterSource with ⟨hsource', hleaf'⟩
    have hproof : hsource' = data.squareMiddle :=
      Subsingleton.elim _ _
    have hleafData :
        SquareMiddleLeafPred .sm2LowerSquare
          (normalizeSquareMiddle data.squareMiddle) := by
      simpa [hproof] using hleaf'
    exact
      ⟨data, hrep,
        (data.sm2LowerSquare_iff_nonempty_allocation).mp hleafData⟩
  · rintro ⟨data, hrep, ⟨allocation⟩⟩
    rw [hrep.2]
    exact allocation.sm2LowerSquareSource

private theorem squarePlusOneSquare_add_one_mod_three
    (a : ZMod 3) :
    (a ^ 2 + 1) ^ 2 + 1 = 2 := by
  fin_cases a <;> decide

private theorem kernel_eq_two_mod_three_of_cube_times_square_eq_two
    (K V : ZMod 3) (h : V ^ 2 * K ^ 3 = 2) :
    K = 2 := by
  have hVcube : V ^ 3 = V := ZMod.pow_card V
  have hfactor : V * (V ^ 2 - 1) = 0 := by
    calc
      V * (V ^ 2 - 1) = V ^ 3 - V := by ring
      _ = 0 := sub_eq_zero.mpr hVcube
  rcases mul_eq_zero.mp hfactor with hVzero | hVsquare
  · rw [hVzero] at h
    have hzero : (0 : ZMod 3) = 2 := by simpa using h
    exact ((by decide : (0 : ZMod 3) ≠ 2) hzero).elim
  · have hVone : V ^ 2 = 1 := sub_eq_zero.mp hVsquare
    rw [hVone, one_mul, ZMod.pow_card K] at h
    exact h

/-- Exact kernel residue shell:
`D = 3 mod 8` and the distinct upper polynomial kernel `K = 5 mod 24`. -/
theorem Sm2LowerSquareAllocation.kernel_residues
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.pell.D % 8 = 3 ∧ data.upperKernel % 24 = 5 := by
  have hcenterEight : data.center % 8 = 2 :=
    allocation.center_mod_eight
  have hcenterFour : data.center % 4 = 2 := by
    have hmod :=
      Nat.mod_mod_of_dvd data.center (by decide : 4 ∣ 8)
    rw [hcenterEight] at hmod
    simpa using hmod.symm
  have hpair := data.kernel_mod_eight_pairing.2 hcenterFour
  have hupperCast :=
    congrArg (fun n : Nat => (n : ZMod 3))
      allocation.upperPolynomialNormalForm.2.2.1
  push_cast at hupperCast
  have hleft :
      ((allocation.y : ZMod 3) ^ 4 +
        2 * (allocation.y : ZMod 3) ^ 2 + 2) = 2 := by
    convert squarePlusOneSquare_add_one_mod_three
      (allocation.y : ZMod 3) using 1
    all_goals ring
  have hright :
      (data.upperSquarePart : ZMod 3) ^ 2 *
          (data.upperKernel : ZMod 3) ^ 3 =
        2 := by
    exact hupperCast.symm.trans hleft
  have hupperCastThree :
      (data.upperKernel : ZMod 3) = 2 :=
    kernel_eq_two_mod_three_of_cube_times_square_eq_two
      (data.upperKernel : ZMod 3)
      (data.upperSquarePart : ZMod 3) hright
  have hupperModThree : data.upperKernel % 3 = 2 :=
    (ZMod.natCast_eq_natCast_iff'
      data.upperKernel 2 3).mp hupperCastThree
  have hmodTwentyFourLt : data.upperKernel % 24 < 24 :=
    Nat.mod_lt _ (by decide)
  have hmodTwentyFourModEight :
      data.upperKernel % 24 % 8 = 5 := by
    rw [Nat.mod_mod_of_dvd data.upperKernel
      (by decide : 8 ∣ 24)]
    exact hpair.2
  have hmodTwentyFourModThree :
      data.upperKernel % 24 % 3 = 2 := by
    rw [Nat.mod_mod_of_dvd data.upperKernel
      (by decide : 3 ∣ 24)]
    exact hupperModThree
  exact ⟨hpair.1, by omega⟩

private theorem square_mod_nine_ne_eight (X : Nat) :
    X ^ 2 % 9 ≠ 8 := by
  intro hbad
  have hlt : X % 9 < 9 := Nat.mod_lt X (by decide)
  have hcases :
      X % 9 = 0 ∨ X % 9 = 1 ∨ X % 9 = 2 ∨
      X % 9 = 3 ∨ X % 9 = 4 ∨ X % 9 = 5 ∨
      X % 9 = 6 ∨ X % 9 = 7 ∨ X % 9 = 8 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h | h <;>
    simp [Nat.pow_mod, h] at hbad

private theorem three_not_dvd_square_add_one (y : Nat) :
    ¬ 3 ∣ y ^ 2 + 1 := by
  intro hdvd
  have hzero : (y ^ 2 + 1) % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  have hlt : y % 3 < 3 := Nat.mod_lt y (by decide)
  have hcases : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
    omega
  rcases hcases with h | h | h <;>
    simp [Nat.add_mod, Nat.pow_mod, h] at hzero

/-- The associated powerful-triple left index lies in the exact common
hierarchy class `27 mod 36`. -/
theorem Sm2LowerSquareAllocation.start_mod_thirtySix
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    (data.center ^ 2 - 1) % 36 = 27 := by
  have htriple := data.squareMiddle.toPowerfulTripleAt
  rcases htriple.start_mod_thirtySix with
    hseven | htwentySeven | hthirtyFive
  · exfalso
    have hnine :
        (data.center ^ 2 - 1) % 9 = 7 := by
      calc
        (data.center ^ 2 - 1) % 9 =
            ((data.center ^ 2 - 1) % 36) % 9 :=
          (Nat.mod_mod_of_dvd
            (data.center ^ 2 - 1) (by decide : 9 ∣ 36)).symm
        _ = 7 := by simp [hseven]
    have hrestore := square_sub_one_add_one data.center_one_lt
    have hsquareNine : data.center ^ 2 % 9 = 8 := by
      omega
    exact square_mod_nine_ne_eight data.center hsquareNine
  · exact htwentySeven
  · exfalso
    have hnine :
        (data.center ^ 2 - 1) % 9 = 8 := by
      calc
        (data.center ^ 2 - 1) % 9 =
            ((data.center ^ 2 - 1) % 36) % 9 :=
          (Nat.mod_mod_of_dvd
            (data.center ^ 2 - 1) (by decide : 9 ∣ 36)).symm
        _ = 8 := by simp [hthirtyFive]
    have hrestore := square_sub_one_add_one data.center_one_lt
    have hsquareNine : data.center ^ 2 % 9 = 0 := by
      omega
    have hsquareThree : data.center ^ 2 % 3 = 0 := by
      calc
        data.center ^ 2 % 3 =
            (data.center ^ 2 % 9) % 3 :=
          (Nat.mod_mod_of_dvd
            (data.center ^ 2) (by decide : 3 ∣ 9)).symm
        _ = 0 := by simp [hsquareNine]
    have hthreeSquare : 3 ∣ data.center ^ 2 :=
      Nat.dvd_of_mod_eq_zero hsquareThree
    have hthreeCenter : 3 ∣ data.center :=
      Nat.prime_three.dvd_of_dvd_pow hthreeSquare
    have hthreePoly : 3 ∣ allocation.y ^ 2 + 1 := by
      simpa [allocation.center_eq] using hthreeCenter
    exact three_not_dvd_square_add_one allocation.y hthreePoly

/-- The square middle itself is therefore `28 mod 36`. -/
theorem Sm2LowerSquareAllocation.middle_mod_thirtySix
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.center ^ 2 % 36 = 28 := by
  have hstart := allocation.start_mod_thirtySix
  have hrestore := square_sub_one_add_one data.center_one_lt
  omega

private theorem square_sub_one_mod_thirtyTwo
    {X : Nat} (hX : 1 < X) (hmod : X % 8 = 2) :
    (X ^ 2 - 1) % 32 = 3 := by
  have hlt : X % 32 < 32 := Nat.mod_lt X (by decide)
  have hmodEight : X % 32 % 8 = 2 := by
    rw [Nat.mod_mod_of_dvd X (by decide : 8 ∣ 32)]
    exact hmod
  have hcases :
      X % 32 = 2 ∨ X % 32 = 10 ∨
        X % 32 = 18 ∨ X % 32 = 26 := by
    omega
  have hsquare : X ^ 2 % 32 = 4 := by
    rcases hcases with h | h | h | h <;>
      simp [Nat.pow_mod, h]
  have hrestore := square_sub_one_add_one hX
  omega

/-- Leaf-specific sharpening of the common modulo-36 placement. -/
theorem Sm2LowerSquareAllocation.mod_twoHundredEightyEight
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    (data.center ^ 2 - 1) % 288 = 99 ∧
      data.center ^ 2 % 288 = 100 := by
  have hthirtySix := allocation.start_mod_thirtySix
  have hthirtyTwo :=
    square_sub_one_mod_thirtyTwo
      data.center_one_lt allocation.center_mod_eight
  have hlt :
      (data.center ^ 2 - 1) % 288 < 288 :=
    Nat.mod_lt _ (by decide)
  have hmodThirtySix :
      (data.center ^ 2 - 1) % 288 % 36 = 27 := by
    rw [Nat.mod_mod_of_dvd
      (data.center ^ 2 - 1) (by decide : 36 ∣ 288)]
    exact hthirtySix
  have hmodThirtyTwo :
      (data.center ^ 2 - 1) % 288 % 32 = 3 := by
    rw [Nat.mod_mod_of_dvd
      (data.center ^ 2 - 1) (by decide : 32 ∣ 288)]
    exact hthirtyTwo
  have hstart : (data.center ^ 2 - 1) % 288 = 99 := by
    omega
  have hrestore := square_sub_one_add_one data.center_one_lt
  have hmiddle : data.center ^ 2 % 288 = 100 := by
    omega
  exact ⟨hstart, hmiddle⟩

private theorem cube_mod_eight_ne_four (c : Nat) :
    c ^ 3 % 8 ≠ 4 := by
  intro hbad
  have hlt : c % 8 < 8 := Nat.mod_lt c (by decide)
  have hcases :
      c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨
      c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h <;>
    simp [Nat.pow_mod, h] at hbad

/-- The retained powerful-triple candidate lies in the noncube root child. -/
theorem Sm2LowerSquareAllocation.candidate_and_noncube
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nonempty
        (PowerfulTripleCandidateAt (data.center ^ 2 - 1)) ∧
      ¬ CubeMiddleAt (data.center ^ 2 - 1) := by
  constructor
  · exact data.squareMiddle.toPowerfulTripleAt.exists_candidate
  · rintro ⟨c, hc⟩
    have hmiddle :
        data.center ^ 2 = c ^ 3 :=
      (square_sub_one_add_one data.center_one_lt).symm.trans hc
    have hsquareMod : data.center ^ 2 % 8 = 4 := by
      simp [Nat.pow_mod, allocation.center_mod_eight]
    have hcubeMod : c ^ 3 % 8 = 4 := by
      rw [← hmiddle]
      exact hsquareMod
    exact cube_mod_eight_ne_four c hcubeMod

/-- Aggregate L2-L3 structural shell for downstream obstruction mechanisms. -/
theorem Sm2LowerSquareAllocation.structural_shell
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nat.Coprime
        (allocation.y ^ 2 + 2)
        (allocation.y ^ 4 + 2 * allocation.y ^ 2 + 2) ∧
      Nat.Coprime
        (data.pell.D * allocation.linearUpperSquarePart)
        (data.upperKernel * data.upperSquarePart) ∧
      Nat.Coprime data.pell.D data.upperKernel ∧
      PellKernel data.pell.D ∧
      PellKernel data.upperKernel ∧
      data.pell.D % 8 = 3 ∧
      data.upperKernel % 24 = 5 ∧
      PowerfulTripleAt (data.center ^ 2 - 1) ∧
      (data.center ^ 2 - 1) % 36 = 27 ∧
      data.center ^ 2 % 36 = 28 ∧
      (data.center ^ 2 - 1) % 288 = 99 ∧
      data.center ^ 2 % 288 = 100 ∧
      Nonempty
        (PowerfulTripleCandidateAt (data.center ^ 2 - 1)) ∧
      ¬ CubeMiddleAt (data.center ^ 2 - 1) := by
  have hresidues := allocation.kernel_residues
  have hmod288 := allocation.mod_twoHundredEightyEight
  have hroot := allocation.candidate_and_noncube
  exact
    ⟨allocation.polynomials_coprime,
      allocation.polynomial_supports_coprime,
      allocation.kernels_coprime,
      allocation.lower_pellKernel,
      allocation.upper_pellKernel,
      hresidues.1,
      hresidues.2,
      data.squareMiddle.toPowerfulTripleAt,
      allocation.start_mod_thirtySix,
      allocation.middle_mod_thirtySix,
      hmod288.1,
      hmod288.2,
      hroot.1,
      hroot.2⟩

end Erdos364
