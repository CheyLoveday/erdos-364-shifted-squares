import Erdos364.SquareMiddle.RightFlankNegativePellSign
import Erdos364.SquareMiddle.RightFlankNormOneControl
import Erdos364.SquareMiddle.RightFlankNormOneMod1089
import Erdos364.SquareMiddle.RightFlankNormOneModNine
import Erdos364.SquareMiddle.RightFlankNormOneModOneFortySeven
import Erdos364.SquareMiddle.RightFlankNormOneModSeventyFive
import Erdos364.SquareMiddle.Sm2LowerSquareLowerFundamental
import Erdos364.SquareMiddle.Sm2LowerSquareNormOnePrimeObstruction
import Erdos364.SquareMiddle.Sm2LowerSquareUpperKernelOneHundredOne

namespace Erdos364

/-!
# Exact source-typed residual for the `sm2LowerSquare` leaf

This module collects only consequences of the complete maintained allocation
and individually proved obstruction mechanisms.  The residual retains the
same canonical source package and centre.  It is therefore an exact
recompilation of the leaf after the current certificate filters, not an
assertion that the remaining domain is empty.
-/

/-- The exact source-typed residual left after all currently integrated
`sm2LowerSquare` certificate mechanisms. -/
structure Sm2LowerSquareResidual
    (data : PairPellCounterexampleData) where
  allocation : Sm2LowerSquareAllocation data
  upperFundamentalSign :
    (((fundamentalPell data.upperKernel
        allocation.upper_pellKernel).x :
      ZMod data.upperKernel) = -1)
  upperFundamentalX_ne_zero_modNine :
    ((fundamentalPell data.upperKernel
        allocation.upper_pellKernel).x : ZMod 9) ≠ 0
  upperFundamentalX_ne_sixtyThree_modSeventyFive :
    ((fundamentalPell data.upperKernel
        allocation.upper_pellKernel).x : ZMod 75) ≠ 63
  upperFundamentalX_ne_twentyFour_modOneFortySeven :
    ((fundamentalPell data.upperKernel
        allocation.upper_pellKernel).x : ZMod 147) ≠ 24
  upperFundamentalX_ne_eightHundredNinetyFour_mod1089 :
    ((fundamentalPell data.upperKernel
        allocation.upper_pellKernel).x : ZMod 1089) ≠ 894
  upperFundamentalX_ne_oneHundredNinetyFive_mod1089 :
    ((fundamentalPell data.upperKernel
        allocation.upper_pellKernel).x : ZMod 1089) ≠ 195
  upperKernel_ne_oneHundredOne :
    data.upperKernel ≠ 101
  upperKernel_ne_oneHundredNinetySeven :
    data.upperKernel ≠ 197
  upperKernel_ne_normOneControl :
    ∀ h c : Nat, 0 < h → 3 ≤ c →
      data.upperKernel ≠ normOneControlKernel h c
  upperIdentityPrimeAvoidance :
    ∀ q : Nat, q.Prime → q % 4 = 3 →
      ((fundamentalPell data.upperKernel
          allocation.upper_pellKernel).x : ZMod q) = 1 →
      ((fundamentalPell data.upperKernel
          allocation.upper_pellKernel).y : ZMod q) = 0 →
      False
  lowerFundamentalNormTwo :
    ∃ r s : Nat,
      0 < r ∧
        0 < s ∧
          fundamentalX data.pell.D data.pell.kernel = r ^ 2 + 1 ∧
            r ^ 2 + 2 = data.pell.D * s ^ 2 ∧
              fundamentalY data.pell.D data.pell.kernel = r * s

namespace Sm2LowerSquareAllocation

/-- Every complete leaf allocation canonically enters the exact residual.
Each avoidance field is the contrapositive of one separately maintained
obstruction theorem. -/
noncomputable def toResidual
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Sm2LowerSquareResidual data := by
  let hK : PellKernel data.upperKernel :=
    allocation.upper_pellKernel
  let e : Pell.Solution₁ (data.upperKernel : Int) :=
    fundamentalPell data.upperKernel hK
  have hfund : Pell.IsFundamental e :=
    fundamentalPell_isFundamental data.upperKernel hK
  have hKTwentyFour : data.upperKernel % 24 = 5 :=
    allocation.kernel_residues.2
  have hKFour : data.upperKernel % 4 = 1 := by
    have hmod :=
      Nat.mod_mod_of_dvd data.upperKernel
        (by decide : 4 ∣ 24)
    rw [hKTwentyFour] at hmod
    simpa using hmod.symm
  have hKTwo : 2 < data.upperKernel := by
    have hlt := Nat.mod_lt data.upperKernel (by decide : 0 < 24)
    omega
  have hsol : PositiveNegativePellSoluble data.upperKernel := by
    have hnegative := data.upper_negativePell
    exact
      ⟨data.center, data.upperKernel * data.upperSquarePart,
        Nat.zero_lt_of_lt data.center_one_lt, hnegative.W_pos,
        hnegative.equation.symm⟩
  have hsign :
      (e.x : ZMod data.upperKernel) = -1 := by
    exact
      (positiveNegativePellSoluble_iff_fundamentalPell_x_eq_negOne
        data.upperKernel hK hKFour).mp hsol
  refine
    { allocation := allocation
      upperFundamentalSign := hsign
      upperFundamentalX_ne_zero_modNine := ?_
      upperFundamentalX_ne_sixtyThree_modSeventyFive := ?_
      upperFundamentalX_ne_twentyFour_modOneFortySeven := ?_
      upperFundamentalX_ne_eightHundredNinetyFour_mod1089 := ?_
      upperFundamentalX_ne_oneHundredNinetyFive_mod1089 := ?_
      upperKernel_ne_oneHundredOne :=
        allocation.upperKernel_ne_oneHundredOne
      upperKernel_ne_oneHundredNinetySeven :=
        allocation.upperKernel_ne_oneHundredNinetySeven
      upperKernel_ne_normOneControl := ?_
      upperIdentityPrimeAvoidance := ?_
      lowerFundamentalNormTwo :=
        allocation.exists_lower_fundamental_normTwo }
  · intro hzero
    exact
      no_pairPellCounterexample_upperKernel_of_normOne_modNine
        e hfund hzero data rfl
  · intro hsixtyThree
    exact
      no_pairPellCounterexample_upperKernel_of_normOne_modSeventyFive
        e hfund hsixtyThree data rfl
  · intro htwentyFour
    exact
      no_pairPellCounterexample_upperKernel_of_normOne_modOneFortySeven
        e hfund htwentyFour data rfl
  · intro heightHundredNinetyFour
    exact
      no_pairPellCounterexample_upperKernel_of_normOne_mod1089
        e hfund heightHundredNinetyFour data rfl
  · intro honeHundredNinetyFive
    exact
      no_pairPellCounterexample_upperKernel_of_normOne_mod1089_x_eq_195
        e hfund honeHundredNinetyFive data rfl
  · intro h c hh hc hupper
    exact
      no_pairPellCounterexample_upperKernel_normOneControlFamily
        hh hc data hupper
  · intro q hq hqMod hx hy
    exact
      (allocation.upperKernel_ne_of_normOne_identity_mod_prime
        hKTwo hq hqMod e hfund hx hy) rfl

end Sm2LowerSquareAllocation

/-- Exact compiler boundary after all currently integrated certificate
filters.  The reverse direction is immediate because the residual retains the
complete canonical allocation and represented centre. -/
theorem sm2LowerSquareSource_iff_exists_residual
    (X : Nat) :
    Sm2LowerSquareSource X ↔
      ∃ data : PairPellCounterexampleData,
        data.pell.Represents X ∧
          Nonempty (Sm2LowerSquareResidual data) := by
  constructor
  · intro hsource
    obtain ⟨data, hrep, ⟨allocation⟩⟩ :=
      (sm2LowerSquareSource_iff_exists_canonical_allocation X).mp
        hsource
    exact ⟨data, hrep, ⟨allocation.toResidual⟩⟩
  · rintro ⟨data, hrep, ⟨residual⟩⟩
    apply
      (sm2LowerSquareSource_iff_exists_canonical_allocation X).mpr
    exact ⟨data, hrep, ⟨residual.allocation⟩⟩

end Erdos364
