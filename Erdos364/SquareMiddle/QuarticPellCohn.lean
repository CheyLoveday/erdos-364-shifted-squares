import Erdos364.SquareMiddle.QuarticPellCounterexample

namespace Erdos364

/-!
# Conditional Cohn bridge for divisible quartic Pell data

This file records the exact external theorem interface needed to remove the
Pell index from a square-middle counterexample.  It does **not** add Cohn's
classification as an axiom: `CohnQuarticPellClassification` is a proposition
which every downstream theorem takes as an explicit argument.

Literature source lock for that proposition:

* J. H. E. Cohn, *The Diophantine equation x⁴ - Dy² = 1, II*,
  Acta Arith. 78 (1997), no. 4, 401–403,
  DOI `10.4064/aa-78-4-401-403`.
* Gary Walsh, *The Diophantine equation X² - db²Y⁴ = 1*,
  Acta Arith. 87 (1998), no. 2, 179–188,
  DOI `10.4064/aa-87-2-179-188`, Theorem A (restatement).

The second Cohn branch is written as `X² + 1 = 2 A²`.  This is equivalent
to `X² = 2 A² - 1` over the intended positive naturals but avoids truncated
natural subtraction.
-/

/-- Explicit external-theorem interface for Cohn's quartic-Pell
classification on the exact source-preserving data used here.  The selected
`fundamentalX` is Mathlib's positive fundamental norm-one Pell coordinate.

This is a definition of a proposition, not a project axiom or theorem. -/
def CohnQuarticPellClassification : Prop :=
  ∀ {M X Y : Nat} (h : DivisibleNatQuarticPell M X Y),
    let hM : PellKernel M := ⟨h.M_one_lt, h.M_squarefree⟩
    X ^ 2 = fundamentalX M hM ∨
      X ^ 2 + 1 = 2 * fundamentalX M hM ^ 2

/-- Parity eliminates Cohn's second branch for the even centres in the
square-middle source. -/
theorem even_quarticPell_is_fundamental
    (hCohn : CohnQuarticPellClassification)
    {M X Y : Nat} (h : DivisibleNatQuarticPell M X Y) :
    let hM : PellKernel M := ⟨h.M_one_lt, h.M_squarefree⟩
    X ^ 2 = fundamentalX M hM := by
  dsimp
  rcases hCohn h with hfirst | hsecond
  · exact hfirst
  · have hXSquareEven : Even (X ^ 2) := by
      rw [pow_two]
      exact h.X_even.mul_right X
    have hleftOdd : Odd (X ^ 2 + 1) := hXSquareEven.add_one
    exfalso
    apply hleftOdd.not_two_dvd_nat
    rw [hsecond]
    exact (even_iff_two_dvd.mp (even_two_mul _))

/-- The remaining one-parameter arithmetic obstruction after the Cohn
classification: the fundamental `x` coordinate cannot be an even square at
the same time as the squarefree discriminant divides the fundamental `y`
coordinate. -/
def FundamentalUnitSquareDivisibleFree : Prop :=
  ∀ (M : Nat) (hM : PellKernel M),
    M % 8 = 7 →
      ¬ ∃ X : Nat,
        1 < X ∧
          Even X ∧
          fundamentalX M hM = X ^ 2 ∧
          M ∣ fundamentalY M hM

/-- Once the quartic solution is identified with the fundamental Pell
solution in its `x` coordinate, positivity determines its `y` coordinate as
well. -/
private theorem divisibleQuarticPell_y_eq_fundamentalY
    (hCohn : CohnQuarticPellClassification)
    {M X Y : Nat} (h : DivisibleNatQuarticPell M X Y) :
    let hM : PellKernel M := ⟨h.M_one_lt, h.M_squarefree⟩
    Y = fundamentalY M hM := by
  dsimp
  let hM : PellKernel M := ⟨h.M_one_lt, h.M_squarefree⟩
  have hx : X ^ 2 = fundamentalX M hM := by
    simpa [hM] using even_quarticPell_is_fundamental hCohn h
  have hquartic :
      fundamentalX M hM ^ 2 = M * Y ^ 2 + 1 := by
    calc
      fundamentalX M hM ^ 2 = (X ^ 2) ^ 2 := by rw [hx]
      _ = X ^ 4 := by ring
      _ = M * Y ^ 2 + 1 := h.equation
  have hfundSub := fundamental_pell_equation M hM
  have hfund :
      fundamentalX M hM ^ 2 =
        M * fundamentalY M hM ^ 2 + 1 := by
    omega
  have hproducts :
      M * Y ^ 2 = M * fundamentalY M hM ^ 2 := by
    omega
  have hsquares : Y ^ 2 = fundamentalY M hM ^ 2 :=
    Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt h.M_one_lt) hproducts
  exact Nat.pow_left_injective (by decide : (2 : Nat) ≠ 0) hsquares

/-- Cohn's classification plus the fundamental-unit obstruction excludes all
source-preserving divisible quartic-Pell packages. -/
theorem no_divisibleQuarticPellData_of_cohn
    (hCohn : CohnQuarticPellClassification)
    (hFundamental : FundamentalUnitSquareDivisibleFree) :
    ¬ Nonempty DivisibleQuarticPellData := by
  rintro ⟨data⟩
  let hM : PellKernel data.M :=
    ⟨data.valid.M_one_lt, data.valid.M_squarefree⟩
  have hx : data.X ^ 2 = fundamentalX data.M hM := by
    simpa [hM] using
      even_quarticPell_is_fundamental hCohn data.valid
  have hy : data.Y = fundamentalY data.M hM := by
    simpa [hM] using
      divisibleQuarticPell_y_eq_fundamentalY hCohn data.valid
  have hMdvd : data.M ∣ fundamentalY data.M hM := by
    rw [← hy]
    exact data.valid.M_dvd_Y
  exact
    (hFundamental data.M hM data.valid.kernel_mod_eight)
      ⟨data.X, data.valid.X_one_lt, data.valid.X_even, hx.symm, hMdvd⟩

/-- The conditional fundamental-unit exclusion discharges the existing
right-flank eliminator without changing its source-facing interface. -/
theorem pellShiftClosed_of_cohn_and_fundamentalUnit
    (hCohn : CohnQuarticPellClassification)
    (hFundamental : FundamentalUnitSquareDivisibleFree) :
    PellShiftClosed := by
  rw [pellShiftClosed_iff_no_pairPellCounterexample]
  rintro ⟨data⟩
  apply no_divisibleQuarticPellData_of_cohn hCohn hFundamental
  exact ⟨data.toDivisibleQuarticPellData⟩

/-- Conditional final assembly: the two explicit arithmetic inputs imply the
already-normalized square-middle theorem. -/
theorem squareMiddleClosed_of_cohn_and_fundamentalUnit
    (hCohn : CohnQuarticPellClassification)
    (hFundamental : FundamentalUnitSquareDivisibleFree) :
    ∀ X : Nat, ¬ SquareMiddle X :=
  squareMiddleClosed_of_pellShiftClosed
    (pellShiftClosed_of_cohn_and_fundamentalUnit hCohn hFundamental)

/-- Unconditionally, square-middle closure rules out the fundamental-unit
configuration: such a configuration itself reconstructs divisible
quartic-Pell data and hence a square-middle source. -/
theorem fundamentalUnitSquareDivisibleFree_of_squareMiddleClosed
    (hClosed : ∀ X : Nat, ¬ SquareMiddle X) :
    FundamentalUnitSquareDivisibleFree := by
  intro M hM _hmod
  rintro ⟨X, hX, hEven, hfundX, hMdvd⟩
  apply hClosed X
  apply DivisibleNatQuarticPell.toSquareMiddle (M := M)
      (Y := fundamentalY M hM)
  have hfundSub := fundamental_pell_equation M hM
  have hfundEq :
      fundamentalX M hM ^ 2 =
        M * fundamentalY M hM ^ 2 + 1 := by
    omega
  exact
    { X_one_lt := hX
      X_even := hEven
      Y_pos := fundamentalY_pos M hM
      M_one_lt := hM.1
      M_squarefree := hM.2
      equation := by
        calc
          X ^ 4 = (X ^ 2) ^ 2 := by ring
          _ = fundamentalX M hM ^ 2 := by rw [hfundX]
          _ = M * fundamentalY M hM ^ 2 + 1 := hfundEq
      M_dvd_Y := hMdvd }

/-- Conditional on the source-locked Cohn classification, the one-parameter
fundamental-unit obstruction is exactly square-middle closure, not merely a
sufficient condition for it. -/
theorem fundamentalUnitSquareDivisibleFree_iff_squareMiddleClosed
    (hCohn : CohnQuarticPellClassification) :
    FundamentalUnitSquareDivisibleFree ↔
      ∀ X : Nat, ¬ SquareMiddle X := by
  constructor
  · exact squareMiddleClosed_of_cohn_and_fundamentalUnit hCohn
  · exact fundamentalUnitSquareDivisibleFree_of_squareMiddleClosed

end Erdos364
