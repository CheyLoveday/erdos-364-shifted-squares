import Erdos364.SquareMiddle.SourceNormalizer

namespace Erdos364

/-!
# Canonical right-flank counterexamples

This module is the conditional assembly boundary left after
`PAIR-PELL-COMPLETE`.  It does not assume that every raw Pell datum is a
square-middle candidate: admissibility remains an explicit hypothesis in the
right-flank eliminator.

A hypothetical counterexample is packaged with both of its canonical
square-cube normal forms.  This gives the exact additive two-kernel equation
without introducing an arithmetic axiom for its nonexistence.
-/

namespace PairPellIndexData

/-- The canonical centre carried by a Pell index datum. -/
noncomputable def center (data : PairPellIndexData) : Nat :=
  canonicalPellCenter data.D data.kernel data.k

/-- The shifted right flank whose non-powerfulness is the sole remaining
arithmetic target. -/
noncomputable def shiftValue (data : PairPellIndexData) : Nat :=
  data.center ^ 2 + 1

/-- An admissible datum represents its own canonical centre. -/
theorem represents_center (data : PairPellIndexData)
    (hadmissible : data.Admissible) :
    data.Represents data.center := by
  exact ⟨hadmissible, rfl⟩

/-- A powerful right flank has a unique positive `A²K³` normal form. -/
theorem existsUnique_upperNormalForm (data : PairPellIndexData)
    (hpowerful : PowerfulPos data.shiftValue) :
    ∃! upper : Nat × Nat,
      SquareCubeNormalForm data.shiftValue upper.1 upper.2 :=
  existsUnique_squareCubeNormalForm_of_powerfulPos hpowerful

end PairPellIndexData

/-- The exact remaining arithmetic eliminator.  The admissibility argument is
essential: `PairPellIndexData` also has inhabitants which do not arise from
the source normalizer. -/
def PellShiftClosed : Prop :=
  ∀ data : PairPellIndexData,
    data.Admissible → ¬ PowerfulPos data.shiftValue

/-- Exact-one-prime formulation of the right-flank target.  For a positive
natural, `q ∣ n` together with `¬ q² ∣ n` says that the prime `q` occurs to
valuation exactly one. -/
def PellShiftHasExactOnePrime : Prop :=
  ∀ data : PairPellIndexData,
    data.Admissible →
      ∃ q : Nat, q.Prime ∧ q ∣ data.shiftValue ∧ ¬ q ^ 2 ∣ data.shiftValue

/-- The non-powerfulness and exact-one-prime formulations are equivalent on
canonical shifted values.  Positivity is automatic from the final `+ 1`. -/
theorem pellShiftClosed_iff_hasExactOnePrime :
    PellShiftClosed ↔ PellShiftHasExactOnePrime := by
  constructor
  · intro hclosed data hadmissible
    have hnotPowerful := hclosed data hadmissible
    by_contra hnoPrime
    apply hnotPowerful
    refine ⟨?_, ?_⟩
    · simp [PairPellIndexData.shiftValue]
    · intro q hq hqDvd
      by_contra hqSquare
      exact hnoPrime ⟨q, hq, hqDvd, hqSquare⟩
  · intro hexact data hadmissible hpowerful
    obtain ⟨q, hq, hqDvd, hqNotSquare⟩ := hexact data hadmissible
    exact hqNotSquare (hpowerful.2 q hq hqDvd)

/-- Canonical data carried by a hypothetical square-middle counterexample.
The lower kernel is the Pell discriminant; the upper kernel is separately
normalized from the shifted right flank. -/
structure PairPellCounterexampleData where
  pell : PairPellIndexData
  admissible : pell.Admissible
  lowerSquarePart : Nat
  lowerNormalForm :
    SquareCubeNormalForm
      (pell.center ^ 2 - 1) lowerSquarePart pell.D
  upperSquarePart : Nat
  upperKernel : Nat
  upperNormalForm :
    SquareCubeNormalForm
      pell.shiftValue upperSquarePart upperKernel

namespace PairPellCounterexampleData

/-- The canonical centre of a counterexample package. -/
noncomputable abbrev center (data : PairPellCounterexampleData) : Nat :=
  data.pell.center

/-- The packaged lower datum represents the packaged centre. -/
theorem represents_center (data : PairPellCounterexampleData) :
    data.pell.Represents data.center :=
  data.pell.represents_center data.admissible

/-- The package reconstructs a genuine square-middle source at its canonical
centre. -/
theorem squareMiddle (data : PairPellCounterexampleData) :
    SquareMiddle data.center := by
  have hlower : SquareMiddleLowerSource data.center :=
    data.represents_center.toLowerSource
  refine ⟨hlower.1, hlower.2.2, ?_⟩
  exact powerfulPos_of_squareCubeNormalForm data.upperNormalForm

/-- The two normal forms differ by exactly two.  Addition, rather than
truncated natural subtraction, makes the statement boundary-safe. -/
theorem twoKernelEquation (data : PairPellCounterexampleData) :
    data.upperKernel ^ 3 * data.upperSquarePart ^ 2 =
      data.pell.D ^ 3 * data.lowerSquarePart ^ 2 + 2 := by
  have hcenter : 1 < data.center := data.squareMiddle.1
  calc
    data.upperKernel ^ 3 * data.upperSquarePart ^ 2 =
        data.upperSquarePart ^ 2 * data.upperKernel ^ 3 := by
          rw [Nat.mul_comm]
    _ = data.center ^ 2 + 1 := data.upperNormalForm.2.2.1.symm
    _ = data.center ^ 2 - 1 + 2 :=
      (square_sub_one_add_two hcenter).symm
    _ = data.lowerSquarePart ^ 2 * data.pell.D ^ 3 + 2 := by
      rw [data.lowerNormalForm.2.2.1]
    _ = data.pell.D ^ 3 * data.lowerSquarePart ^ 2 + 2 := by
      rw [Nat.mul_comm]

end PairPellCounterexampleData

/-- Construct the complete canonical counterexample package from an original
square-middle source. -/
noncomputable def pairPellCounterexampleDataOfSquareMiddle {X : Nat}
    (h : SquareMiddle X) : PairPellCounterexampleData := by
  let normalized := normalizeSquareMiddle h
  have hrep : normalized.pell.Represents X :=
    normalized.pell_represents_source
  let lowerExists : ∃ lowerSquarePart : Nat,
      SquareCubeNormalForm
        (X ^ 2 - 1) lowerSquarePart normalized.pell.D :=
    hrep.exists_squareSubOne_normalForm
  let lowerSquarePart : Nat := Classical.choose lowerExists
  have lowerNormalForm :
      SquareCubeNormalForm
        (X ^ 2 - 1) lowerSquarePart normalized.pell.D :=
    Classical.choose_spec lowerExists
  let upperExists : ∃! upper : Nat × Nat,
      SquareCubeNormalForm (X ^ 2 + 1) upper.1 upper.2 :=
    existsUnique_squareCubeNormalForm_of_powerfulPos h.2.2
  let upper : Nat × Nat := Classical.choose upperExists
  have upperNormalForm :
      SquareCubeNormalForm (X ^ 2 + 1) upper.1 upper.2 :=
    (Classical.choose_spec upperExists).1
  have hcenter : X = normalized.pell.center := normalized.center_eq
  have lowerNormalForm' :
      SquareCubeNormalForm
        (normalized.pell.center ^ 2 - 1) lowerSquarePart normalized.pell.D := by
    rw [← hcenter]
    exact lowerNormalForm
  have upperNormalForm' :
      SquareCubeNormalForm normalized.pell.shiftValue upper.1 upper.2 := by
    rw [PairPellIndexData.shiftValue, ← hcenter]
    exact upperNormalForm
  exact
    { pell := normalized.pell
      admissible := normalized.pellAdmissible
      lowerSquarePart := lowerSquarePart
      lowerNormalForm := lowerNormalForm'
      upperSquarePart := upper.1
      upperKernel := upper.2
      upperNormalForm := upperNormalForm' }

/-- The canonical package represents the exact source centre from which it
was normalized. -/
theorem pairPellCounterexampleDataOfSquareMiddle_represents {X : Nat}
    (h : SquareMiddle X) :
    (pairPellCounterexampleDataOfSquareMiddle h).pell.Represents X := by
  simpa only [pairPellCounterexampleDataOfSquareMiddle] using
    (normalizeSquareMiddle h).pell_represents_source

/-- Source-level equivalence between square-middle candidates and canonical
right-flank counterexample packages. -/
theorem squareMiddle_iff_pairPellCounterexample (X : Nat) :
    SquareMiddle X ↔
      ∃ data : PairPellCounterexampleData, data.pell.Represents X := by
  constructor
  · intro h
    exact
      ⟨pairPellCounterexampleDataOfSquareMiddle h,
        pairPellCounterexampleDataOfSquareMiddle_represents h⟩
  · rintro ⟨data, hrep⟩
    have hsource : SquareMiddle data.center := data.squareMiddle
    rw [hrep.2]
    exact hsource

/-- The universal right-flank theorem is exactly the nonexistence of a
canonical counterexample package.  This is a source-equivalent statement,
unlike the bare two-kernel equation. -/
theorem pellShiftClosed_iff_no_pairPellCounterexample :
    PellShiftClosed ↔ ¬ Nonempty PairPellCounterexampleData := by
  constructor
  · intro hclosed hcounterexample
    obtain ⟨data⟩ := hcounterexample
    exact
      hclosed data.pell data.admissible
        (powerfulPos_of_squareCubeNormalForm data.upperNormalForm)
  · intro hnone data hadmissible hpowerful
    have hrep : data.Represents data.center :=
      data.represents_center hadmissible
    obtain ⟨lowerSquarePart, lowerNormalForm⟩ :=
      hrep.exists_squareSubOne_normalForm
    obtain ⟨upper, upperNormalForm, _hunique⟩ :=
      data.existsUnique_upperNormalForm hpowerful
    apply hnone
    let counterexample : PairPellCounterexampleData :=
      { pell := data
        admissible := hadmissible
        lowerSquarePart := lowerSquarePart
        lowerNormalForm := lowerNormalForm
        upperSquarePart := upper.1
        upperKernel := upper.2
        upperNormalForm := upperNormalForm }
    exact ⟨counterexample⟩

/-- Once the single admissible right-flank theorem is supplied, full
square-middle closure is a direct consequence of the proved source
normalizer. -/
theorem squareMiddleClosed_of_pellShiftClosed
    (hShift : PellShiftClosed) :
    ∀ X : Nat, ¬ SquareMiddle X := by
  intro X hSquare
  let normalized := normalizeSquareMiddle hSquare
  apply hShift normalized.pell normalized.pellAdmissible
  have hright : PowerfulPos (X ^ 2 + 1) := normalized.upper_powerful
  rw [normalized.center_eq] at hright
  exact hright

end Erdos364
