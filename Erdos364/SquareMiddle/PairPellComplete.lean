import Erdos364.SquareMiddle.PellCanonical
import Erdos364.SquareMiddle.PellDivisibilityRank
import Erdos364.SquareMiddle.PellParity
import Erdos364.SquareMiddle.SourceArithmetic

namespace Erdos364

/-- The exact lower-pair source normalized by `PAIR-PELL-COMPLETE`.  This is
strictly weaker than `SquareMiddle`: the shifted right flank is not assumed. -/
def SquareMiddleLowerSource (X : Nat) : Prop :=
  1 < X ∧ Even X ∧ PowerfulPos (X ^ 2 - 1)

/-- The canonical Pell exponent attached to a kernel and a nonnegative
parameter `k`. -/
noncomputable def canonicalPellIndex
    (D : Nat) (hD : PellKernel D) (k : Nat) : Nat :=
  pellRank D hD * (2 * k + 1)

/-- The corresponding canonical center. -/
noncomputable def canonicalPellCenter
    (D : Nat) (hD : PellKernel D) (k : Nat) : Nat :=
  pellX D hD (canonicalPellIndex D hD k)

/-- Unindexed data carried by a canonical lower-pair representation.  The
source center appears only in `Represents`, so the final statement can use a
literal unique-existence quantifier over this record. -/
structure PairPellIndexData where
  D : Nat
  kernel : PellKernel D
  k : Nat

/-- Arithmetic admissibility of a canonical Pell datum. -/
def PairPellIndexData.Admissible (data : PairPellIndexData) : Prop :=
  Odd data.D ∧ Even (fundamentalX data.D data.kernel)

/-- A datum represents `X` when it is admissible and its canonical center is
exactly `X`. -/
def PairPellIndexData.Represents (data : PairPellIndexData) (X : Nat) : Prop :=
  data.Admissible ∧
    X = canonicalPellCenter data.D data.kernel data.k

/-- Exact lower-pair formulation of `PAIR-PELL-COMPLETE`.  This definition
states the target without postulating it; `pairPellCompleteTarget_proved`
discharges it below using the concrete normalization path. -/
def PairPellCompleteTarget : Prop :=
  ∀ X : Nat,
    SquareMiddleLowerSource X ↔
      ∃! data : PairPellIndexData, data.Represents X

/-- Every canonical exponent is positive. -/
theorem canonicalPellIndex_pos
    (D : Nat) (hD : PellKernel D) (k : Nat) :
    0 < canonicalPellIndex D hD k := by
  exact Nat.mul_pos (pellRank_pos D hD) (by omega)

/-- Canonical exponents are injective in `k`. -/
theorem canonicalPellIndex_injective
    (D : Nat) (hD : PellKernel D) :
    Function.Injective (canonicalPellIndex D hD) := by
  intro k l hkl
  unfold canonicalPellIndex at hkl
  have hoddFactors : 2 * k + 1 = 2 * l + 1 :=
    Nat.eq_of_mul_eq_mul_left (pellRank_pos D hD) hkl
  omega

/-- Canonical centers are injective in `k`.  This is the uniqueness hook used
by the eventual source normalizer after uniqueness of the kernel is known. -/
theorem canonicalPellCenter_injective
    (D : Nat) (hD : PellKernel D) :
    Function.Injective (canonicalPellCenter D hD) := by
  intro k l hkl
  apply canonicalPellIndex_injective D hD
  apply pellX_injective D hD
  exact hkl

/-- Every lower-pair source produces a concrete canonical Pell datum. -/
theorem SquareMiddleLowerSource.exists_pairPellIndexData
    {X : Nat} (h : SquareMiddleLowerSource X) :
    ∃ data : PairPellIndexData, data.Represents X := by
  obtain ⟨Z, D, hform⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos h.2.2
  have hD_odd : Odd D :=
    hform.kernel_odd_of_even_center h.1 h.2.1
  have hpell : DivisibleNatPell D X (D * Z) :=
    squareSubOne_normalForm_to_divisibleNatPell h.1 hform
  let hD : PellKernel D := ⟨hpell.D_one_lt, hpell.D_squarefree⟩
  obtain ⟨n, hxNat, hyNat⟩ := hpell.exists_pellCoordinates
  change X = pellX D hD n at hxNat
  change D * Z = pellY D hD n at hyNat
  have hD_dvd_y : D ∣ pellY D hD n := by
    rw [← hyNat]
    exact hpell.D_dvd_Y
  have hx_even : Even (pellX D hD n) := by
    rw [← hxNat]
    exact h.2.1
  obtain ⟨hfund_even, k, hk⟩ :=
    (kernel_dvd_pellY_and_pellX_even_iff_rank_odd_index
      D hD hD_odd n).mp ⟨hD_dvd_y, hx_even⟩
  let data : PairPellIndexData :=
    { D := D
      kernel := hD
      k := k }
  refine ⟨data, ⟨⟨hD_odd, hfund_even⟩, ?_⟩⟩
  dsimp [data, canonicalPellCenter, canonicalPellIndex]
  rw [← hk]
  exact hxNat

/-- A represented canonical Pell center reconstructs the complete lower-pair
source. -/
theorem PairPellIndexData.Represents.toLowerSource
    {data : PairPellIndexData} {X : Nat}
    (h : data.Represents X) :
    SquareMiddleLowerSource X := by
  rcases h with ⟨⟨hD_odd, hfund_even⟩, hX⟩
  let n := canonicalPellIndex data.D data.kernel data.k
  have hn_pos : 0 < n := by
    simpa [n] using
      canonicalPellIndex_pos data.D data.kernel data.k
  have hboth :
      data.D ∣ pellY data.D data.kernel n ∧
        Even (pellX data.D data.kernel n) := by
    apply
      (kernel_dvd_pellY_and_pellX_even_iff_rank_odd_index
        data.D data.kernel hD_odd n).mpr
    refine ⟨hfund_even, data.k, ?_⟩
    rfl
  have hpell :=
    pellCoordinates_divisibleNatPell
      data.D data.kernel n hn_pos hboth.1
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · simpa [canonicalPellCenter, n] using hpell.X_one_lt
  · simpa [canonicalPellCenter, n] using hboth.2
  · simpa [canonicalPellCenter, n] using
      powerfulPos_pellX_square_sub_one
        data.D data.kernel n hn_pos hboth.1

/-- A represented datum reconstructs a lower normal form whose kernel is
exactly the datum's discriminant. -/
theorem PairPellIndexData.Represents.exists_squareSubOne_normalForm
    {data : PairPellIndexData} {X : Nat}
    (h : data.Represents X) :
    ∃ Z : Nat, SquareCubeNormalForm (X ^ 2 - 1) Z data.D := by
  rcases h with ⟨⟨hD_odd, hfund_even⟩, hX⟩
  let n := canonicalPellIndex data.D data.kernel data.k
  have hn_pos : 0 < n := by
    simpa [n] using
      canonicalPellIndex_pos data.D data.kernel data.k
  have hboth :
      data.D ∣ pellY data.D data.kernel n ∧
        Even (pellX data.D data.kernel n) := by
    apply
      (kernel_dvd_pellY_and_pellX_even_iff_rank_odd_index
        data.D data.kernel hD_odd n).mpr
    exact ⟨hfund_even, data.k, rfl⟩
  have hpell :=
    pellCoordinates_divisibleNatPell
      data.D data.kernel n hn_pos hboth.1
  obtain ⟨Z, hZ, _hunique⟩ :=
    hpell.existsUnique_squareSubOne_normalForm_factor
  refine ⟨Z, ?_⟩
  rw [hX]
  simpa [canonicalPellCenter, n] using hZ.2

/-- Two canonical Pell data representing the same center are equal. Kernel
uniqueness comes from the established `A²D³` normal form; parameter
uniqueness then comes from injectivity of the canonical Pell centers. -/
theorem pairPellIndexData_unique
    {X : Nat} {first second : PairPellIndexData}
    (hfirst : first.Represents X)
    (hsecond : second.Represents X) :
    first = second := by
  obtain ⟨Zfirst, hformFirst⟩ :=
    hfirst.exists_squareSubOne_normalForm
  obtain ⟨Zsecond, hformSecond⟩ :=
    hsecond.exists_squareSubOne_normalForm
  have hsource : SquareMiddleLowerSource X := hfirst.toLowerSource
  have hD : first.D = second.D :=
    squareCubeNormalForm_kernel_unique
      hsource.2.2.1 hformFirst hformSecond
  cases first with
  | mk D hDkernel k =>
      cases second with
      | mk E hEkernel l =>
          dsimp at hD ⊢
          subst E
          have hKernelProof : hEkernel = hDkernel :=
            Subsingleton.elim _ _
          subst hEkernel
          have hcenters :
              canonicalPellCenter D hDkernel k =
                canonicalPellCenter D hDkernel l :=
            hfirst.2.symm.trans hsecond.2
          have hkl : k = l :=
            canonicalPellCenter_injective D hDkernel hcenters
          subst l
          rfl

/-- Kernel-checked `PAIR-PELL-COMPLETE`: nontrivial even centers with a
powerful lower square-neighbour are exactly, and uniquely, the admissible
canonical Pell centers. -/
theorem pairPellComplete (X : Nat) :
    SquareMiddleLowerSource X ↔
      ∃! data : PairPellIndexData, data.Represents X := by
  constructor
  · intro hsource
    obtain ⟨data, hdata⟩ := hsource.exists_pairPellIndexData
    exact ⟨data, hdata, fun other hother =>
      pairPellIndexData_unique hother hdata⟩
  · rintro ⟨data, hdata, _hunique⟩
    exact hdata.toLowerSource

/-- The quantified target definition is now discharged by the concrete
normalizer theorem above. -/
theorem pairPellCompleteTarget_proved : PairPellCompleteTarget := by
  intro X
  exact pairPellComplete X

end Erdos364
