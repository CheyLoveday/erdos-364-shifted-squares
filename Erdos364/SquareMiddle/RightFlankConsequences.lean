import Erdos364.SquareMiddle.RightFlankCounterexample
import Erdos364.SquareMiddle.RightFlankNegativePell
import Erdos364.SquareMiddle.RightFlankQuadratic

namespace Erdos364

/-!
# Canonical right-flank consequences

This module specializes the raw support, residue, quadratic-character, and
negative-Pell lemmas to `PairPellCounterexampleData`.  It remains a
normalization layer: no theorem here excludes the resulting data.
-/

namespace PairPellCounterexampleData

/-- The canonical counterexample centre is nontrivial. -/
theorem center_one_lt (data : PairPellCounterexampleData) : 1 < data.center :=
  data.squareMiddle.1

/-- The canonical counterexample centre is even. -/
theorem center_even (data : PairPellCounterexampleData) : Even data.center :=
  data.squareMiddle.center_even

/-- Every lower square/kernel factor is coprime to every upper
square/kernel factor. -/
theorem support_coprime (data : PairPellCounterexampleData) :
    Nat.Coprime
      (data.pell.D * data.lowerSquarePart)
      (data.upperKernel * data.upperSquarePart) :=
  squareCubeNormalForm_supports_coprime_of_even_center
    data.center_one_lt data.center_even
    data.lowerNormalForm data.upperNormalForm

/-- The two squarefree cube kernels are coprime. -/
theorem kernels_coprime (data : PairPellCounterexampleData) :
    Nat.Coprime data.pell.D data.upperKernel :=
  squareCubeNormalForm_kernels_coprime_of_even_center
    data.center_one_lt data.center_even
    data.lowerNormalForm data.upperNormalForm

/-- The upper cube kernel is genuinely nontrivial. -/
theorem upperKernel_one_lt (data : PairPellCounterexampleData) :
    1 < data.upperKernel :=
  squareCubeNormalForm_kernel_one_lt_of_square_add_one
    data.center_one_lt data.upperNormalForm

/-- Every prime in the complete upper support is one modulo four. -/
theorem upperSupport_prime_mod_four_eq_one
    (data : PairPellCounterexampleData) {q : Nat}
    (hq : q.Prime)
    (hqDvd : q ∣ data.upperKernel * data.upperSquarePart) :
    q % 4 = 1 := by
  apply prime_mod_four_eq_one_of_dvd_square_add_one data.center_even hq
  change q ∣ data.pell.shiftValue
  apply dvd_trans hqDvd
  simpa [Nat.mul_comm] using
    data.upperNormalForm.squareFactor_mul_kernel_dvd_value

/-- In particular, `3` cannot occur anywhere in the upper support. -/
theorem three_not_dvd_upperSupport (data : PairPellCounterexampleData) :
    ¬ 3 ∣ data.upperKernel * data.upperSquarePart := by
  intro hthree
  have hmod := data.upperSupport_prime_mod_four_eq_one Nat.prime_three hthree
  norm_num at hmod

/-- Exact mod-eight implications for the two possible even-centre branches. -/
theorem kernel_mod_eight_pairing (data : PairPellCounterexampleData) :
    (data.center % 4 = 0 →
        data.pell.D % 8 = 7 ∧ data.upperKernel % 8 = 1) ∧
      (data.center % 4 = 2 →
        data.pell.D % 8 = 3 ∧ data.upperKernel % 8 = 5) :=
  squareMiddle_twoKernel_mod_eight_pairing
    data.center_one_lt data.center_even
    data.lowerNormalForm data.upperNormalForm

/-- Every counterexample lies in exactly one of the two displayed coefficient
residue branches. -/
theorem kernel_mod_eight_cases (data : PairPellCounterexampleData) :
    (data.pell.D % 8 = 7 ∧ data.upperKernel % 8 = 1) ∨
      (data.pell.D % 8 = 3 ∧ data.upperKernel % 8 = 5) := by
  have hmodTwo : data.center % 4 % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd data.center (by decide : 2 ∣ 4)]
    exact Nat.even_iff.mp data.center_even
  have hmodLt : data.center % 4 < 4 := Nat.mod_lt _ (by decide)
  have hcases : data.center % 4 = 0 ∨ data.center % 4 = 2 := by
    omega
  rcases hcases with hzero | htwo
  · exact Or.inl (data.kernel_mod_eight_pairing.1 hzero)
  · exact Or.inr (data.kernel_mod_eight_pairing.2 htwo)

/-- Lower-kernel prime quadratic-character constraint. -/
theorem upperKernel_legendre_eq_two_of_dvd_lowerKernel
    (data : PairPellCounterexampleData) {p : Nat} [Fact p.Prime]
    (hpD : p ∣ data.pell.D) :
    legendreSym p data.upperKernel = legendreSym p 2 :=
  legendreSym_upperKernel_eq_two_of_dvd_lowerKernel
    data.center_one_lt data.center_even
    data.lowerNormalForm data.upperNormalForm hpD

/-- Upper-kernel prime quadratic-character constraint. -/
theorem lowerKernel_legendre_eq_two_of_dvd_upperKernel
    (data : PairPellCounterexampleData) {q : Nat} [Fact q.Prime]
    (hqK : q ∣ data.upperKernel) :
    legendreSym q data.pell.D = legendreSym q 2 :=
  legendreSym_lowerKernel_eq_two_of_dvd_upperKernel
    data.center_one_lt data.center_even
    data.lowerNormalForm data.upperNormalForm hqK

/-- The upper normal form gives the exact divisible negative-Pell datum at
the same canonical centre. -/
theorem upper_negativePell (data : PairPellCounterexampleData) :
    DivisibleNatNegativePell data.upperKernel data.center
      (data.upperKernel * data.upperSquarePart) :=
  squareAddOne_normalForm_to_divisibleNatNegativePell
    data.center_one_lt data.upperNormalForm

/-- A counterexample is an intersection of a positive divisible-Pell source
and a negative divisible-Pell source with one shared centre.  This is the
source-preserving replacement for the lossy bare two-kernel equation. -/
theorem simultaneous_divisiblePell (data : PairPellCounterexampleData) :
    DivisibleNatPell data.pell.D data.center
        (data.pell.D * data.lowerSquarePart) ∧
      DivisibleNatNegativePell data.upperKernel data.center
        (data.upperKernel * data.upperSquarePart) := by
  exact
    ⟨squareSubOne_normalForm_to_divisibleNatPell
        data.center_one_lt data.lowerNormalForm,
      data.upper_negativePell⟩

end PairPellCounterexampleData

/-- Boundary regression: the right flank can be powerful at an even centre
when the lower canonical-Pell source is absent. -/
theorem rightFlank_only_counterexample_682 :
    Even 682 ∧
      PowerfulPos (682 ^ 2 + 1) ∧
        ¬ PowerfulPos (682 ^ 2 - 1) := by
  constructor
  · norm_num [even_iff_two_dvd]
  constructor
  · apply powerfulPos_of_squareCubeNormalForm
    refine ⟨(by norm_num : 0 < 61), (by norm_num : 0 < 5), by norm_num, ?_⟩
    intro p hp hpSquare
    have hpLe : p ^ 2 ≤ 5 := Nat.le_of_dvd (by decide) hpSquare
    have hpEq : p = 2 := by
      have hpTwoLe := hp.two_le
      nlinarith
    subst p
    norm_num at hpSquare
  · apply not_powerfulPos_of_three_dvd_not_nine
    · norm_num
    · norm_num

/-- Boundary regression for the lossy coefficient projection: these two
square-cube-shaped values differ by two, but their midpoint is strictly
between consecutive squares. -/
theorem twoKernel_projection_falseConverse_control :
    5 ^ 3 * 332717 ^ 2 = 3 ^ 3 * 715893 ^ 2 + 2 ∧
      3719889 ^ 2 < 3 ^ 3 * 715893 ^ 2 + 1 ∧
        3 ^ 3 * 715893 ^ 2 + 1 < 3719890 ^ 2 := by
  norm_num

end Erdos364
