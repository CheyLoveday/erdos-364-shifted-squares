import Erdos364.SquareMiddle.RightFlankSupport
import Erdos364.SquareMiddle.RightFlankResidues
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace Erdos364

/-!
# Quadratic-character constraints on the two square-cube kernels

The simultaneous normal forms

`X² - 1 = U²D³`,  `X² + 1 = V²K³`

force reciprocal quadratic-character restrictions at every prime in either
kernel.  The intermediate `IsSquare` statements below expose the exact local
square identities used by the Legendre-symbol corollaries.
-/

private theorem legendreSym_eq_of_mul_isSquare
    {p a b : Nat} [Fact p.Prime]
    (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    (hsquare : IsSquare ((a * b : Nat) : ZMod p)) :
    legendreSym p a = legendreSym p b := by
  have hab : ((a * b : Nat) : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_mul] using mul_ne_zero ha hb
  have hprodNat : legendreSym p (a * b) = 1 :=
    (legendreSym.eq_one_iff' p hab).2 hsquare
  have hprod : legendreSym p a * legendreSym p b = 1 := by
    rw [← hprodNat]
    simpa only [Nat.cast_mul] using
      (legendreSym.mul p (a : Int) (b : Int)).symm
  have haInt : ((a : Int) : ZMod p) ≠ 0 := by exact_mod_cast ha
  rcases legendreSym.eq_one_or_neg_one p haInt with haOne | haNeg
  · have hbOne : legendreSym p b = 1 := by simpa [haOne] using hprod
    exact haOne.trans hbOne.symm
  · have hbNeg : legendreSym p b = -1 := by
      rw [haNeg] at hprod
      linarith
    exact haNeg.trans hbNeg.symm

private theorem prime_not_dvd_opposite_support
    {p left right : Nat} (hp : p.Prime)
    (hcop : Nat.Coprime left right) (hpLeft : p ∣ left) :
    ¬ p ∣ right := by
  intro hpRight
  have hpOne : p ∣ 1 := by
    simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hpLeft hpRight
  exact hp.not_dvd_one hpOne

/-- At a prime of the lower kernel, `2K` is a square modulo that prime.
This is the raw local identity behind `(K/p) = (2/p)`. -/
theorem isSquare_two_mul_upperKernel_mod_lowerPrime
    {X U D V K p : Nat} (hX : 1 < X) (_hEven : Even X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K)
    (hp : p.Prime) (hpD : p ∣ D) :
    IsSquare ((2 * K : Nat) : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwoKernel :=
    squareCubeNormalForms_twoKernel_additive hX hlower hupper
  have hpDZero : (D : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff D p).2 hpD
  have hcast := congrArg (fun n : Nat => (n : ZMod p)) htwoKernel
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add] at hcast
  rw [hpDZero, zero_pow (by decide : 3 ≠ 0), zero_mul, zero_add] at hcast
  refine ⟨(K : ZMod p) ^ 2 * (V : ZMod p), ?_⟩
  calc
    ((2 * K : Nat) : ZMod p) =
        ((K : ZMod p) ^ 3 * (V : ZMod p) ^ 2) * (K : ZMod p) := by
          rw [hcast]
          norm_num
    _ = ((K : ZMod p) ^ 2 * (V : ZMod p)) *
          ((K : ZMod p) ^ 2 * (V : ZMod p)) := by ring

/-- At a prime of the upper kernel, `2D` is a square modulo that prime.
The extra square root of `-1` is supplied by the centre itself. -/
theorem isSquare_two_mul_lowerKernel_mod_upperPrime
    {X U D V K q : Nat} (hX : 1 < X) (_hEven : Even X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K)
    (hq : q.Prime) (hqK : q ∣ K) :
    IsSquare ((2 * D : Nat) : ZMod q) := by
  letI : Fact q.Prime := ⟨hq⟩
  have htwoKernel :=
    squareCubeNormalForms_twoKernel_additive hX hlower hupper
  have hqKZero : (K : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff K q).2 hqK
  have hcast := congrArg (fun n : Nat => (n : ZMod q)) htwoKernel
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add] at hcast
  rw [hqKZero, zero_pow (by decide : 3 ≠ 0), zero_mul] at hcast
  have hDU : (D : ZMod q) ^ 3 * (U : ZMod q) ^ 2 = -2 := by
    exact eq_neg_of_add_eq_zero_left hcast.symm
  have hqValue : q ∣ X ^ 2 + 1 :=
    dvd_trans hqK (squareCubeNormalForm_kernel_dvd_value hupper)
  have hvalueZero : ((X ^ 2 + 1 : Nat) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (X ^ 2 + 1) q).2 hqValue
  norm_num only [Nat.cast_add, Nat.cast_pow] at hvalueZero
  have hXsq : (X : ZMod q) ^ 2 = -1 :=
    eq_neg_of_add_eq_zero_left hvalueZero
  refine
    ⟨(X : ZMod q) * (D : ZMod q) ^ 2 * (U : ZMod q), ?_⟩
  calc
    ((2 * D : Nat) : ZMod q) =
        (-1 : ZMod q) * (-2 : ZMod q) * (D : ZMod q) := by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    _ = (X : ZMod q) ^ 2 *
          ((D : ZMod q) ^ 3 * (U : ZMod q) ^ 2) * (D : ZMod q) := by
            rw [hXsq, hDU]
    _ = ((X : ZMod q) * (D : ZMod q) ^ 2 * (U : ZMod q)) *
          ((X : ZMod q) * (D : ZMod q) ^ 2 * (U : ZMod q)) := by ring

/-- If `p` is a prime factor of the lower kernel, then the upper kernel and
`2` have the same Legendre symbol modulo `p`. -/
theorem legendreSym_upperKernel_eq_two_of_dvd_lowerKernel
    {X U D V K p : Nat} [Fact p.Prime]
    (hX : 1 < X) (hEven : Even X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K)
    (hpD : p ∣ D) :
    legendreSym p K = legendreSym p 2 := by
  have hp : p.Prime := Fact.out
  have hsupports :=
    squareCubeNormalForm_supports_coprime_of_even_center
      hX hEven hlower hupper
  have hpLeft : p ∣ D * U := dvd_trans hpD (dvd_mul_right D U)
  have hpRight : ¬ p ∣ K * V :=
    prime_not_dvd_opposite_support hp hsupports hpLeft
  have hpK : ¬ p ∣ K := fun h =>
    hpRight (dvd_trans h (dvd_mul_right K V))
  have hKZero : (K : ZMod p) ≠ 0 := fun h =>
    hpK ((ZMod.natCast_eq_zero_iff K p).1 h)
  have hpLower : p ∣ X ^ 2 - 1 :=
    dvd_trans hpD (squareCubeNormalForm_kernel_dvd_value hlower)
  have hsquareEven : Even (X ^ 2) :=
    Nat.even_pow.mpr ⟨hEven, by decide⟩
  have hLowerOdd : Odd (X ^ 2 - 1) :=
    Nat.Even.sub_odd (by nlinarith : 1 ≤ X ^ 2) hsquareEven odd_one
  have hpNeTwo : p ≠ 2 := by
    intro h
    subst p
    exact hLowerOdd.not_two_dvd_nat hpLower
  have hTwoZero : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpTwo : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by decide) hpTwo
    exact hpNeTwo (Nat.le_antisymm hpLe hp.two_le)
  apply legendreSym_eq_of_mul_isSquare hKZero hTwoZero
  simpa [Nat.mul_comm] using
    isSquare_two_mul_upperKernel_mod_lowerPrime
      hX hEven hlower hupper hp hpD

/-- If `q` is a prime factor of the upper kernel, then the lower kernel and
`2` have the same Legendre symbol modulo `q`.  The fact `q = 1 (mod 4)` is
proved separately by `prime_mod_four_eq_one_of_dvd_square_add_one`; the local
square proof here uses the equivalent square root of `-1` supplied by `X`. -/
theorem legendreSym_lowerKernel_eq_two_of_dvd_upperKernel
    {X U D V K q : Nat} [Fact q.Prime]
    (hX : 1 < X) (hEven : Even X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K)
    (hqK : q ∣ K) :
    legendreSym q D = legendreSym q 2 := by
  have hq : q.Prime := Fact.out
  have hsupports :=
    squareCubeNormalForm_supports_coprime_of_even_center
      hX hEven hlower hupper
  have hqRight : q ∣ K * V := dvd_trans hqK (dvd_mul_right K V)
  have hqLeft : ¬ q ∣ D * U :=
    prime_not_dvd_opposite_support hq hsupports.symm hqRight
  have hqD : ¬ q ∣ D := fun h =>
    hqLeft (dvd_trans h (dvd_mul_right D U))
  have hDZero : (D : ZMod q) ≠ 0 := fun h =>
    hqD ((ZMod.natCast_eq_zero_iff D q).1 h)
  have hqModFour : q % 4 = 1 :=
    hupper.prime_mod_four_eq_one_of_dvd_right_kernel hEven hq hqK
  have hqNeTwo : q ≠ 2 := by omega
  have hTwoZero : (2 : ZMod q) ≠ 0 := by
    intro hzero
    have hqTwo : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 hzero
    have hqLe : q ≤ 2 := Nat.le_of_dvd (by decide) hqTwo
    exact hqNeTwo (Nat.le_antisymm hqLe hq.two_le)
  apply legendreSym_eq_of_mul_isSquare hDZero hTwoZero
  simpa [Nat.mul_comm] using
    isSquare_two_mul_lowerKernel_mod_upperPrime
      hX hEven hlower hupper hq hqK

end Erdos364
