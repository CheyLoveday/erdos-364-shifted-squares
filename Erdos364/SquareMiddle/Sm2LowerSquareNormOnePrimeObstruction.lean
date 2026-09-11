import Erdos364.SquareMiddle.RightFlankUpperKernelSquarePlusOne
import Erdos364.SquareMiddle.Sm2LowerSquareAllocation

namespace Erdos364

open Pell

/-!
# A norm-one prime obstruction for the `sm2LowerSquare` leaf

Let `e` be the positive fundamental norm-one solution for an upper kernel
`K`.  If `e` reduces to the identity pair `(1, 0)` modulo a prime
`q = 3 mod 4`, then every retained divisible negative-Pell source real
coordinate `X` is zero modulo `q`.  Consequently `X - 1` is a quadratic
nonsquare modulo `q`.

This is a leaf-specific certificate: it excludes the intersection of the
`sm2LowerSquare` leaf with the selected upper-kernel fibre.  It need not
exclude other leaves in that fibre.

For the square-plus-one family `K = t² + 1`, the explicit fundamental
solution `(2t² + 1, 2t)` is the identity modulo every prime divisor of `t`.
Thus every prime `q = 3 mod 4` dividing `t` supplies such a certificate.
-/

private theorem pellSolution_pow_identity_mod
    {K q : Nat} (e : Pell.Solution₁ (K : Int))
    (hx : (e.x : ZMod q) = 1)
    (hy : (e.y : ZMod q) = 0) :
    ∀ n : Nat,
      (((e ^ n).x : Int) : ZMod q) = 1 ∧
        (((e ^ n).y : Int) : ZMod q) = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
      push_cast
      simp [ih.1, ih.2, hx, hy]

/-- If the selected fundamental norm-one solution is the identity modulo a
prime `q = 3 mod 4`, then every retained divisible negative-Pell source real
coordinate has a nonsquare predecessor modulo `q`.

The source-depth condition `K ∣ W` is retained by the input structure but is
not used in the proof of this source-typed conclusion. -/
theorem
    divisibleNatNegativePell_center_sub_one_not_square_of_normOne_identity_mod
    {K q X W : Nat} (hK : 2 < K) (hq : q.Prime)
    (hqMod : q % 4 = 3)
    (e : Pell.Solution₁ (K : Int))
    (hfund : Pell.IsFundamental e)
    (hex : (e.x : ZMod q) = 1)
    (hey : (e.y : ZMod q) = 0)
    (h : DivisibleNatNegativePell K X W) :
    ¬ IsSquare ((((X : Int) - 1 : Int) : ZMod q)) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hPell : X ^ 2 + 1 = K * W ^ 2 := h.equation.symm
  obtain ⟨n, _hnOdd, hn, _hSign⟩ :=
    negativePell_eq_fundamental_odd_power_and_x_mod_kernel
      hK e hfund (Nat.zero_lt_of_lt h.X_one_lt) h.W_pos hPell
  have hstate := pellSolution_pow_identity_mod e hex hey n
  have hcoord := congrArg Pell.Solution₁.x hn
  have hreal :
      (negativePellSquareSolution hPell).x =
        2 * (X : Int) ^ 2 + 1 := by
    simp only [negativePellSquareSolution, Pell.Solution₁.x_mk]
    have hz :
        (X : Int) ^ 2 + 1 = K * (W : Int) ^ 2 := by
      exact_mod_cast hPell
    linear_combination -hz
  have hcoordMod :=
    congrArg (fun z : Int => (z : ZMod q)) hcoord
  rw [hreal] at hcoordMod
  push_cast at hcoordMod
  rw [hstate.1] at hcoordMod
  have htwoSq :
      (2 : ZMod q) * (X : ZMod q) ^ 2 = 0 := by
    linear_combination hcoordMod
  have hqThree : 3 ≤ q := by omega
  have htwoNe : (2 : ZMod q) ≠ 0 := by
    intro hzero
    have hdiv : q ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 q).mp hzero
    have hle : q ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hxsq : (X : ZMod q) ^ 2 = 0 :=
    (mul_eq_zero.mp htwoSq).resolve_left htwoNe
  have hxmul : (X : ZMod q) * (X : ZMod q) = 0 := by
    simpa [pow_two] using hxsq
  have hxzero : (X : ZMod q) = 0 :=
    (mul_eq_zero.mp hxmul).elim id id
  push_cast
  change ¬ IsSquare ((X : ZMod q) - 1)
  intro hsquare
  have hneg : IsSquare (-1 : ZMod q) := by
    simpa [hxzero] using hsquare
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hneg) hqMod

/-- Generic source-to-cell adapter for a norm-one identity-prime
certificate. -/
theorem
    Sm2LowerSquareAllocation.upperKernel_ne_of_normOne_identity_mod_prime
    {K q : Nat} (hK : 2 < K) (hq : q.Prime)
    (hqMod : q % 4 = 3)
    (e : Pell.Solution₁ (K : Int))
    (hfund : Pell.IsFundamental e)
    (hex : (e.x : ZMod q) = 1)
    (hey : (e.y : ZMod q) = 0)
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.upperKernel ≠ K := by
  intro hupper
  have hnegative :
      DivisibleNatNegativePell K data.center
        (data.upperKernel * data.upperSquarePart) := by
    simpa [hupper] using data.upper_negativePell
  have hnot :=
    divisibleNatNegativePell_center_sub_one_not_square_of_normOne_identity_mod
      hK hq hqMod e hfund hex hey hnegative
  apply hnot
  refine ⟨(allocation.y : ZMod q), ?_⟩
  have hcenterInt :
      (data.center : Int) - 1 = (allocation.y : Int) ^ 2 := by
    rw [allocation.center_eq]
    push_cast
    ring
  have hcast :=
    congrArg (fun z : Int => (z : ZMod q)) hcenterInt
  push_cast at hcast
  simpa [pow_two] using hcast

/-- Infinite leaf-fibre family: if `q = 3 mod 4` is prime and divides
positive `t`, then the `sm2LowerSquare` cell at upper kernel `t² + 1` is
empty. -/
theorem
    Sm2LowerSquareAllocation.upperKernel_ne_squarePlusOne_of_prime_dvd
    {t q : Nat} (ht : 0 < t) (hq : q.Prime)
    (hqMod : q % 4 = 3) (hqt : q ∣ t)
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.upperKernel ≠ squarePlusOneKernel t := by
  have hqThree : 3 ≤ q := by omega
  have hqLeT : q ≤ t := Nat.le_of_dvd ht hqt
  have htThree : 3 ≤ t := le_trans hqThree hqLeT
  have hK : 2 < squarePlusOneKernel t := by
    simp only [squarePlusOneKernel]
    nlinarith
  have htZero : (t : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff t q).mpr hqt
  apply allocation.upperKernel_ne_of_normOne_identity_mod_prime
    hK hq hqMod (pellSquarePlusOne t)
      (pellSquarePlusOne_isFundamental ht)
  · simp only [pellSquarePlusOne, Pell.Solution₁.x_mk]
    push_cast
    rw [htZero]
    ring
  · simp only [pellSquarePlusOne, Pell.Solution₁.y_mk]
    push_cast
    rw [htZero]
    ring

/-- The projected-shell control `K = 197 = 14² + 1` is nevertheless absent
from the `sm2LowerSquare` leaf, using `q = 7`. -/
theorem
    Sm2LowerSquareAllocation.upperKernel_ne_oneHundredNinetySeven
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.upperKernel ≠ 197 := by
  simpa [squarePlusOneKernel] using
    (allocation.upperKernel_ne_squarePlusOne_of_prime_dvd
      (t := 14) (q := 7) (by norm_num)
      (by norm_num) (by decide) (by norm_num))

end Erdos364
