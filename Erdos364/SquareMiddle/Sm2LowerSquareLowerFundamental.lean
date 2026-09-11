import Erdos364.SquareMiddle.FixedPellFlankAllocation
import Erdos364.SquareMiddle.Sm2LowerSquareAllocation

namespace Erdos364

/-!
# The lower fundamental unit forced by the `sm2LowerSquare` leaf

The canonical lower Pell exponent is odd.  On this leaf the retained
same-centre identity is `X = y² + 1`, while the lower Pell kernel divides
`y² + 2 = X + 1`.  Consequently the real coordinate of the selected
fundamental norm-one unit is `-1` modulo the lower kernel.

Splitting the fundamental Pell equation across its two coprime odd flanks
then shows that this fundamental unit is half the square of a positive
norm-`-2` point.  This is a necessary lower-axis condition for the leaf, not
an exclusion of the leaf.
-/

/-- The selected lower fundamental real coordinate is `-1` modulo the
canonical lower Pell kernel. -/
theorem Sm2LowerSquareAllocation.lower_fundamentalX_mod_kernel
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    (fundamentalX data.pell.D data.pell.kernel : ZMod data.pell.D) = -1 := by
  let n :=
    canonicalPellIndex data.pell.D data.pell.kernel data.pell.k
  have hnOdd : Odd n := by
    dsimp [n, canonicalPellIndex]
    exact
      (pellRank_odd_of_kernel_odd data.pell.D data.pell.kernel
        data.admissible.1).mul (odd_two_mul_add_one data.pell.k)
  have hcenterMod :
      (data.center : ZMod data.pell.D) =
        (fundamentalX data.pell.D data.pell.kernel : ZMod data.pell.D) := by
    have hpell :=
      pellX_mod_kernel_eq_fundamentalX_of_odd
        data.pell.D data.pell.kernel hnOdd
    have hcenter := data.represents_center.2
    dsimp [n, canonicalPellCenter] at hcenter
    rw [hcenter]
    exact hpell
  have hyZero :
      (allocation.y : ZMod data.pell.D) ^ 2 + 2 = 0 := by
    have hform :=
      congrArg (fun z : Nat => (z : ZMod data.pell.D))
        allocation.linearUpperNormalForm.2.2.1
    push_cast at hform
    simpa using hform
  have hcenterCast :=
    congrArg (fun z : Nat => (z : ZMod data.pell.D))
      allocation.center_eq
  push_cast at hcenterCast
  have hcenterNeg : (data.center : ZMod data.pell.D) = -1 := by
    rw [hcenterCast]
    linear_combination hyZero
  rw [← hcenterMod]
  exact hcenterNeg

/-- Natural divisibility form of `lower_fundamentalX_mod_kernel`. -/
theorem Sm2LowerSquareAllocation.lower_kernel_dvd_fundamentalX_add_one
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    data.pell.D ∣
      fundamentalX data.pell.D data.pell.kernel + 1 := by
  apply
    (ZMod.natCast_eq_zero_iff
      (fundamentalX data.pell.D data.pell.kernel + 1)
      data.pell.D).mp
  push_cast
  rw [allocation.lower_fundamentalX_mod_kernel]
  ring

private theorem coprime_factors_of_square_local
    {A B C : Nat} (hcop : Nat.Coprime A B)
    (hprod : A * B = C ^ 2) :
    (∃ a : Nat, A = a ^ 2) ∧
      ∃ b : Nat, B = b ^ 2 := by
  constructor
  · apply exists_eq_pow_of_mul_eq_pow (a := A) (b := B) (c := C)
    · rw [gcd_eq_nat_gcd, hcop]
      exact isUnit_one
    · exact hprod
  · apply exists_eq_pow_of_mul_eq_pow (a := B) (b := A) (c := C)
    · rw [gcd_eq_nat_gcd, Nat.gcd_comm, hcop]
      exact isUnit_one
    · simpa [mul_comm] using hprod

/-- Every `sm2LowerSquare` allocation forces the selected lower fundamental
unit to be half the square of a positive norm-`-2` solution.

Concretely, if its coordinates are `a + b√D`, then there are positive
`r, s` with

`a = r² + 1`, `r² + 2 = D s²`, and `b = r s`.
-/
theorem Sm2LowerSquareAllocation.exists_lower_fundamental_normTwo
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    ∃ r s : Nat,
      0 < r ∧
        0 < s ∧
          fundamentalX data.pell.D data.pell.kernel = r ^ 2 + 1 ∧
            r ^ 2 + 2 = data.pell.D * s ^ 2 ∧
              fundamentalY data.pell.D data.pell.kernel = r * s := by
  let D := data.pell.D
  let hD := data.pell.kernel
  let a := fundamentalX D hD
  let b := fundamentalY D hD
  have haOne : 1 < a := fundamentalX_one_lt D hD
  have haEven : Even a := data.admissible.2
  have hPell := fundamental_pell_equation D hD
  change a ^ 2 - D * b ^ 2 = 1 at hPell
  have hPellEq : a ^ 2 = D * b ^ 2 + 1 := by
    omega
  have hFlank :
      (a - 1) * (a + 1) = D * b ^ 2 := by
    calc
      (a - 1) * (a + 1) = a ^ 2 - 1 :=
        (square_sub_one_eq_flank_mul
          (Nat.zero_lt_of_lt haOne)).symm
      _ = D * b ^ 2 := by omega
  obtain ⟨c, hc⟩ :=
    allocation.lower_kernel_dvd_fundamentalX_add_one
  change a + 1 = D * c at hc
  have hScaled :
      D * ((a - 1) * c) = D * b ^ 2 := by
    calc
      D * ((a - 1) * c) = (a - 1) * (D * c) := by ring
      _ = (a - 1) * (a + 1) := by rw [hc]
      _ = D * b ^ 2 := hFlank
  have hProduct : (a - 1) * c = b ^ 2 :=
    Nat.eq_of_mul_eq_mul_left
      (Nat.zero_lt_of_lt hD.1) hScaled
  have hcDvd : c ∣ a + 1 := by
    refine ⟨D, ?_⟩
    rw [hc]
    ring
  have hCoprime : Nat.Coprime (a - 1) c :=
    (fundamentalFlanks_coprime_of_even D hD haEven).of_dvd
      (dvd_refl (a - 1)) hcDvd
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ :=
    coprime_factors_of_square_local hCoprime hProduct
  have hrPos : 0 < r := by
    by_contra hrNot
    have hrZero : r = 0 := Nat.eq_zero_of_not_pos hrNot
    rw [hrZero] at hr
    simp at hr
    omega
  have hcPos : 0 < c := by
    by_contra hcNot
    have hcZero : c = 0 := Nat.eq_zero_of_not_pos hcNot
    rw [hcZero] at hc
    simp at hc
  have hsPos : 0 < s := by
    by_contra hsNot
    have hsZero : s = 0 := Nat.eq_zero_of_not_pos hsNot
    rw [hsZero] at hs
    simp at hs
    omega
  have haForm : a = r ^ 2 + 1 := by omega
  have hNormTwo : r ^ 2 + 2 = D * s ^ 2 := by
    rw [← hs, ← hc, haForm]
  have hbSquare : (r * s) ^ 2 = b ^ 2 := by
    calc
      (r * s) ^ 2 = (a - 1) * c := by rw [hr, hs]; ring
      _ = b ^ 2 := hProduct
  have hbForm : b = r * s := by
    exact
      (Nat.pow_left_injective
        (by norm_num : (2 : Nat) ≠ 0) hbSquare).symm
  exact
    ⟨r, s, hrPos, hsPos, haForm, hNormTwo, hbForm⟩

end Erdos364
