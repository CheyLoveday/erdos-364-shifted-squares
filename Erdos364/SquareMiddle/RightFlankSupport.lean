import Erdos364.Foundations.ConsecutiveKernelConstraints
import Erdos364.SquareMiddle.NormalForm
import Erdos364.SquareMiddle.SourceArithmetic

namespace Erdos364

/-!
# Elementary right-flank support

This file records the source-independent arithmetic shared by every proposed
right-flank eliminator.  Its hypotheses are deliberately raw normal forms for
the two values `X² - 1` and `X² + 1`; no canonical counterexample record is
required.

The two-kernel equation is stated additively over `Nat`.  This avoids hiding a
truncated-subtraction side condition in the displayed difference-of-values
identity.
-/

/-- For a nontrivial even centre, the values at distance two around `X²` are
coprime.  The lower value is odd, so the only possible common divisor of the
two values is excluded. -/
theorem squareSubOne_squareAddOne_coprime_of_even {X : Nat}
    (hX : 1 < X) (hEven : Even X) :
    Nat.Coprime (X ^ 2 - 1) (X ^ 2 + 1) := by
  have hsquare_even : Even (X ^ 2) :=
    Nat.even_pow.mpr ⟨hEven, by decide⟩
  have hleft_odd : Odd (X ^ 2 - 1) :=
    Nat.Even.sub_odd (by nlinarith : 1 ≤ X ^ 2) hsquare_even odd_one
  have hcop_two : Nat.Coprime (X ^ 2 - 1) 2 :=
    Nat.coprime_two_right.mpr hleft_odd
  have hright : X ^ 2 + 1 = 2 + (X ^ 2 - 1) := by
    simpa [Nat.add_comm] using (square_sub_one_add_two hX).symm
  rw [hright, Nat.coprime_add_self_right]
  exact hcop_two

/-- The product of the square part and cube kernel divides the value
represented by a square-cube normal form. -/
theorem SquareCubeNormalForm.squareFactor_mul_kernel_dvd_value
    {N A D : Nat} (hform : SquareCubeNormalForm N A D) :
    A * D ∣ N := by
  rw [hform.2.2.1]
  refine ⟨A * D ^ 2, ?_⟩
  ring

/-- All lower support is coprime to all upper support.  This is stronger than
kernel coprimality: it also rules out either kernel meeting the opposite
square part and rules out a common prime in the two square parts. -/
theorem squareCubeNormalForm_supports_coprime_of_even_center
    {X U D V K : Nat} (hX : 1 < X) (hEven : Even X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    Nat.Coprime (D * U) (K * V) := by
  have hvalues := squareSubOne_squareAddOne_coprime_of_even hX hEven
  apply hvalues.of_dvd
  · simpa [mul_comm] using hlower.squareFactor_mul_kernel_dvd_value
  · simpa [mul_comm] using hupper.squareFactor_mul_kernel_dvd_value

/-- In particular, the lower and upper squarefree cube kernels are coprime. -/
theorem squareCubeNormalForm_kernels_coprime_of_even_center
    {X U D V K : Nat} (hX : 1 < X) (hEven : Even X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    Nat.Coprime D K := by
  exact
    (squareCubeNormalForm_supports_coprime_of_even_center
      hX hEven hlower hupper).of_dvd
      (dvd_mul_right D U) (dvd_mul_right K V)

/-- The upper cube kernel cannot be `1`: otherwise `X² + 1` would be a
square strictly between the consecutive squares `X²` and `(X+1)²`. -/
theorem squareCubeNormalForm_kernel_ne_one_of_square_add_one
    {X V K : Nat} (hX : 1 < X)
    (hform : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    K ≠ 1 := by
  intro hK
  subst K
  have hvalue : X ^ 2 + 1 = V ^ 2 := by
    simpa using hform.2.2.1
  have hX_lt_V : X < V := by
    apply (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).lt_iff_lt.mp
    omega
  have hsucc_le : X + 1 ≤ V := by omega
  have hsquare_le : (X + 1) ^ 2 ≤ V ^ 2 :=
    Nat.pow_le_pow_left hsucc_le 2
  nlinarith

/-- Positivity of a normal-form kernel upgrades the preceding exclusion to
the strict lower bound used by counterexample records. -/
theorem squareCubeNormalForm_kernel_one_lt_of_square_add_one
    {X V K : Nat} (hX : 1 < X)
    (hform : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    1 < K := by
  have hK_pos := hform.2.1
  have hK_ne := squareCubeNormalForm_kernel_ne_one_of_square_add_one hX hform
  omega

/-- The two normal forms imply the exact simultaneous two-kernel equation.
The additive statement is the subtraction-safe `Nat` form of
`K³V² - D³U² = 2`. -/
theorem squareCubeNormalForms_twoKernel_additive
    {X U D V K : Nat} (hX : 1 < X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    K ^ 3 * V ^ 2 = D ^ 3 * U ^ 2 + 2 := by
  calc
    K ^ 3 * V ^ 2 = V ^ 2 * K ^ 3 := by ring
    _ = X ^ 2 + 1 := hupper.2.2.1.symm
    _ = (X ^ 2 - 1) + 2 := (square_sub_one_add_two hX).symm
    _ = U ^ 2 * D ^ 3 + 2 := by rw [hlower.2.2.1]
    _ = D ^ 3 * U ^ 2 + 2 := by ring

/-- The familiar difference form follows once the additive identity has made
the subtraction side condition explicit. -/
theorem squareCubeNormalForms_twoKernel_sub
    {X U D V K : Nat} (hX : 1 < X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    K ^ 3 * V ^ 2 - D ^ 3 * U ^ 2 = 2 := by
  rw [squareCubeNormalForms_twoKernel_additive hX hlower hupper]
  omega

end Erdos364
