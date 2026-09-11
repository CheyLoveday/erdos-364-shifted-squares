import Erdos364.Foundations.ConsecutiveKernelConstraints
import Erdos364.SquareMiddle.SourceArithmetic

namespace Erdos364

/-!
# Square-middle flank normal forms

This module records the normal forms of the two linear flanks `X - 1` and
`X + 1` of a square-middle source.  It proves only their direct arithmetic
relations: uniqueness, coprimality, reconstruction of the lower normal form,
and the mod-eight residue table.  It deliberately does not identify either
flank kernel with a fundamental-unit formula.
-/

/-- The unique `A²D³` normal forms of the two linear flanks, packaged at a
fixed centre. -/
structure SquareMiddleFlankNormalForms (X : Nat) where
  lowerSquare : Nat
  lowerKernel : Nat
  upperSquare : Nat
  upperKernel : Nat
  lowerForm : SquareCubeNormalForm (X - 1) lowerSquare lowerKernel
  upperForm : SquareCubeNormalForm (X + 1) upperSquare upperKernel

/-- Every square-middle source has normal forms for both linear flanks. -/
theorem SquareMiddle.exists_flankNormalForms {X : Nat} (h : SquareMiddle X) :
    Nonempty (SquareMiddleFlankNormalForms X) := by
  obtain ⟨hminus, hplus⟩ := h.flanks_powerful
  obtain ⟨aMinus, dMinus, hMinus⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos hminus
  obtain ⟨aPlus, dPlus, hPlus⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos hplus
  exact
    ⟨{ lowerSquare := aMinus
       lowerKernel := dMinus
       upperSquare := aPlus
       upperKernel := dPlus
       lowerForm := hMinus
       upperForm := hPlus }⟩

/-- The two flank normal forms are componentwise unique at a nontrivial
centre, so the fields of `SquareMiddleFlankNormalForms` are canonical data. -/
theorem SquareMiddleFlankNormalForms.components_eq {X : Nat} (hX : 1 < X)
    (s t : SquareMiddleFlankNormalForms X) :
    s.lowerSquare = t.lowerSquare ∧ s.lowerKernel = t.lowerKernel ∧
      s.upperSquare = t.upperSquare ∧ s.upperKernel = t.upperKernel := by
  have hminusPos : 0 < X - 1 := by omega
  have hplusPos : 0 < X + 1 := by omega
  have hminus := squareCubeNormalForm_pair_unique hminusPos s.lowerForm t.lowerForm
  have hplus := squareCubeNormalForm_pair_unique hplusPos s.upperForm t.upperForm
  exact ⟨hminus.1, hminus.2, hplus.1, hplus.2⟩

/-- The two flank kernels are coprime because the two linear flanks are
coprime at a square-middle source. -/
theorem SquareMiddleFlankNormalForms.kernels_coprime {X : Nat}
    (h : SquareMiddle X) (w : SquareMiddleFlankNormalForms X) :
    Nat.Coprime w.lowerKernel w.upperKernel := by
  exact squareCubeNormalForm_kernels_coprime_of_values_coprime
    h.flanks_coprime w.lowerForm w.upperForm

/-- Multiplying the two flank normal forms reconstructs a normal form of
`X² - 1`. -/
theorem SquareMiddleFlankNormalForms.product_normalForm {X : Nat}
    (h : SquareMiddle X) (w : SquareMiddleFlankNormalForms X) :
    SquareCubeNormalForm (X ^ 2 - 1)
      (w.lowerSquare * w.upperSquare)
      (w.lowerKernel * w.upperKernel) := by
  have hXgt : 1 < X := h.1
  apply squareCubeNormalForm_of_eq_sq_mul_cube
  · exact Nat.mul_pos w.lowerForm.1 w.upperForm.1
  · exact Nat.mul_pos w.lowerForm.2.1 w.upperForm.2.1
  · calc
      X ^ 2 - 1 = (X - 1) * (X + 1) :=
        square_sub_one_eq_flank_mul (by omega : 0 < X)
      _ = (w.lowerSquare ^ 2 * w.lowerKernel ^ 3) *
          (w.upperSquare ^ 2 * w.upperKernel ^ 3) := by
          rw [w.lowerForm.2.2.1, w.upperForm.2.2.1]
      _ = (w.lowerSquare * w.upperSquare) ^ 2 *
          (w.lowerKernel * w.upperKernel) ^ 3 := by ring
  · exact (Nat.squarefree_mul (w.kernels_coprime h)).mpr
      ⟨w.lowerForm.kernel_squarefree, w.upperForm.kernel_squarefree⟩

/-- The product of the two flank kernels equals the canonical normal-form
kernel of `X² - 1`.  The theorem is stated against an arbitrary normal-form
witness because uniqueness makes that kernel independent of the witness. -/
theorem SquareMiddleFlankNormalForms.kernel_product_eq {X a D : Nat}
    (h : SquareMiddle X) (w : SquareMiddleFlankNormalForms X)
    (hsource : SquareCubeNormalForm (X ^ 2 - 1) a D) :
    w.lowerKernel * w.upperKernel = D := by
  have hXgt : 1 < X := h.1
  apply squareCubeNormalForm_kernel_unique
    (n := X ^ 2 - 1)
    (a := w.lowerSquare * w.upperSquare)
    (b := w.lowerKernel * w.upperKernel)
    (c := a)
    (d := D)
  · have hXtwo : 2 ≤ X := by omega
    have hsquare : 2 ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hXtwo 2
    norm_num at hsquare
    omega
  · exact w.product_normalForm h
  · exact hsource

private theorem odd_mod_eight_cases {n : Nat} (hn : Odd n) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  have hmod : n % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)]
    exact hn2
  omega

private theorem odd_square_mod_eight {n : Nat} (hn : Odd n) : n ^ 2 % 8 = 1 := by
  rcases odd_mod_eight_cases hn with h | h | h | h <;>
    simp [Nat.pow_mod, h]

private theorem odd_cube_mod_eight {n : Nat} (hn : Odd n) :
    n ^ 3 % 8 = n % 8 := by
  rcases odd_mod_eight_cases hn with h | h | h | h <;>
    simp [Nat.pow_mod, h]

/-- An odd square-cube value has a cube kernel in the same residue class
modulo eight. -/
private theorem squareCubeNormalForm_kernel_mod_eight_of_odd_value
    {n a b : Nat} (hform : SquareCubeNormalForm n a b) (hn : Odd n) :
    b % 8 = n % 8 := by
  have hvalue : Odd (a ^ 2 * b ^ 3) := by
    rw [← hform.2.2.1]
    exact hn
  have haPow : Odd (a ^ 2) := (Nat.odd_mul.mp hvalue).1
  have hbPow : Odd (b ^ 3) := (Nat.odd_mul.mp hvalue).2
  have ha : Odd a :=
    (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp haPow
  have hb : Odd b :=
    (Nat.odd_pow_iff (by decide : 3 ≠ 0)).mp hbPow
  rw [hform.2.2.1, Nat.mul_mod, odd_square_mod_eight ha,
    odd_cube_mod_eight hb]
  omega

private theorem flank_mod_eight_table {X : Nat} (hX : 1 < X) :
    (X % 8 = 0 → (X - 1) % 8 = 7 ∧ (X + 1) % 8 = 1) ∧
    (X % 8 = 2 → (X - 1) % 8 = 1 ∧ (X + 1) % 8 = 3) ∧
    (X % 8 = 4 → (X - 1) % 8 = 3 ∧ (X + 1) % 8 = 5) ∧
    (X % 8 = 6 → (X - 1) % 8 = 5 ∧ (X + 1) % 8 = 7) := by
  constructor
  · intro hmod
    have hdecomp : X % 8 + 8 * (X / 8) = X := Nat.mod_add_div X 8
    rw [hmod] at hdecomp
    omega
  constructor
  · intro hmod
    have hdecomp : X % 8 + 8 * (X / 8) = X := Nat.mod_add_div X 8
    rw [hmod] at hdecomp
    omega
  constructor
  · intro hmod
    have hdecomp : X % 8 + 8 * (X / 8) = X := Nat.mod_add_div X 8
    rw [hmod] at hdecomp
    omega
  · intro hmod
    have hdecomp : X % 8 + 8 * (X / 8) = X := Nat.mod_add_div X 8
    rw [hmod] at hdecomp
    omega

private theorem even_mod_eight_cases {X : Nat} (hX : Even X) :
    X % 8 = 0 ∨ X % 8 = 2 ∨ X % 8 = 4 ∨ X % 8 = 6 := by
  have hmod2 : X % 8 % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd X (by decide : 2 ∣ 8)]
    exact Nat.even_iff.mp hX
  have hlt : X % 8 < 8 := Nat.mod_lt X (by decide)
  omega

/-- Exact mod-eight kernel allocation for the six proposed square-middle
leaves.  This is a residue table only; it does not assign a source to a leaf. -/
theorem SquareMiddleFlankNormalForms.kernel_mod_eight_table {X : Nat}
    (h : SquareMiddle X) (w : SquareMiddleFlankNormalForms X) :
    (X % 8 = 0 ∧ w.lowerKernel % 8 = 7 ∧ w.upperKernel % 8 = 1) ∨
      (X % 8 = 2 ∧ w.lowerKernel % 8 = 1 ∧ w.upperKernel % 8 = 3) ∨
      (X % 8 = 4 ∧ w.lowerKernel % 8 = 3 ∧ w.upperKernel % 8 = 5) ∨
      (X % 8 = 6 ∧ w.lowerKernel % 8 = 5 ∧ w.upperKernel % 8 = 7) := by
  have hXgt : 1 < X := h.1
  have hXeven : Even X := h.center_even
  have hminusOdd : Odd (X - 1) :=
    Nat.Even.sub_odd (by omega : 1 ≤ X) hXeven odd_one
  have hplusOdd : Odd (X + 1) := hXeven.add_odd odd_one
  have hminusKernel : w.lowerKernel % 8 = (X - 1) % 8 :=
    squareCubeNormalForm_kernel_mod_eight_of_odd_value w.lowerForm hminusOdd
  have hplusKernel : w.upperKernel % 8 = (X + 1) % 8 :=
    squareCubeNormalForm_kernel_mod_eight_of_odd_value w.upperForm hplusOdd
  have hresidues := flank_mod_eight_table hXgt
  rcases even_mod_eight_cases hXeven with h0 | h2 | h4 | h6
  · exact Or.inl ⟨h0, hminusKernel.trans (hresidues.1 h0).1,
      hplusKernel.trans (hresidues.1 h0).2⟩
  · exact Or.inr (Or.inl ⟨h2, hminusKernel.trans (hresidues.2.1 h2).1,
      hplusKernel.trans (hresidues.2.1 h2).2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h4,
      hminusKernel.trans (hresidues.2.2.1 h4).1,
      hplusKernel.trans (hresidues.2.2.1 h4).2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h6,
      hminusKernel.trans (hresidues.2.2.2 h6).1,
      hplusKernel.trans (hresidues.2.2.2 h6).2⟩))

end Erdos364
