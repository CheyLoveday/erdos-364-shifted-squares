import Erdos364.Foundations.ConsecutiveKernelConstraints
import Erdos364.Foundations.SquarefreeKernel

namespace Erdos364

/-- The three exact square-cube normal forms attached to the triple starting at `n`. -/
structure TripleNormalFormAt (n : Nat) where
  a0 : Nat
  b0 : Nat
  a1 : Nat
  b1 : Nat
  a2 : Nat
  b2 : Nat
  form0 : SquareCubeNormalForm n a0 b0
  form1 : SquareCubeNormalForm (n + 1) a1 b1
  form2 : SquareCubeNormalForm (n + 2) a2 b2

/-- Every positive powerful triple has an input-indexed triple normal form. -/
theorem PowerfulTripleAt.exists_tripleNormalFormAt {n : Nat}
    (htriple : PowerfulTripleAt n) :
    Nonempty (TripleNormalFormAt n) := by
  obtain ⟨a0, b0, h0⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos htriple.1
  obtain ⟨a1, b1, h1⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos htriple.2.1
  obtain ⟨a2, b2, h2⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos htriple.2.2
  exact
    ⟨{ a0 := a0
       b0 := b0
       a1 := a1
       b1 := b1
       a2 := a2
       b2 := b2
       form0 := h0
       form1 := h1
       form2 := h2 }⟩

/-- Exact forward reconstruction of all three represented values. -/
theorem TripleNormalFormAt.reconstruct {n : Nat}
    (s : TripleNormalFormAt n) :
    s.a0 ^ 2 * s.b0 ^ 3 = n ∧
      s.a1 ^ 2 * s.b1 ^ 3 = n + 1 ∧
        s.a2 ^ 2 * s.b2 ^ 3 = n + 2 := by
  exact
    ⟨s.form0.2.2.1.symm,
      s.form1.2.2.1.symm,
      s.form2.2.2.1.symm⟩

/-- Two states indexed by the same positive start agree in all six components. -/
theorem TripleNormalFormAt.components_eq {n : Nat}
    (hn : 0 < n)
    (s t : TripleNormalFormAt n) :
    s.a0 = t.a0 ∧ s.b0 = t.b0 ∧
      s.a1 = t.a1 ∧ s.b1 = t.b1 ∧
        s.a2 = t.a2 ∧ s.b2 = t.b2 := by
  have h0 := squareCubeNormalForm_pair_unique hn s.form0 t.form0
  have hn1 : 0 < n + 1 := Nat.succ_pos n
  have h1 := squareCubeNormalForm_pair_unique hn1 s.form1 t.form1
  have hn2 : 0 < n + 2 := by omega
  have h2 := squareCubeNormalForm_pair_unique hn2 s.form2 t.form2
  exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩

/-- The state kernels inherit the pairwise coprimality proved at F5b. -/
theorem TripleNormalFormAt.kernels_pairwise_coprime {n : Nat}
    (htriple : PowerfulTripleAt n)
    (s : TripleNormalFormAt n) :
    Nat.Coprime s.b0 s.b1 ∧
      Nat.Coprime s.b1 s.b2 ∧
        Nat.Coprime s.b0 s.b2 := by
  exact
    htriple.normalForm_kernels_pairwise_coprime
      s.form0 s.form1 s.form2

/-- The state kernels inherit the forced outer mod-four orientation proved at F5b. -/
theorem TripleNormalFormAt.outer_kernels_mod_four {n : Nat}
    (htriple : PowerfulTripleAt n)
    (s : TripleNormalFormAt n) :
    s.b0 % 4 = 3 ∧ s.b2 % 4 = 1 := by
  exact htriple.normalForm_outer_kernels_mod_four s.form0 s.form2

/-- In particular, the left kernel of a powerful triple is not one. -/
theorem TripleNormalFormAt.left_kernel_ne_one {n : Nat}
    (htriple : PowerfulTripleAt n)
    (s : TripleNormalFormAt n) :
    s.b0 ≠ 1 := by
  have hmod : s.b0 % 4 = 3 :=
    (TripleNormalFormAt.outer_kernels_mod_four htriple s).1
  intro hone
  omega

end Erdos364
