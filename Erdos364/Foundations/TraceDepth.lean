import Erdos364.Foundations.ConsecutiveKernelConstraints
import Erdos364.Foundations.PowerfulFactorTransport
import Erdos364.Foundations.SquarefreeKernel

namespace Erdos364

/-- The exact trace-depth package attached to two adjacent naturals `r` and
`r + 1`.  Its Pell-shaped equation retains the shared trace `2 * r + 1`,
while `2 * Δ ∣ B` records the depth forced by square-cube normal forms. -/
structure AdjacentTraceDepthData (r : Nat) where
  Δ : Nat
  B : Nat
  Δ_pos : 0 < Δ
  Δ_squarefree : _root_.Squarefree Δ
  B_pos : 0 < B
  pell : (2 * r + 1) ^ 2 = 1 + Δ * B ^ 2
  depth : 2 * Δ ∣ B

/-- The two overlapping trace-depth packages attached to three consecutive
naturals.  The shared middle term is retained by the external indices. -/
structure TraceDepthTripleData (n : Nat) where
  left : AdjacentTraceDepthData n
  right : AdjacentTraceDepthData (n + 1)

/-- Two adjacent square-cube normal forms produce their exact trace-depth
package. -/
def adjacentTraceDepthData_of_normalForms
    {r a0 b0 a1 b1 : Nat}
    (h0 : SquareCubeNormalForm r a0 b0)
    (h1 : SquareCubeNormalForm (r + 1) a1 b1) :
    AdjacentTraceDepthData r := by
  have hcop : Nat.Coprime b0 b1 :=
    squareCubeNormalForm_kernels_coprime_of_values_coprime
      (consecutive_coprime r) h0 h1
  refine
    { Δ := b0 * b1
      B := 2 * (a0 * b0) * (a1 * b1)
      Δ_pos := Nat.mul_pos h0.2.1 h1.2.1
      Δ_squarefree := (Nat.squarefree_mul hcop).2
        ⟨h0.kernel_squarefree, h1.kernel_squarefree⟩
      B_pos :=
        Nat.mul_pos
          (Nat.mul_pos (by decide) (Nat.mul_pos h0.1 h0.2.1))
          (Nat.mul_pos h1.1 h1.2.1)
      pell := ?_
      depth := ?_ }
  · calc
      (2 * r + 1) ^ 2 = 1 + 4 * r * (r + 1) := by ring
      _ = 1 + (b0 * b1) * (2 * (a0 * b0) * (a1 * b1)) ^ 2 := by
        rw [h1.2.2.1, h0.2.2.1]
        ring
  · refine ⟨a0 * a1, ?_⟩
    ring

/-- Every powerful adjacent pair has a trace-depth package. -/
theorem adjacentTraceDepthData_of_powerful_pair {r : Nat}
    (hpair : PowerfulPos r ∧ PowerfulPos (r + 1)) :
    Nonempty (AdjacentTraceDepthData r) := by
  obtain ⟨a0, b0, h0⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos hpair.1
  obtain ⟨a1, b1, h1⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos hpair.2
  exact ⟨adjacentTraceDepthData_of_normalForms h0 h1⟩

/-- A trace-depth package reconstructs the square-cube normal form of the
adjacent product.  The quotient `c` is retained explicitly. -/
theorem AdjacentTraceDepthData.exists_productNormalForm {r : Nat}
    (data : AdjacentTraceDepthData r) :
    ∃ c : Nat,
      data.B = 2 * data.Δ * c ∧
        SquareCubeNormalForm (r * (r + 1)) c data.Δ := by
  obtain ⟨c, hB⟩ := data.depth
  have hc : 0 < c := by
    by_contra hc
    have hc_zero : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    have hB_zero : data.B = 0 := by simpa using hB
    exact (Nat.ne_of_gt data.B_pos) hB_zero
  have hproduct : r * (r + 1) = c ^ 2 * data.Δ ^ 3 := by
    have htrace :
        4 * (r * (r + 1)) = data.Δ * data.B ^ 2 := by
      nlinarith [data.pell]
    have hscaled :
        4 * (r * (r + 1)) = 4 * (c ^ 2 * data.Δ ^ 3) := by
      calc
        4 * (r * (r + 1)) = data.Δ * data.B ^ 2 := htrace
        _ = 4 * (c ^ 2 * data.Δ ^ 3) := by
          rw [hB]
          ring
    exact Nat.eq_of_mul_eq_mul_left (by decide) hscaled
  exact
    ⟨c, hB,
      squareCubeNormalForm_of_eq_sq_mul_cube
        hc data.Δ_pos hproduct data.Δ_squarefree⟩

/-- Trace depth is sufficient to recover powerfulness of both adjacent
factors. -/
theorem AdjacentTraceDepthData.powerful_pair {r : Nat}
    (data : AdjacentTraceDepthData r) :
    PowerfulPos r ∧ PowerfulPos (r + 1) := by
  obtain ⟨c, _, hform⟩ := data.exists_productNormalForm
  exact
    powerfulPos_factors_of_coprime_mul
      (consecutive_coprime r)
      (powerfulPos_of_squareCubeNormalForm hform)

/-- Exact equivalence between a positive powerful adjacent pair and
nonempty trace-depth data at the same left endpoint. -/
theorem powerfulPos_pair_iff_nonempty_adjacentTraceDepthData (r : Nat) :
    (PowerfulPos r ∧ PowerfulPos (r + 1)) ↔
      Nonempty (AdjacentTraceDepthData r) := by
  constructor
  · exact adjacentTraceDepthData_of_powerful_pair
  · rintro ⟨data⟩
    exact data.powerful_pair

/-- The trace-depth components at a fixed adjacent pair are unique. -/
theorem AdjacentTraceDepthData.components_eq {r : Nat}
    (data₁ data₂ : AdjacentTraceDepthData r) :
    data₁.Δ = data₂.Δ ∧ data₁.B = data₂.B := by
  obtain ⟨c₁, hB₁, hform₁⟩ := data₁.exists_productNormalForm
  obtain ⟨c₂, hB₂, hform₂⟩ := data₂.exists_productNormalForm
  have hproduct_pos : 0 < r * (r + 1) :=
    (powerfulPos_of_squareCubeNormalForm hform₁).1
  have hcomponents :=
    squareCubeNormalForm_pair_unique hproduct_pos hform₁ hform₂
  constructor
  · exact hcomponents.2
  · rw [hB₁, hB₂, hcomponents.1, hcomponents.2]

/-- Exact equivalence between a positive powerful consecutive triple and
the two overlapping trace-depth packages at the same start. -/
theorem powerfulTripleAt_iff_nonempty_traceDepthTripleData (n : Nat) :
    PowerfulTripleAt n ↔ Nonempty (TraceDepthTripleData n) := by
  constructor
  · intro htriple
    have hleft :
        Nonempty (AdjacentTraceDepthData n) :=
      adjacentTraceDepthData_of_powerful_pair ⟨htriple.1, htriple.2.1⟩
    have hright :
        Nonempty (AdjacentTraceDepthData (n + 1)) :=
      adjacentTraceDepthData_of_powerful_pair
        ⟨htriple.2.1, by simpa [Nat.add_assoc] using htriple.2.2⟩
    obtain ⟨left⟩ := hleft
    obtain ⟨right⟩ := hright
    exact ⟨{ left := left, right := right }⟩
  · rintro ⟨data⟩
    have hleft := data.left.powerful_pair
    have hright := data.right.powerful_pair
    exact
      ⟨hleft.1, hleft.2,
        by simpa [Nat.add_assoc] using hright.2⟩

/-- Both overlapping trace-depth packages of a fixed triple have unique
components. -/
theorem TraceDepthTripleData.components_eq {n : Nat}
    (data₁ data₂ : TraceDepthTripleData n) :
    data₁.left.Δ = data₂.left.Δ ∧
      data₁.left.B = data₂.left.B ∧
        data₁.right.Δ = data₂.right.Δ ∧
          data₁.right.B = data₂.right.B := by
  have hleft := data₁.left.components_eq data₂.left
  have hright := data₁.right.components_eq data₂.right
  exact ⟨hleft.1, hleft.2, hright.1, hright.2⟩

end Erdos364
