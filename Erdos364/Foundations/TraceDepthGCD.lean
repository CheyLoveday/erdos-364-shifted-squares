import Erdos364.Foundations.TraceDepth
import Erdos364.Foundations.TripleNormalForm

namespace Erdos364

/-- The common factor of the two adjacent trace radicands. -/
def TraceDepthTripleData.sharedRadicandGCD {n : Nat}
    (data : TraceDepthTripleData n) : Nat :=
  Nat.gcd data.left.Δ data.right.Δ

/-- The common factor of the two adjacent trace ordinates. -/
def TraceDepthTripleData.sharedOrdinateGCD {n : Nat}
    (data : TraceDepthTripleData n) : Nat :=
  Nat.gcd data.left.B data.right.B

/-- The square coordinate `a * b` of a square-cube normal form divides its
represented value. -/
private theorem normalForm_scale_dvd_value {m a b : Nat}
    (hform : SquareCubeNormalForm m a b) :
    a * b ∣ m := by
  refine ⟨a * b ^ 2, ?_⟩
  rw [hform.2.2.1]
  ring

/-- Compare an arbitrary trace-depth triple with the two adjacent packages
constructed from any normal-form state at the same source index. -/
theorem TraceDepthTripleData.components_eq_normalForms {n : Nat}
    (data : TraceDepthTripleData n)
    (state : TripleNormalFormAt n) :
    data.left.Δ = state.b0 * state.b1 ∧
      data.left.B =
        2 * (state.a0 * state.b0) * (state.a1 * state.b1) ∧
      data.right.Δ = state.b1 * state.b2 ∧
      data.right.B =
        2 * (state.a1 * state.b1) * (state.a2 * state.b2) := by
  have hform2 :
      SquareCubeNormalForm ((n + 1) + 1) state.a2 state.b2 := by
    simpa [Nat.add_assoc] using state.form2
  have hleft :=
    data.left.components_eq
      (adjacentTraceDepthData_of_normalForms state.form0 state.form1)
  have hright :=
    data.right.components_eq
      (adjacentTraceDepthData_of_normalForms state.form1 hform2)
  exact
    ⟨by
       simpa [adjacentTraceDepthData_of_normalForms] using hleft.1,
     by
       simpa [adjacentTraceDepthData_of_normalForms] using hleft.2,
     by
       simpa [adjacentTraceDepthData_of_normalForms] using hright.1,
     by
       simpa [adjacentTraceDepthData_of_normalForms] using hright.2⟩

/-- The common trace factors recover the middle kernel and twice the middle
square coordinate.  This uses the source-equivalent triple, not merely two
unrelated Pell-shaped equations. -/
theorem TraceDepthTripleData.sharedGCDs_eq_middleComponents {n : Nat}
    (data : TraceDepthTripleData n)
    (state : TripleNormalFormAt n) :
    data.sharedRadicandGCD = state.b1 ∧
      data.sharedOrdinateGCD = 2 * (state.a1 * state.b1) := by
  have htriple : PowerfulTripleAt n :=
    (powerfulTripleAt_iff_nonempty_traceDepthTripleData n).2 ⟨data⟩
  have hcomponents := data.components_eq_normalForms state
  have hkernels := state.kernels_pairwise_coprime htriple
  have houter_scales :
      Nat.Coprime (state.a0 * state.b0) (state.a2 * state.b2) :=
    Nat.Coprime.of_dvd
      (normalForm_scale_dvd_value state.form0)
      (normalForm_scale_dvd_value state.form2)
      htriple.pairwise_coprime.2.2
  constructor
  · unfold TraceDepthTripleData.sharedRadicandGCD
    rw [hcomponents.1, hcomponents.2.2.1]
    calc
      Nat.gcd (state.b0 * state.b1) (state.b1 * state.b2) =
          Nat.gcd (state.b1 * state.b0) (state.b1 * state.b2) := by
            rw [Nat.mul_comm state.b0 state.b1]
      _ = state.b1 * Nat.gcd state.b0 state.b2 :=
        Nat.gcd_mul_left state.b1 state.b0 state.b2
      _ = state.b1 := by
        rw [hkernels.2.2.gcd_eq_one, mul_one]
  · unfold TraceDepthTripleData.sharedOrdinateGCD
    rw [hcomponents.2.1, hcomponents.2.2.2]
    calc
      Nat.gcd
          (2 * (state.a0 * state.b0) * (state.a1 * state.b1))
          (2 * (state.a1 * state.b1) * (state.a2 * state.b2)) =
          Nat.gcd
            ((2 * (state.a1 * state.b1)) * (state.a0 * state.b0))
            ((2 * (state.a1 * state.b1)) * (state.a2 * state.b2)) := by
              congr 1
              all_goals ring
      _ =
          (2 * (state.a1 * state.b1)) *
            Nat.gcd (state.a0 * state.b0) (state.a2 * state.b2) :=
        Nat.gcd_mul_left
          (2 * (state.a1 * state.b1))
          (state.a0 * state.b0)
          (state.a2 * state.b2)
      _ = 2 * (state.a1 * state.b1) := by
        rw [houter_scales.gcd_eq_one, mul_one]

/-- Recover the three squarefree kernels and the three square coordinates
`aᵢ * bᵢ` from the two shared GCDs. -/
theorem TraceDepthTripleData.recover_kernelAndScaleCoordinates {n : Nat}
    (data : TraceDepthTripleData n)
    (state : TripleNormalFormAt n) :
    data.left.Δ / data.sharedRadicandGCD = state.b0 ∧
      data.sharedRadicandGCD = state.b1 ∧
      data.right.Δ / data.sharedRadicandGCD = state.b2 ∧
      data.left.B / data.sharedOrdinateGCD = state.a0 * state.b0 ∧
      data.sharedOrdinateGCD / 2 = state.a1 * state.b1 ∧
      data.right.B / data.sharedOrdinateGCD = state.a2 * state.b2 := by
  have hcomponents := data.components_eq_normalForms state
  have hgcds := data.sharedGCDs_eq_middleComponents state
  have hG_pos : 0 < 2 * (state.a1 * state.b1) := by
    exact
      Nat.mul_pos (by decide)
        (Nat.mul_pos state.form1.1 state.form1.2.1)
  refine ⟨?_, hgcds.1, ?_, ?_, ?_, ?_⟩
  · rw [hgcds.1, hcomponents.1]
    exact Nat.mul_div_left state.b0 state.form1.2.1
  · rw [hgcds.1, hcomponents.2.2.1]
    exact Nat.mul_div_right state.b2 state.form1.2.1
  · rw [hgcds.2, hcomponents.2.1]
    apply Nat.div_eq_of_eq_mul_right hG_pos
    ring
  · rw [hgcds.2]
    exact Nat.mul_div_right (state.a1 * state.b1) (by decide)
  · rw [hgcds.2, hcomponents.2.2.2]
    apply Nat.div_eq_of_eq_mul_right hG_pos
    ring

/-- Recover the three square factors after first recovering the kernels and
square coordinates. -/
theorem TraceDepthTripleData.recover_squareFactors {n : Nat}
    (data : TraceDepthTripleData n)
    (state : TripleNormalFormAt n) :
    (data.left.B / data.sharedOrdinateGCD) /
          (data.left.Δ / data.sharedRadicandGCD) = state.a0 ∧
      (data.sharedOrdinateGCD / 2) /
          data.sharedRadicandGCD = state.a1 ∧
      (data.right.B / data.sharedOrdinateGCD) /
          (data.right.Δ / data.sharedRadicandGCD) = state.a2 := by
  have hrecover := data.recover_kernelAndScaleCoordinates state
  rw [hrecover.1, hrecover.2.2.1, hrecover.2.2.2.1,
    hrecover.2.2.2.2.1, hrecover.2.2.2.2.2, hrecover.2.1]
  exact
    ⟨Nat.mul_div_left state.a0 state.form0.2.1,
      Nat.mul_div_left state.a1 state.form1.2.1,
      Nat.mul_div_left state.a2 state.form2.2.1⟩

/-- The shared ordinate GCD is even. -/
theorem TraceDepthTripleData.two_dvd_sharedOrdinateGCD {n : Nat}
    (data : TraceDepthTripleData n) :
    2 ∣ data.sharedOrdinateGCD := by
  have htriple : PowerfulTripleAt n :=
    (powerfulTripleAt_iff_nonempty_traceDepthTripleData n).2 ⟨data⟩
  obtain ⟨state⟩ := htriple.exists_tripleNormalFormAt
  have hG := (data.sharedGCDs_eq_middleComponents state).2
  exact ⟨state.a1 * state.b1, hG⟩

/-- The source depth conditions survive the shared-GCD compression in all
three reconstructed positions. -/
theorem TraceDepthTripleData.split_depth {n : Nat}
    (data : TraceDepthTripleData n) :
    data.left.Δ / data.sharedRadicandGCD ∣
        data.left.B / data.sharedOrdinateGCD ∧
      data.sharedRadicandGCD ∣ data.sharedOrdinateGCD / 2 ∧
      data.right.Δ / data.sharedRadicandGCD ∣
        data.right.B / data.sharedOrdinateGCD := by
  have htriple : PowerfulTripleAt n :=
    (powerfulTripleAt_iff_nonempty_traceDepthTripleData n).2 ⟨data⟩
  obtain ⟨state⟩ := htriple.exists_tripleNormalFormAt
  have hrecover := data.recover_kernelAndScaleCoordinates state
  rw [hrecover.1, hrecover.2.2.1, hrecover.2.2.2.1,
    hrecover.2.2.2.2.1, hrecover.2.2.2.2.2, hrecover.2.1]
  exact
    ⟨dvd_mul_left state.b0 state.a0,
      dvd_mul_left state.b1 state.a1,
      dvd_mul_left state.b2 state.a2⟩

/-- Exact large-GCD identity forced by the shared middle term. -/
theorem TraceDepthTripleData.shared_middle_identity {n : Nat}
    (data : TraceDepthTripleData n) :
    4 * (n + 1) =
      data.sharedRadicandGCD * data.sharedOrdinateGCD ^ 2 := by
  have htriple : PowerfulTripleAt n :=
    (powerfulTripleAt_iff_nonempty_traceDepthTripleData n).2 ⟨data⟩
  obtain ⟨state⟩ := htriple.exists_tripleNormalFormAt
  have hgcds := data.sharedGCDs_eq_middleComponents state
  rw [hgcds.1, hgcds.2, state.form1.2.2.1]
  ring

/-- The shared ordinate GCD cannot exceed the exact middle scale supplied by
the trace-depth compression. -/
theorem TraceDepthTripleData.sharedOrdinateGCD_sq_le_four_mul_middle {n : Nat}
    (data : TraceDepthTripleData n) :
    data.sharedOrdinateGCD ^ 2 ≤ 4 * (n + 1) := by
  rw [data.shared_middle_identity]
  exact Nat.le_mul_of_pos_left _
    (Nat.gcd_pos_of_pos_left _ data.left.Δ_pos)

/-- Trace depth forces the middle scale to be at most the cube of the shared
ordinate GCD.  The divisibility of the recovered middle kernel supplies the
extra factor of two. -/
theorem TraceDepthTripleData.eight_mul_middle_le_sharedOrdinateGCD_cube
    {n : Nat} (data : TraceDepthTripleData n) :
    8 * (n + 1) ≤ data.sharedOrdinateGCD ^ 3 := by
  have hGpos : 0 < data.sharedOrdinateGCD := by
    exact Nat.gcd_pos_of_pos_left _ data.left.B_pos
  have htwo : 2 ∣ data.sharedOrdinateGCD :=
    data.two_dvd_sharedOrdinateGCD
  have hhalfPos : 0 < data.sharedOrdinateGCD / 2 := by
    omega
  have hdiv :
      data.sharedRadicandGCD ∣ data.sharedOrdinateGCD / 2 :=
    (data.split_depth).2.1
  have hbound :
      data.sharedRadicandGCD ≤ data.sharedOrdinateGCD / 2 :=
    Nat.le_of_dvd hhalfPos hdiv
  have hdouble :
      2 * data.sharedRadicandGCD ≤ data.sharedOrdinateGCD := by
    calc
      2 * data.sharedRadicandGCD ≤
          2 * (data.sharedOrdinateGCD / 2) :=
        Nat.mul_le_mul_left 2 hbound
      _ = data.sharedOrdinateGCD := by
        rw [Nat.mul_comm, Nat.div_mul_cancel htwo]
  have hscale :
      (2 * data.sharedRadicandGCD) * data.sharedOrdinateGCD ^ 2 ≤
        data.sharedOrdinateGCD * data.sharedOrdinateGCD ^ 2 :=
    Nat.mul_le_mul_right _ hdouble
  calc
    8 * (n + 1) = 2 * (4 * (n + 1)) := by ring
    _ = 2 * (data.sharedRadicandGCD * data.sharedOrdinateGCD ^ 2) := by
      rw [data.shared_middle_identity]
    _ = (2 * data.sharedRadicandGCD) * data.sharedOrdinateGCD ^ 2 := by ring
    _ ≤ data.sharedOrdinateGCD * data.sharedOrdinateGCD ^ 2 := hscale
    _ = data.sharedOrdinateGCD ^ 3 := by ring

/-- The two source-derived trace radicands are distinct. -/
theorem TraceDepthTripleData.radicands_ne {n : Nat}
    (data : TraceDepthTripleData n) :
    data.left.Δ ≠ data.right.Δ := by
  have htriple : PowerfulTripleAt n :=
    (powerfulTripleAt_iff_nonempty_traceDepthTripleData n).2 ⟨data⟩
  obtain ⟨state⟩ := htriple.exists_tripleNormalFormAt
  have hcomponents := data.components_eq_normalForms state
  have horientation := state.outer_kernels_mod_four htriple
  intro heq
  have hproducts :
      state.b0 * state.b1 = state.b1 * state.b2 :=
    hcomponents.1.symm.trans (heq.trans hcomponents.2.2.1)
  have hproducts' :
      state.b1 * state.b0 = state.b1 * state.b2 := by
    simpa [Nat.mul_comm] using hproducts
  have hb_eq : state.b0 = state.b2 :=
    Nat.eq_of_mul_eq_mul_left state.form1.2.1 hproducts'
  rw [hb_eq] at horientation
  omega

end Erdos364
