import Erdos364.SquareMiddle.PellDivisibilityRank

namespace Erdos364

private theorem even_add_even_nat {m n : Nat}
    (hm : Even m) (hn : Even n) : Even (m + n) := by
  rw [Nat.even_add]
  exact iff_of_true hm hn

/-- Addition-form natural Pell equation for the selected fundamental
coordinates. This avoids reasoning through natural subtraction. -/
theorem fundamental_pell_equation_add (D : Nat) (hD : PellKernel D) :
    fundamentalX D hD ^ 2 =
      1 + D * fundamentalY D hD ^ 2 := by
  have h := (fundamentalPell D hD).prop_x
  rw [← fundamentalX_intCast D hD, ← fundamentalY_intCast D hD] at h
  exact_mod_cast h

/-- For odd `D`, the two fundamental Pell coefficients have opposite parity:
the x-coordinate is even exactly when the y-coordinate is odd. -/
theorem fundamentalX_even_iff_fundamentalY_odd
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) :
    Even (fundamentalX D hD) ↔ Odd (fundamentalY D hD) := by
  let A := fundamentalX D hD
  let B := fundamentalY D hD
  have hequation : A ^ 2 = 1 + D * B ^ 2 := by
    simpa [A, B] using fundamental_pell_equation_add D hD
  constructor
  · intro hA_even
    rw [← Nat.not_even_iff_odd]
    intro hB_even
    have hleft_even : Even (A ^ 2) :=
      Nat.even_pow.mpr ⟨hA_even, by decide⟩
    have hB_square_even : Even (B ^ 2) :=
      Nat.even_pow.mpr ⟨hB_even, by decide⟩
    have hproduct_even : Even (D * B ^ 2) :=
      hB_square_even.mul_left D
    have hright_odd : Odd (1 + D * B ^ 2) :=
      odd_one.add_even hproduct_even
    have hleft_odd : Odd (A ^ 2) := by
      rw [hequation]
      exact hright_odd
    exact hleft_odd.not_two_dvd_nat hleft_even.two_dvd
  · intro hB_odd
    have hB_square_odd : Odd (B ^ 2) := hB_odd.pow
    have hproduct_odd : Odd (D * B ^ 2) :=
      hD_odd.mul hB_square_odd
    have hright_even : Even (1 + D * B ^ 2) :=
      odd_one.add_odd hproduct_odd
    have hleft_even : Even (A ^ 2) := by
      rw [hequation]
      exact hright_even
    exact (Nat.even_pow.mp hleft_even).1

/-- Equivalent complementary form of the fundamental-coefficient parity law. -/
theorem fundamentalX_odd_iff_fundamentalY_even
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) :
    Odd (fundamentalX D hD) ↔ Even (fundamentalY D hD) := by
  constructor
  · intro hX_odd
    rw [← Nat.not_odd_iff_even]
    intro hY_odd
    exact hX_odd.not_two_dvd_nat
      (fundamentalX_even_iff_fundamentalY_odd D hD hD_odd |>.mpr hY_odd).two_dvd
  · intro hY_even
    rw [← Nat.not_even_iff_odd]
    intro hX_even
    exact
      (fundamentalX_even_iff_fundamentalY_odd D hD hD_odd |>.mp hX_even).not_two_dvd_nat
        hY_even.two_dvd

/-- Natural x-coordinate recurrence for canonical powers. -/
theorem pellX_succ (D : Nat) (hD : PellKernel D) (n : Nat) :
    pellX D hD (n + 1) =
      fundamentalX D hD * pellX D hD n +
        D * fundamentalY D hD * pellY D hD n := by
  have hInt :
      (pellSolution D hD (n + 1)).x =
        (fundamentalX D hD : Int) * (pellX D hD n : Int) +
          (D : Int) * (fundamentalY D hD : Int) * (pellY D hD n : Int) := by
    simp only [pellSolution, pow_succ, Pell.Solution₁.x_mul]
    rw [fundamentalX_intCast D hD, fundamentalY_intCast D hD,
      pellX_intCast D hD n, pellY_intCast D hD n]
    simp only [pellSolution]
    ring
  rw [← pellX_intCast D hD (n + 1)] at hInt
  exact_mod_cast hInt

/-- Natural y-coordinate recurrence for canonical powers. -/
theorem pellY_succ (D : Nat) (hD : PellKernel D) (n : Nat) :
    pellY D hD (n + 1) =
      fundamentalY D hD * pellX D hD n +
        fundamentalX D hD * pellY D hD n := by
  have hInt :
      (pellSolution D hD (n + 1)).y =
        (fundamentalY D hD : Int) * (pellX D hD n : Int) +
          (fundamentalX D hD : Int) * (pellY D hD n : Int) := by
    simp only [pellSolution, pow_succ, Pell.Solution₁.y_mul]
    rw [fundamentalX_intCast D hD, fundamentalY_intCast D hD,
      pellX_intCast D hD n, pellY_intCast D hD n]
    simp only [pellSolution]
    ring
  rw [← pellY_intCast D hD (n + 1)] at hInt
  exact_mod_cast hInt

/-- Simultaneous parity state when the fundamental x-coordinate is even. The
state alternates between `(x odd, y even)` and `(x even, y odd)`. -/
private theorem pellXY_parity_state_of_fundamentalX_even
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D)
    (hfund_even : Even (fundamentalX D hD)) :
    ∀ n : Nat,
      (Even n → Odd (pellX D hD n) ∧ Even (pellY D hD n)) ∧
        (Odd n → Even (pellX D hD n) ∧ Odd (pellY D hD n)) := by
  have hfundY_odd : Odd (fundamentalY D hD) :=
    (fundamentalX_even_iff_fundamentalY_odd D hD hD_odd).mp hfund_even
  intro n
  induction n with
  | zero =>
      constructor
      · intro _hzero_even
        rw [pellX_zero, pellY_zero]
        exact ⟨odd_one, Even.zero⟩
      · intro hzero_odd
        exact (Nat.not_odd_zero hzero_odd).elim
  | succ n ih =>
      rcases Nat.even_or_odd n with hn_even | hn_odd
      · have hn_state := ih.1 hn_even
        constructor
        · intro hsucc_even
          have hsucc_odd : Odd (n + 1) := hn_even.add_one
          exact (hsucc_odd.not_two_dvd_nat hsucc_even.two_dvd).elim
        · intro _hsucc_odd
          rw [pellX_succ, pellY_succ]
          have hAX_even :
              Even (fundamentalX D hD * pellX D hD n) :=
            hfund_even.mul_right _
          have hDBY_even :
              Even (D * fundamentalY D hD * pellY D hD n) :=
            hn_state.2.mul_left _
          have hBX_odd :
              Odd (fundamentalY D hD * pellX D hD n) :=
            hfundY_odd.mul hn_state.1
          have hAY_even :
              Even (fundamentalX D hD * pellY D hD n) :=
            hfund_even.mul_right _
          exact
            ⟨even_add_even_nat hAX_even hDBY_even,
              hBX_odd.add_even hAY_even⟩
      · have hn_state := ih.2 hn_odd
        constructor
        · intro _hsucc_even
          rw [pellX_succ, pellY_succ]
          have hAX_even :
              Even (fundamentalX D hD * pellX D hD n) :=
            hfund_even.mul_right _
          have hDBY_odd :
              Odd (D * fundamentalY D hD * pellY D hD n) :=
            (hD_odd.mul hfundY_odd).mul hn_state.2
          have hBX_even :
              Even (fundamentalY D hD * pellX D hD n) :=
            hn_state.1.mul_left _
          have hAY_even :
              Even (fundamentalX D hD * pellY D hD n) :=
            hfund_even.mul_right _
          exact
            ⟨hAX_even.add_odd hDBY_odd,
              even_add_even_nat hBX_even hAY_even⟩
        · intro hsucc_odd
          have hsucc_even : Even (n + 1) := hn_odd.add_one
          exact (hsucc_odd.not_two_dvd_nat hsucc_even.two_dvd).elim

/-- If the fundamental x-coordinate is odd, every canonical x-coordinate is
odd and every canonical y-coordinate is even. -/
private theorem pellXY_parity_state_of_fundamentalX_odd
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D)
    (hfund_odd : Odd (fundamentalX D hD)) :
    ∀ n : Nat, Odd (pellX D hD n) ∧ Even (pellY D hD n) := by
  have hfundY_even : Even (fundamentalY D hD) :=
    (fundamentalX_odd_iff_fundamentalY_even D hD hD_odd).mp hfund_odd
  intro n
  induction n with
  | zero =>
      rw [pellX_zero, pellY_zero]
      exact ⟨odd_one, Even.zero⟩
  | succ n ih =>
      rw [pellX_succ, pellY_succ]
      have hAX_odd :
          Odd (fundamentalX D hD * pellX D hD n) :=
        hfund_odd.mul ih.1
      have hDBY_even :
          Even (D * fundamentalY D hD * pellY D hD n) :=
        hfundY_even.mul_left D |>.mul_right _
      have hBX_even :
          Even (fundamentalY D hD * pellX D hD n) :=
        hfundY_even.mul_right _
      have hAY_even :
          Even (fundamentalX D hD * pellY D hD n) :=
        ih.2.mul_left _
      exact
        ⟨hAX_odd.add_even hDBY_even,
          even_add_even_nat hBX_even hAY_even⟩

/-- Exact canonical-powers parity law for odd Pell kernels. An x-coordinate is
even exactly when the fundamental x-coordinate is even and the exponent is
odd. -/
theorem pellX_even_iff_fundamentalX_even_and_index_odd
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) (n : Nat) :
    Even (pellX D hD n) ↔
      Even (fundamentalX D hD) ∧ Odd n := by
  by_cases hfund_even : Even (fundamentalX D hD)
  · have hstate :=
      pellXY_parity_state_of_fundamentalX_even
        D hD hD_odd hfund_even n
    constructor
    · intro hx_even
      refine ⟨hfund_even, ?_⟩
      rcases Nat.even_or_odd n with hn_even | hn_odd
      · have hx_odd := (hstate.1 hn_even).1
        exact (hx_odd.not_two_dvd_nat hx_even.two_dvd).elim
      · exact hn_odd
    · rintro ⟨_hfund, hn_odd⟩
      exact (hstate.2 hn_odd).1
  · have hfund_odd : Odd (fundamentalX D hD) :=
      Nat.not_even_iff_odd.mp hfund_even
    have hx_odd :=
      (pellXY_parity_state_of_fundamentalX_odd
        D hD hD_odd hfund_odd n).1
    constructor
    · intro hx_even
      exact (hx_odd.not_two_dvd_nat hx_even.two_dvd).elim
    · rintro ⟨hcontra, _hn_odd⟩
      exact (hfund_even hcontra).elim

/-- An even canonical x-coordinate forces an odd exponent. -/
theorem index_odd_of_pellX_even
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) {n : Nat}
    (hx_even : Even (pellX D hD n)) :
    Odd n :=
  (pellX_even_iff_fundamentalX_even_and_index_odd D hD hD_odd n).mp hx_even |>.2

/-- An even canonical x-coordinate also forces the selected fundamental
x-coordinate to be even. -/
theorem fundamentalX_even_of_pellX_even
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) {n : Nat}
    (hx_even : Even (pellX D hD n)) :
    Even (fundamentalX D hD) :=
  (pellX_even_iff_fundamentalX_even_and_index_odd D hD hD_odd n).mp hx_even |>.1

/-- The Pell divisibility rank is odd whenever its squarefree kernel is odd. -/
theorem pellRank_odd_of_kernel_odd
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) :
    Odd (pellRank D hD) := by
  rw [← Nat.not_even_iff_odd]
  intro hRank_even
  have htwo_dvd_rank : 2 ∣ pellRank D hD := hRank_even.two_dvd
  have htwo_dvd_D : 2 ∣ D :=
    htwo_dvd_rank.trans (pellRank_dvd_kernel D hD)
  exact hD_odd.not_two_dvd_nat htwo_dvd_D

/-- Exact rank-and-parity normalization. Kernel divisibility of `Yₙ` and
evenness of `Xₙ` are equivalent to an even fundamental x-coordinate and an
odd rank multiple `R_D(2k+1)`. -/
theorem kernel_dvd_pellY_and_pellX_even_iff_rank_odd_index
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) (n : Nat) :
    D ∣ pellY D hD n ∧ Even (pellX D hD n) ↔
      Even (fundamentalX D hD) ∧
        ∃ k : Nat, n = pellRank D hD * (2 * k + 1) := by
  constructor
  · rintro ⟨hD_dvd_y, hx_even⟩
    have hRank_dvd_n : pellRank D hD ∣ n :=
      (D_dvd_pellY_iff_rank_dvd_index D hD n).mp hD_dvd_y
    obtain ⟨m, rfl⟩ := hRank_dvd_n
    have hindex_odd : Odd (pellRank D hD * m) :=
      index_odd_of_pellX_even D hD hD_odd hx_even
    have hm_odd : Odd m := (Nat.odd_mul.mp hindex_odd).2
    obtain ⟨k, hk⟩ := hm_odd.exists_bit1
    refine ⟨fundamentalX_even_of_pellX_even D hD hD_odd hx_even, k, ?_⟩
    rw [hk]
  · rintro ⟨hfund_even, k, rfl⟩
    constructor
    · apply (D_dvd_pellY_iff_rank_dvd_index D hD _).mpr
      exact dvd_mul_right (pellRank D hD) (2 * k + 1)
    · apply
        (pellX_even_iff_fundamentalX_even_and_index_odd
          D hD hD_odd _).mpr
      refine ⟨hfund_even, ?_⟩
      exact (pellRank_odd_of_kernel_odd D hD hD_odd).mul (odd_two_mul_add_one k)

/-- The normalized odd rank multiplier is unique. -/
theorem existsUnique_rank_odd_index_of_kernel_dvd_pellY_of_pellX_even
    (D : Nat) (hD : PellKernel D) (hD_odd : Odd D) {n : Nat}
    (hD_dvd_y : D ∣ pellY D hD n)
    (hx_even : Even (pellX D hD n)) :
    ∃! k : Nat, n = pellRank D hD * (2 * k + 1) := by
  obtain ⟨_hfund_even, k, hk⟩ :=
    (kernel_dvd_pellY_and_pellX_even_iff_rank_odd_index
      D hD hD_odd n).mp ⟨hD_dvd_y, hx_even⟩
  refine ⟨k, hk, ?_⟩
  intro j hj
  have hproducts :
      pellRank D hD * (2 * k + 1) =
        pellRank D hD * (2 * j + 1) := hk.symm.trans hj
  have hfactors : 2 * k + 1 = 2 * j + 1 :=
    Nat.mul_left_cancel (pellRank_pos D hD) hproducts
  omega

end Erdos364
