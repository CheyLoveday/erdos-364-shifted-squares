import Erdos364.SquareMiddle.RightFlankConsequences

namespace Erdos364

/-!
# Divisible quartic-Pell compression

A square-middle source has two coprime powerful values `X² - 1` and
`X² + 1`.  Multiplying their canonical square-cube normal forms compresses
the two kernels into one squarefree coefficient `M` and gives

`X⁴ = M * Y² + 1`, with `M ∣ Y`.

This module proves that the compression is source-equivalent.  It is only a
normalization theorem: it does not assert that divisible quartic-Pell data are
impossible.
-/

/-- Difference-of-squares factorization at the squared centre, with the
natural-subtraction boundary retained explicitly. -/
theorem fourth_sub_one_eq_square_flanks_mul {X : Nat} (hX : 0 < X) :
    X ^ 4 - 1 = (X ^ 2 - 1) * (X ^ 2 + 1) := by
  calc
    X ^ 4 - 1 = (X ^ 2) ^ 2 - 1 := by ring_nf
    _ = (X ^ 2 - 1) * (X ^ 2 + 1) :=
      square_sub_one_eq_flank_mul (pow_pos hX 2)

/-- At an even centre, the square-middle predicate is exactly powerfulness of
the quartic product.  The positivity in `PowerfulPos` rules out the remaining
`X = 0` boundary, so no separate `1 < X` hypothesis is needed on the right. -/
theorem squareMiddle_iff_even_powerfulPos_fourth_sub_one (X : Nat) :
    SquareMiddle X ↔ Even X ∧ PowerfulPos (X ^ 4 - 1) := by
  constructor
  · intro h
    refine ⟨h.center_even, ?_⟩
    rw [fourth_sub_one_eq_square_flanks_mul (Nat.zero_lt_of_lt h.1)]
    exact powerfulPos_mul h.2.1 h.2.2
  · rintro ⟨hEven, hpowerful⟩
    have hX : 1 < X := by
      by_contra hnot
      have hle : X ≤ 1 := Nat.le_of_not_gt hnot
      interval_cases X <;> norm_num [PowerfulPos] at hpowerful
    have hproduct :
        PowerfulPos ((X ^ 2 - 1) * (X ^ 2 + 1)) := by
      rw [← fourth_sub_one_eq_square_flanks_mul (by omega : 0 < X)]
      exact hpowerful
    obtain ⟨hlower, hupper⟩ :=
      powerfulPos_factors_of_coprime_mul
        (squareSubOne_squareAddOne_coprime_of_even hX hEven) hproduct
    exact ⟨hX, hlower, hupper⟩

/-- A positive natural solution of the quartic Pell equation carrying the
squarefree-kernel and deep divisibility data forced by a square-middle
counterexample. -/
structure DivisibleNatQuarticPell (M X Y : Nat) : Prop where
  X_one_lt : 1 < X
  X_even : Even X
  Y_pos : 0 < Y
  M_one_lt : 1 < M
  M_squarefree : _root_.Squarefree M
  equation : X ^ 4 = M * Y ^ 2 + 1
  M_dvd_Y : M ∣ Y

/-- Existentially packaged quartic-Pell data. -/
structure DivisibleQuarticPellData where
  M : Nat
  X : Nat
  Y : Nat
  valid : DivisibleNatQuarticPell M X Y

/-- Two square-cube flank normal forms give the compressed quartic-Pell
solution with `M = D*K` and `Y = (D*K)*(U*V)`. -/
theorem squareCubeNormalForms_to_divisibleNatQuarticPell
    {X U D V K : Nat} (hX : 1 < X) (hEven : Even X)
    (hlower : SquareCubeNormalForm (X ^ 2 - 1) U D)
    (hupper : SquareCubeNormalForm (X ^ 2 + 1) V K) :
    DivisibleNatQuarticPell
      (D * K) X ((D * K) * (U * V)) := by
  have hD_one_lt : 1 < D :=
    squareSubOne_normalForm_kernel_one_lt hX hlower
  have hK_one_lt : 1 < K :=
    squareCubeNormalForm_kernel_one_lt_of_square_add_one hX hupper
  have hcop : Nat.Coprime D K :=
    squareCubeNormalForm_kernels_coprime_of_even_center
      hX hEven hlower hupper
  refine
    { X_one_lt := hX
      X_even := hEven
      Y_pos := Nat.mul_pos (Nat.mul_pos hlower.2.1 hupper.2.1)
        (Nat.mul_pos hlower.1 hupper.1)
      M_one_lt := lt_of_lt_of_le hD_one_lt
        (Nat.le_mul_of_pos_right D (Nat.zero_lt_of_lt hK_one_lt))
      M_squarefree := (Nat.squarefree_mul hcop).2
        ⟨hlower.kernel_squarefree, hupper.kernel_squarefree⟩
      equation := ?_
      M_dvd_Y := ⟨U * V, rfl⟩ }
  calc
    X ^ 4 = (X ^ 4 - 1) + 1 := by
      have hpositive : 0 < X ^ 4 := pow_pos (by omega : 0 < X) 4
      omega
    _ = (X ^ 2 - 1) * (X ^ 2 + 1) + 1 := by
      rw [fourth_sub_one_eq_square_flanks_mul (by omega : 0 < X)]
    _ = (U ^ 2 * D ^ 3) * (V ^ 2 * K ^ 3) + 1 := by
      rw [hlower.2.2.1, hupper.2.2.1]
    _ = (D * K) * ((D * K) * (U * V)) ^ 2 + 1 := by ring

namespace DivisibleNatQuarticPell

/-- The divisibility condition `M ∣ Y` reconstructs a unique positive
square factor `W`, and hence the canonical square-cube form of `X⁴ - 1`. -/
theorem existsUnique_squareCubeNormalForm_factor {M X Y : Nat}
    (h : DivisibleNatQuarticPell M X Y) :
    ∃! W : Nat,
      Y = M * W ∧ SquareCubeNormalForm (X ^ 4 - 1) W M := by
  obtain ⟨W, hY⟩ := h.M_dvd_Y
  have hW_pos : 0 < W := by
    by_contra hnot
    have hW_zero : W = 0 := Nat.eq_zero_of_not_pos hnot
    have hY_zero : Y = 0 := by simpa [hW_zero] using hY
    exact (Nat.ne_of_gt h.Y_pos) hY_zero
  have hvalue : X ^ 4 - 1 = W ^ 2 * M ^ 3 := by
    calc
      X ^ 4 - 1 = M * Y ^ 2 := by
        rw [h.equation]
        omega
      _ = M * (M * W) ^ 2 := by rw [hY]
      _ = W ^ 2 * M ^ 3 := by ring
  have hform : SquareCubeNormalForm (X ^ 4 - 1) W M :=
    squareCubeNormalForm_of_eq_sq_mul_cube
      hW_pos (Nat.zero_lt_of_lt h.M_one_lt) hvalue h.M_squarefree
  refine ⟨W, ⟨hY, hform⟩, ?_⟩
  intro W' hW'
  apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt h.M_one_lt)
  calc
    M * W' = Y := hW'.1.symm
    _ = M * W := hY

/-- A divisible quartic-Pell solution reconstructs both powerful flanks and
therefore a square-middle source. -/
theorem toSquareMiddle {M X Y : Nat}
    (h : DivisibleNatQuarticPell M X Y) :
    SquareMiddle X := by
  apply (squareMiddle_iff_even_powerfulPos_fourth_sub_one X).2
  refine ⟨h.X_even, ?_⟩
  obtain ⟨W, hW, _hunique⟩ := h.existsUnique_squareCubeNormalForm_factor
  exact powerfulPos_of_squareCubeNormalForm hW.2

/-- The squarefree coefficient of every divisible quartic-Pell source is
seven modulo eight. -/
theorem kernel_mod_eight {M X Y : Nat}
    (h : DivisibleNatQuarticPell M X Y) :
    M % 8 = 7 := by
  obtain ⟨W, hW, _hunique⟩ := h.existsUnique_squareCubeNormalForm_factor
  have hXfourMod : X ^ 4 % 8 = 0 := by
    obtain ⟨t, rfl⟩ := h.X_even
    rw [show (t + t) ^ 4 = 8 * (2 * t ^ 4) by ring]
    simp
  have hmod : X ^ 4 ≡ 8 [MOD 8] := by
    change X ^ 4 % 8 = 8 % 8
    simpa using hXfourMod
  have hsub : X ^ 4 - 1 ≡ 8 - 1 [MOD 8] :=
    Nat.ModEq.sub
      (Nat.succ_le_iff.mpr
        (pow_pos (Nat.zero_lt_of_lt h.X_one_lt) 4))
      (by decide : 1 ≤ 8)
      hmod Nat.ModEq.rfl
  have hvalueMod : (X ^ 4 - 1) % 8 = 7 := by
    change (X ^ 4 - 1) % 8 = (8 - 1) % 8 at hsub
    simpa using hsub
  exact (hW.2.kernel_mod_eight_of_odd_value
    (by
      rw [Nat.odd_iff]
      have : (X ^ 4 - 1) % 2 = 1 := by
        rw [← Nat.mod_mod_of_dvd (X ^ 4 - 1) (by decide : 2 ∣ 8)]
        simp [hvalueMod]
      exact this)).trans hvalueMod

end DivisibleNatQuarticPell

namespace DivisibleQuarticPellData

/-- Packaged quartic-Pell data reconstruct a square-middle source. -/
theorem squareMiddle (data : DivisibleQuarticPellData) :
    SquareMiddle data.X :=
  data.valid.toSquareMiddle

/-- Packaged coefficient specialization of the universal mod-eight result. -/
theorem kernel_mod_eight (data : DivisibleQuarticPellData) :
    data.M % 8 = 7 :=
  data.valid.kernel_mod_eight

end DivisibleQuarticPellData

/-- Construct quartic-Pell data directly from a square-middle source. -/
theorem squareMiddle_to_divisibleNatQuarticPell {X : Nat}
    (h : SquareMiddle X) :
    ∃ M Y : Nat, DivisibleNatQuarticPell M X Y := by
  obtain ⟨U, D, hlower⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos h.2.1
  obtain ⟨V, K, hupper⟩ :=
    exists_squareCubeNormalForm_of_powerfulPos h.2.2
  exact
    ⟨D * K, (D * K) * (U * V),
      squareCubeNormalForms_to_divisibleNatQuarticPell
        h.1 h.center_even hlower hupper⟩

/-- Exact source equivalence at a fixed centre. -/
theorem squareMiddle_iff_divisibleQuarticPell (X : Nat) :
    SquareMiddle X ↔
      ∃ M Y : Nat, DivisibleNatQuarticPell M X Y := by
  constructor
  · exact squareMiddle_to_divisibleNatQuarticPell
  · rintro ⟨M, Y, h⟩
    exact h.toSquareMiddle

/-- Global source equivalence in the packaged form consumed by theorem
interfaces which eliminate all quartic-Pell data. -/
theorem squareMiddle_iff_nonempty_divisibleQuarticPell :
    (∃ X : Nat, SquareMiddle X) ↔
      Nonempty DivisibleQuarticPellData := by
  constructor
  · rintro ⟨X, hX⟩
    obtain ⟨M, Y, hquartic⟩ :=
      (squareMiddle_iff_divisibleQuarticPell X).1 hX
    exact ⟨⟨M, X, Y, hquartic⟩⟩
  · rintro ⟨data⟩
    exact ⟨data.X, data.squareMiddle⟩

/-- The existing canonical right-flank eliminator is exactly nonexistence of
source-equivalent divisible quartic-Pell data. -/
theorem pellShiftClosed_iff_no_divisibleQuarticPellData :
    PellShiftClosed ↔ ¬ Nonempty DivisibleQuarticPellData := by
  constructor
  · intro hclosed
    have hnoCanonical :=
      pellShiftClosed_iff_no_pairPellCounterexample.mp hclosed
    rintro ⟨quartic⟩
    obtain ⟨canonical, _hrep⟩ :=
      (squareMiddle_iff_pairPellCounterexample quartic.X).mp
        quartic.squareMiddle
    exact hnoCanonical ⟨canonical⟩
  · intro hnoQuartic
    apply pellShiftClosed_iff_no_pairPellCounterexample.mpr
    rintro ⟨canonical⟩
    apply hnoQuartic
    obtain ⟨M, Y, hquartic⟩ :=
      squareMiddle_to_divisibleNatQuarticPell canonical.squareMiddle
    exact ⟨⟨M, canonical.center, Y, hquartic⟩⟩

namespace PairPellCounterexampleData

/-- The canonical two-kernel package compressed to one divisible quartic-Pell
solution. -/
theorem toDivisibleNatQuarticPell (data : PairPellCounterexampleData) :
    DivisibleNatQuarticPell
      (data.pell.D * data.upperKernel) data.center
      ((data.pell.D * data.upperKernel) *
        (data.lowerSquarePart * data.upperSquarePart)) :=
  squareCubeNormalForms_to_divisibleNatQuarticPell
    data.center_one_lt data.center_even
    data.lowerNormalForm data.upperNormalForm

/-- Packaged adapter from the canonical lower/upper counterexample record. -/
noncomputable def toDivisibleQuarticPellData
    (data : PairPellCounterexampleData) : DivisibleQuarticPellData :=
  { M := data.pell.D * data.upperKernel
    X := data.center
    Y := (data.pell.D * data.upperKernel) *
      (data.lowerSquarePart * data.upperSquarePart)
    valid := data.toDivisibleNatQuarticPell }

@[simp] theorem quarticPell_kernel_eq_lower_mul_upper
    (data : PairPellCounterexampleData) :
    data.toDivisibleQuarticPellData.M =
      data.pell.D * data.upperKernel :=
  rfl

@[simp] theorem quarticPell_center_eq
    (data : PairPellCounterexampleData) :
    data.toDivisibleQuarticPellData.X = data.center :=
  rfl

@[simp] theorem quarticPell_y_eq_kernel_mul_lower_mul_upper
    (data : PairPellCounterexampleData) :
    data.toDivisibleQuarticPellData.Y =
      (data.pell.D * data.upperKernel) *
        (data.lowerSquarePart * data.upperSquarePart) :=
  rfl

end PairPellCounterexampleData

end Erdos364
