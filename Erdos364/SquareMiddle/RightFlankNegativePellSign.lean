import Erdos364.SquareMiddle.FixedPellFlankAllocation
import Erdos364.SquareMiddle.RightFlankNormOneModNine

namespace Erdos364

open Pell

/-!
# Exact fundamental-sign classifier for negative Pell solubility

On the canonical upper-kernel domain `K ≡ 1 (mod 4)`, positive solubility of
`X² + 1 = K W²` is equivalent to the selected positive fundamental norm-one
real coordinate being `-1` modulo `K`.

The forward implication follows from negative-Pell orbit completeness.  For
the converse, oddness of the fundamental real coordinate splits its Pell
equation into two coprime factors of a square and reconstructs a positive
negative-Pell solution.

This gives a reusable `U₀` complete-fibre eliminator.  It is a classifier and
source adapter, not a statement that every admissible kernel fails the sign
test.
-/

/-- Positive-natural solubility of the negative Pell equation. -/
def PositiveNegativePellSoluble (K : Nat) : Prop :=
  ∃ X W : Nat, 0 < X ∧ 0 < W ∧ X ^ 2 + 1 = K * W ^ 2

private theorem two_lt_of_pellKernel_of_mod_four_eq_one
    {K : Nat} (hPK : PellKernel K) (hmod : K % 4 = 1) :
    2 < K := by
  have hKOne : 1 < K := hPK.1
  omega

private theorem odd_of_mod_four_eq_one
    {K : Nat} (hmod : K % 4 = 1) :
    Odd K := by
  rw [Nat.odd_iff]
  omega

private theorem coprime_factors_of_square_local
    {A B C : Nat} (hcop : Nat.Coprime A B)
    (hprod : A * B = C ^ 2) :
    ∃ a b : Nat, A = a ^ 2 ∧ B = b ^ 2 := by
  have hsplit :
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
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hsplit
  exact ⟨a, b, ha, hb⟩

/-- For a Pell kernel congruent to one modulo four, the fundamental
norm-one real coordinate is odd. -/
theorem fundamentalX_odd_of_mod_four_eq_one
    (K : Nat) (hPK : PellKernel K) (hmod : K % 4 = 1) :
    Odd (fundamentalX K hPK) := by
  have hKodd : Odd K := odd_of_mod_four_eq_one hmod
  rw [← Nat.not_even_iff_odd]
  intro hXeven
  have hYodd : Odd (fundamentalY K hPK) :=
    (fundamentalX_even_iff_fundamentalY_odd K hPK hKodd).mp hXeven
  obtain ⟨r, hr⟩ := hXeven
  obtain ⟨s, hs⟩ := hYodd
  have hKcast : (K : ZMod 4) = 1 := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    simp [Nat.ModEq, hmod]
  have heq :=
    congrArg (fun value : Nat => (value : ZMod 4))
      (fundamental_pell_equation_add K hPK)
  push_cast at heq
  rw [hr, hs, hKcast] at heq
  have hrSq : (((r + r : Nat) : ZMod 4) ^ 2) = 0 := by
    push_cast
    ring_nf
    rw [show (4 : ZMod 4) = 0 by decide]
    ring
  have hsSq : (((2 * s + 1 : Nat) : ZMod 4) ^ 2) = 1 := by
    push_cast
    ring_nf
    rw [show (4 : ZMod 4) = 0 by decide]
    ring
  rw [hrSq, hsSq] at heq
  exact (by decide : (0 : ZMod 4) ≠ 1 + 1) (by simpa using heq)

/-- On the `K ≡ 1 (mod 4)` Pell-kernel domain, positive negative-Pell
solubility is equivalent to the selected fundamental norm-one real
coordinate being `-1` modulo `K`. -/
theorem positiveNegativePellSoluble_iff_fundamentalPell_x_eq_negOne
    (K : Nat) (hPK : PellKernel K) (hmod : K % 4 = 1) :
    PositiveNegativePellSoluble K ↔
      (((fundamentalPell K hPK).x : ZMod K) = -1) := by
  constructor
  · rintro ⟨X, W, hX, hW, hPell⟩
    obtain ⟨_n, _hnOdd, _hpow, hsign⟩ :=
      negativePell_eq_fundamental_odd_power_and_x_mod_kernel
        (two_lt_of_pellKernel_of_mod_four_eq_one hPK hmod)
        (fundamentalPell K hPK)
        (fundamentalPell_isFundamental K hPK)
        hX hW hPell
    exact hsign
  · intro hsign
    let a := fundamentalX K hPK
    let b := fundamentalY K hPK
    have haOne : 1 < a := by
      simpa [a] using fundamentalX_one_lt K hPK
    have hEq : a ^ 2 = 1 + K * b ^ 2 := by
      simpa [a, b] using fundamental_pell_equation_add K hPK
    have hKodd : Odd K := odd_of_mod_four_eq_one hmod
    have haOdd : Odd a := by
      simpa [a] using fundamentalX_odd_of_mod_four_eq_one K hPK hmod
    have hbEven : Even b :=
      (fundamentalX_odd_iff_fundamentalY_even K hPK hKodd).mp
        (by simpa [a, b] using haOdd)
    have hsignNat : (a : ZMod K) = -1 := by
      have hcastRaw :=
        congrArg (fun value : Int => (value : ZMod K))
          (fundamentalX_intCast K hPK)
      have hcast :
          ((fundamentalX K hPK : Nat) : ZMod K) =
            ((fundamentalPell K hPK).x : ZMod K) := by
        simpa using hcastRaw
      calc
        (a : ZMod K) =
            ((fundamentalX K hPK : Nat) : ZMod K) := by rfl
        _ = ((fundamentalPell K hPK).x : ZMod K) := hcast
        _ = -1 := hsign
    have hKdvdAplus : K ∣ a + 1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      push_cast
      rw [hsignNat]
      ring
    obtain ⟨A, haEq⟩ := haOdd
    obtain ⟨v, hbEq⟩ := hbEven
    have hKcopTwo : K.Coprime 2 :=
      Nat.coprime_two_right.mpr hKodd
    have hKdvdA1 : K ∣ A + 1 := by
      apply hKcopTwo.dvd_of_dvd_mul_left
      convert hKdvdAplus using 1
      rw [haEq]
      ring
    obtain ⟨B, hA1Eq⟩ := hKdvdA1
    have hAB : A * B = v ^ 2 := by
      have hAA : A * (A + 1) = K * v ^ 2 := by
        rw [haEq, hbEq] at hEq
        nlinarith
      have hKmul : K * (A * B) = K * v ^ 2 := by
        calc
          K * (A * B) = A * (K * B) := by ring
          _ = A * (A + 1) := by rw [hA1Eq]
          _ = K * v ^ 2 := hAA
      exact
        Nat.eq_of_mul_eq_mul_left
          (Nat.zero_lt_of_lt hPK.1) hKmul
    have hAcopA1 : A.Coprime (A + 1) := by
      rw [Nat.coprime_self_add_right]
      simp
    have hBdvdA1 : B ∣ A + 1 := by
      refine ⟨K, ?_⟩
      rw [hA1Eq]
      ring
    have hAcopB : A.Coprime B :=
      hAcopA1.of_dvd_right hBdvdA1
    obtain ⟨X, W, hAsq, hBsq⟩ :=
      coprime_factors_of_square_local hAcopB hAB
    have hXPos : 0 < X := by
      have hAPos : 0 < A := by
        rw [haEq] at haOne
        omega
      rw [hAsq] at hAPos
      by_contra hX
      have hXzero : X = 0 := Nat.eq_zero_of_not_pos hX
      simp [hXzero] at hAPos
    have hWPos : 0 < W := by
      have hBPos : 0 < B := by
        have hA1Pos : 0 < A + 1 := by omega
        rw [hA1Eq] at hA1Pos
        by_contra hB
        have hBzero : B = 0 := Nat.eq_zero_of_not_pos hB
        simp [hBzero] at hA1Pos
      rw [hBsq] at hBPos
      by_contra hW
      have hWzero : W = 0 := Nat.eq_zero_of_not_pos hW
      simp [hWzero] at hBPos
    refine ⟨X, W, hXPos, hWPos, ?_⟩
    calc
      X ^ 2 + 1 = A + 1 := by rw [hAsq]
      _ = K * B := hA1Eq
      _ = K * W ^ 2 := by rw [hBsq]

/-- Natural-coordinate spelling of the exact classifier. -/
theorem positiveNegativePellSoluble_iff_fundamentalX_eq_negOne
    (K : Nat) (hPK : PellKernel K) (hmod : K % 4 = 1) :
    PositiveNegativePellSoluble K ↔
      ((fundamentalX K hPK : ZMod K) = -1) := by
  have hcastRaw :=
    congrArg (fun value : Int => (value : ZMod K))
      (fundamentalX_intCast K hPK)
  have hcast :
      ((fundamentalX K hPK : Nat) : ZMod K) =
        ((fundamentalPell K hPK).x : ZMod K) := by
    simpa using hcastRaw
  constructor
  · intro h
    exact hcast.trans <|
      (positiveNegativePellSoluble_iff_fundamentalPell_x_eq_negOne
        K hPK hmod).mp h
  · intro h
    apply
      (positiveNegativePellSoluble_iff_fundamentalPell_x_eq_negOne
        K hPK hmod).mpr
    exact hcast.symm.trans h

/-- Contrapositive form of the exact natural-coordinate classifier. -/
theorem no_positiveNegativePell_of_fundamentalX_ne_negOne
    (K : Nat) (hPK : PellKernel K) (hmod : K % 4 = 1)
    (hne : (fundamentalX K hPK : ZMod K) ≠ -1) :
    ¬ PositiveNegativePellSoluble K := by
  intro hsol
  exact hne <|
    (positiveNegativePellSoluble_iff_fundamentalX_eq_negOne
      K hPK hmod).mp hsol

/-- Complete fixed-upper-fibre eliminator obtained from the exact
fundamental-sign classifier. -/
theorem no_pairPellCounterexample_upperKernel_of_fundamentalX_ne_negOne
    {K : Nat} (hPK : PellKernel K) (hmod : K % 4 = 1)
    (hne : (fundamentalX K hPK : ZMod K) ≠ -1)
    (data : PairPellCounterexampleData)
    (hupper : data.upperKernel = K) :
    False := by
  apply no_positiveNegativePell_of_fundamentalX_ne_negOne K hPK hmod hne
  have hnegative := data.upper_negativePell
  refine
    ⟨data.center, data.upperKernel * data.upperSquarePart,
      Nat.zero_lt_of_lt data.center_one_lt, hnegative.W_pos, ?_⟩
  simpa [hupper] using hnegative.equation.symm

end Erdos364
