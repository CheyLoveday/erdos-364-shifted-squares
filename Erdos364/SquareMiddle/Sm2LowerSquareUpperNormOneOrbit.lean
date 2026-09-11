import Erdos364.SquareMiddle.Sm2LowerSquareLowerNormTwoOrbit

namespace Erdos364

open Pell

/-!
# Exact upper norm-one orbit for `sm2LowerSquare`

This module exposes the upper negative-Pell source as an exact odd,
rank-divisible power of the selected fundamental norm-one unit.  It also
uses the retained leaf congruences to sharpen the fundamental real
coordinate to two classes modulo `576`.
-/

private theorem coprime_factors_of_square_upper
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

/-- The fundamental norm-one unit has a positive norm-minus-one square root
whenever its real coordinate has the exact negative-Pell sign. -/
theorem exists_fundamental_negativePell_root
    (K : Nat) (hK : PellKernel K) (hmod : K % 4 = 1)
    (hsign : (fundamentalX K hK : ZMod K) = -1) :
    ∃ u v : Nat,
      0 < u ∧
        0 < v ∧
          u ^ 2 + 1 = K * v ^ 2 ∧
            fundamentalX K hK = 2 * u ^ 2 + 1 ∧
              fundamentalY K hK = 2 * u * v := by
  let a := fundamentalX K hK
  let b := fundamentalY K hK
  have haOne : 1 < a := by
    simpa [a] using fundamentalX_one_lt K hK
  have hEq : a ^ 2 = 1 + K * b ^ 2 := by
    simpa [a, b] using fundamental_pell_equation_add K hK
  have hKodd : Odd K := by
    rw [Nat.odd_iff]
    omega
  have haOdd : Odd a := by
    simpa [a] using
      fundamentalX_odd_of_mod_four_eq_one K hK hmod
  have hbEven : Even b :=
    (fundamentalX_odd_iff_fundamentalY_even K hK hKodd).mp
      (by simpa [a, b] using haOdd)
  have hKdvdAplus : K ∣ a + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    change (fundamentalX K hK : ZMod K) + 1 = 0
    rw [hsign]
    ring
  obtain ⟨A, haEq⟩ := haOdd
  obtain ⟨w, hbEq⟩ := hbEven
  have hKcopTwo : K.Coprime 2 :=
    Nat.coprime_two_right.mpr hKodd
  have hKdvdA1 : K ∣ A + 1 := by
    apply hKcopTwo.dvd_of_dvd_mul_left
    convert hKdvdAplus using 1
    rw [haEq]
    ring
  obtain ⟨B, hA1Eq⟩ := hKdvdA1
  have hAB : A * B = w ^ 2 := by
    have hAA : A * (A + 1) = K * w ^ 2 := by
      rw [haEq, hbEq] at hEq
      nlinarith
    have hKmul : K * (A * B) = K * w ^ 2 := by
      calc
        K * (A * B) = A * (K * B) := by ring
        _ = A * (A + 1) := by rw [hA1Eq]
        _ = K * w ^ 2 := hAA
    exact
      Nat.eq_of_mul_eq_mul_left
        (Nat.zero_lt_of_lt hK.1) hKmul
  have hAcopA1 : A.Coprime (A + 1) := by
    rw [Nat.coprime_self_add_right]
    simp
  have hBdvdA1 : B ∣ A + 1 := by
    refine ⟨K, ?_⟩
    rw [hA1Eq]
    ring
  have hAcopB : A.Coprime B :=
    hAcopA1.of_dvd_right hBdvdA1
  obtain ⟨u, v, hAsq, hBsq⟩ :=
    coprime_factors_of_square_upper hAcopB hAB
  have huPos : 0 < u := by
    have hAPos : 0 < A := by
      rw [haEq] at haOne
      omega
    rw [hAsq] at hAPos
    by_contra hu
    have huZero : u = 0 := Nat.eq_zero_of_not_pos hu
    simp [huZero] at hAPos
  have hvPos : 0 < v := by
    have hBPos : 0 < B := by
      have hA1Pos : 0 < A + 1 := by omega
      rw [hA1Eq] at hA1Pos
      rcases Nat.eq_zero_or_pos B with hBZero | hBPos
      · simp [hBZero] at hA1Pos
      · exact hBPos
    rw [hBsq] at hBPos
    by_contra hv
    have hvZero : v = 0 := Nat.eq_zero_of_not_pos hv
    simp [hvZero] at hBPos
  have hwEq : w = u * v := by
    have hsquares : w ^ 2 = (u * v) ^ 2 := by
      calc
        w ^ 2 = A * B := hAB.symm
        _ = u ^ 2 * v ^ 2 := by rw [hAsq, hBsq]
        _ = (u * v) ^ 2 := by ring
    exact
      Nat.pow_left_injective
        (by decide : (2 : Nat) ≠ 0) hsquares
  refine ⟨u, v, huPos, hvPos, ?_, ?_, ?_⟩
  · calc
      u ^ 2 + 1 = A + 1 := by rw [hAsq]
      _ = K * B := hA1Eq
      _ = K * v ^ 2 := by rw [hBsq]
  · rw [show fundamentalX K hK = a by rfl, haEq, hAsq]
  · rw [show fundamentalY K hK = b by rfl, hbEq, hwEq]
    ring

/-- Natural coordinates of the squared negative-Pell source when it is
identified with a canonical norm-one Pell power. -/
theorem negativePellSquareSolution_pellCoordinates
    {K X W : Nat} (hK : PellKernel K)
    (hPell : X ^ 2 + 1 = K * W ^ 2) (n : Nat)
    (hpow :
      negativePellSquareSolution hPell =
        pellSolution K hK n) :
    pellX K hK n = 2 * X ^ 2 + 1 ∧
      pellY K hK n = 2 * X * W := by
  have hzX :
      (negativePellSquareSolution hPell).x =
        2 * (X : Int) ^ 2 + 1 := by
    simp only [negativePellSquareSolution, Pell.Solution₁.x_mk]
    have hPellInt :
        (X : Int) ^ 2 + 1 = K * (W : Int) ^ 2 := by
      exact_mod_cast hPell
    linarith
  have hxInt :
      (pellX K hK n : Int) =
        2 * (X : Int) ^ 2 + 1 := by
    calc
      (pellX K hK n : Int) =
          (pellSolution K hK n).x :=
        pellX_intCast K hK n
      _ = (negativePellSquareSolution hPell).x := by
        rw [hpow]
      _ = 2 * (X : Int) ^ 2 + 1 := hzX
  have hyInt :
      (pellY K hK n : Int) =
        2 * (X : Int) * W := by
    calc
      (pellY K hK n : Int) =
          (pellSolution K hK n).y :=
        pellY_intCast K hK n
      _ = (negativePellSquareSolution hPell).y := by
        rw [hpow]
      _ = 2 * (X : Int) * W := by
        simp only [negativePellSquareSolution, Pell.Solution₁.y_mk]
  have hxNatCast :
      (pellX K hK n : Int) =
        ((2 * X ^ 2 + 1 : Nat) : Int) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one] using hxInt
  have hyNatCast :
      (pellY K hK n : Int) =
        ((2 * X * W : Nat) : Int) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hyInt
  exact ⟨Int.ofNat_inj.mp hxNatCast, Int.ofNat_inj.mp hyNatCast⟩

/-- A divisible negative-Pell source enters a unique odd multiple of the
canonical norm-one divisibility rank. -/
theorem divisibleNegativePell_exists_normOne_depth
    {K X W : Nat} (hK : PellKernel K) (hKodd : Odd K)
    (hKtwo : 2 < K) (hnegative : DivisibleNatNegativePell K X W) :
    ∃ n : Nat,
      Odd n ∧
        negativePellSquareSolution hnegative.equation.symm =
          pellSolution K hK n ∧
          pellX K hK n = 2 * X ^ 2 + 1 ∧
            pellY K hK n = 2 * X * W ∧
              ∃! t : Nat,
                n = pellRank K hK * (2 * t + 1) := by
  obtain ⟨n, hnOdd, hpow, _hsign⟩ :=
    negativePell_eq_fundamental_odd_power_and_x_mod_kernel
      hKtwo (fundamentalPell K hK)
      (fundamentalPell_isFundamental K hK)
      (Nat.zero_lt_of_lt hnegative.X_one_lt)
      hnegative.W_pos hnegative.equation.symm
  have hcoords :=
    negativePellSquareSolution_pellCoordinates
      hK hnegative.equation.symm n hpow
  have hKdY : K ∣ pellY K hK n := by
    rw [hcoords.2]
    obtain ⟨V, hW⟩ := hnegative.K_dvd_W
    refine ⟨2 * X * V, ?_⟩
    rw [hW]
    ring
  have hRank : pellRank K hK ∣ n :=
    (D_dvd_pellY_iff_rank_dvd_index K hK n).mp hKdY
  have hRankOdd : Odd (pellRank K hK) :=
    pellRank_odd_of_kernel_odd K hK hKodd
  have hdepth :
      ∃! t : Nat, n = pellRank K hK * (2 * t + 1) :=
    (odd_dvd_iff_existsUnique_twice_mul_add_one
      (pellRank_pos K hK) hRankOdd).mp ⟨hRank, hnOdd⟩
  exact
    ⟨n, hnOdd, hpow, hcoords.1, hcoords.2, hdepth⟩

private theorem negativePell_root_mod_four
    {K u v : Nat} (hK : K % 8 = 5)
    (heq : u ^ 2 + 1 = K * v ^ 2) :
    u % 4 = 2 := by
  have hcast :=
    congrArg (fun n : Nat => (n : ZMod 8)) heq
  push_cast at hcast
  have hKcast : (K : ZMod 8) = 5 :=
    (ZMod.natCast_eq_natCast_iff' K 5 8).mpr hK
  rw [hKcast] at hcast
  have hclass :
      ∀ x y : ZMod 8,
        x ^ 2 + 1 = 5 * y ^ 2 →
          x = 2 ∨ x = 6 := by
    decide
  rcases hclass (u : ZMod 8) (v : ZMod 8) hcast with hu2 | hu6
  · have hu8 : u % 8 = 2 :=
      (ZMod.natCast_eq_natCast_iff' u 2 8).mp hu2
    have hm := Nat.mod_mod_of_dvd u (by decide : 4 ∣ 8)
    rw [hu8] at hm
    omega
  · have hu8 : u % 8 = 6 :=
      (ZMod.natCast_eq_natCast_iff' u 6 8).mp hu6
    have hm := Nat.mod_mod_of_dvd u (by decide : 4 ∣ 8)
    rw [hu8] at hm
    omega

private theorem twice_square_add_one_mod_sixtyFour
    {u : Nat} (hu : u % 4 = 2) :
    (2 * u ^ 2 + 1) % 64 = 9 := by
  have huEq : u = 4 * (u / 4) + 2 := by
    have hdiv := (Nat.mod_add_div u 4).symm
    rw [hu] at hdiv
    omega
  rcases (u / 4).even_or_odd with ht | ht
  · obtain ⟨j, hj⟩ := ht
    have huCast : (u : ZMod 64) = 8 * j + 2 := by
      rw [huEq, hj]
      push_cast
      ring
    apply (ZMod.natCast_eq_natCast_iff' _ 9 64).mp
    push_cast
    rw [huCast]
    ring_nf
    rw [show (64 : ZMod 64) = 0 by decide,
      show (128 : ZMod 64) = 0 by decide]
    ring
  · obtain ⟨j, hj⟩ := ht
    have huCast : (u : ZMod 64) = 8 * j + 6 := by
      rw [huEq, hj]
      push_cast
      ring
    apply (ZMod.natCast_eq_natCast_iff' _ 9 64).mp
    push_cast
    rw [huCast]
    ring_nf
    rw [show (192 : ZMod 64) = 0 by decide,
      show (128 : ZMod 64) = 0 by decide,
      show (73 : ZMod 64) = 9 by decide]
    ring

/-- The canonical upper fundamental unit of every `sm2LowerSquare`
allocation has a positive fundamental norm-minus-one square root. -/
theorem Sm2LowerSquareAllocation.exists_upper_fundamental_negativePell_root
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    ∃ u v : Nat,
      0 < u ∧
        0 < v ∧
          u ^ 2 + 1 = data.upperKernel * v ^ 2 ∧
            fundamentalX data.upperKernel allocation.upper_pellKernel =
              2 * u ^ 2 + 1 ∧
              fundamentalY data.upperKernel allocation.upper_pellKernel =
                2 * u * v := by
  let K := data.upperKernel
  let hK : PellKernel K := allocation.upper_pellKernel
  have hKFour : K % 4 = 1 := by
    have hTwentyFour : K % 24 = 5 := allocation.kernel_residues.2
    have hmod := Nat.mod_mod_of_dvd K (by decide : 4 ∣ 24)
    rw [hTwentyFour] at hmod
    omega
  have hsol : PositiveNegativePellSoluble K := by
    have hnegative := data.upper_negativePell
    exact
      ⟨data.center, K * data.upperSquarePart,
        Nat.zero_lt_of_lt data.center_one_lt,
        hnegative.W_pos,
        by simpa [K] using hnegative.equation.symm⟩
  have hsign :
      (fundamentalX K hK : ZMod K) = -1 :=
    (positiveNegativePellSoluble_iff_fundamentalX_eq_negOne
      K hK hKFour).mp hsol
  simpa [K, hK] using
    exists_fundamental_negativePell_root K hK hKFour hsign

/-- The selected upper norm-one real coordinate is always `9 mod 64` on
the `sm2LowerSquare` leaf. -/
theorem Sm2LowerSquareAllocation.upperFundamentalX_mod_sixtyFour
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    fundamentalX data.upperKernel allocation.upper_pellKernel % 64 = 9 := by
  obtain ⟨u, v, _huPos, _hvPos, hnegative, hreal, _himag⟩ :=
    allocation.exists_upper_fundamental_negativePell_root
  have hKEight : data.upperKernel % 8 = 5 := by
    have hTwentyFour := allocation.kernel_residues.2
    have hmod :=
      Nat.mod_mod_of_dvd data.upperKernel (by decide : 8 ∣ 24)
    rw [hTwentyFour] at hmod
    omega
  have huFour : u % 4 = 2 :=
    negativePell_root_mod_four hKEight hnegative
  rw [hreal]
  exact twice_square_add_one_mod_sixtyFour huFour

/-- Symbolic norm-one power state modulo nine.  The first component is the
real coordinate; the second is the coefficient multiplying the generator's
ordinate. -/
def normOnePowerStateModNine (a : ZMod 9) :
    Nat → ZMod 9 × ZMod 9
  | 0 => (1, 0)
  | n + 1 =>
      let s := normOnePowerStateModNine a n
      (a * s.1 + (a ^ 2 - 1) * s.2, s.1 + a * s.2)

private theorem pellSolution_pow_state_modNine
    {K : Nat} (e : Pell.Solution₁ (K : Int)) (n : Nat) :
    ((e ^ n).x : ZMod 9) =
        (normOnePowerStateModNine (e.x : ZMod 9) n).1 ∧
      ((e ^ n).y : ZMod 9) =
        (normOnePowerStateModNine (e.x : ZMod 9) n).2 *
          (e.y : ZMod 9) := by
  have hnorm :
      (K : ZMod 9) * (e.y : ZMod 9) ^ 2 =
        (e.x : ZMod 9) ^ 2 - 1 := by
    have h := congrArg (fun z : Int => (z : ZMod 9)) e.prop
    push_cast at h
    linear_combination -h
  induction n with
  | zero =>
      simp [normOnePowerStateModNine]
  | succ n ih =>
      constructor
      · rw [pow_succ, Pell.Solution₁.x_mul]
        push_cast
        rw [ih.1, ih.2]
        simp only [normOnePowerStateModNine]
        linear_combination
          (normOnePowerStateModNine
            (e.x : ZMod 9) n).2 * hnorm
      · rw [pow_succ, Pell.Solution₁.y_mul]
        push_cast
        rw [ih.1, ih.2]
        simp only [normOnePowerStateModNine]
        ring

set_option maxRecDepth 4096 in
private theorem normOnePowerStateModNine_thirtySix (a : ZMod 9) :
    normOnePowerStateModNine a 36 = (1, 0) := by
  fin_cases a <;> decide

private theorem pellSolution_pow_modNine_periodic
    {K : Nat} (e : Pell.Solution₁ (K : Int)) :
    Function.Periodic
      (fun n : Nat =>
        (((e ^ n).x : ZMod 9), ((e ^ n).y : ZMod 9))) 36 := by
  have hstate := pellSolution_pow_state_modNine e 36
  rw [normOnePowerStateModNine_thirtySix] at hstate
  have hthirtySix :
      ((e ^ 36).x : ZMod 9) = 1 ∧
        ((e ^ 36).y : ZMod 9) = 0 := by
    simpa using hstate
  intro n
  apply Prod.ext
  · change ((e ^ (n + 36)).x : ZMod 9) =
      ((e ^ n).x : ZMod 9)
    rw [pow_add, Pell.Solution₁.x_mul]
    push_cast
    rw [hthirtySix.1, hthirtySix.2]
    ring
  · change ((e ^ (n + 36)).y : ZMod 9) =
      ((e ^ n).y : ZMod 9)
    rw [pow_add, Pell.Solution₁.y_mul]
    push_cast
    rw [hthirtySix.1, hthirtySix.2]
    ring

set_option maxRecDepth 4096 in
private theorem normOnePowerStateModNine_classification_table :
    ∀ (a : ZMod 9) (r : Fin 36),
      r.1 % 2 = 1 →
        (normOnePowerStateModNine a r.1).1 = 3 →
          (a = 3 ∧ (r.1 % 12 = 1 ∨ r.1 % 12 = 11)) ∨
            (a = 6 ∧ (r.1 % 12 = 5 ∨ r.1 % 12 = 7)) := by
  decide

private theorem normOnePowerStateModNine_classifies_odd_trace_three
    (a : ZMod 9) (r : Nat)
    (hr : r < 36) (hodd : r % 2 = 1)
    (hx : (normOnePowerStateModNine a r).1 = 3) :
    (a = 3 ∧ (r % 12 = 1 ∨ r % 12 = 11)) ∨
      (a = 6 ∧ (r % 12 = 5 ∨ r % 12 = 7)) := by
  exact
    normOnePowerStateModNine_classification_table
      a ⟨r, hr⟩ hodd hx

/-- The leaf trace `2*X²+1 = 3 mod 9` leaves exactly two possible
fundamental generator classes and their corresponding total exponent
classes modulo twelve. -/
theorem Sm2LowerSquareAllocation.upperNormOne_exponent_classes
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) {n : Nat}
    (hnOdd : Odd n)
    (hpow :
      negativePellSquareSolution
          data.upper_negativePell.equation.symm =
        fundamentalPell data.upperKernel
            allocation.upper_pellKernel ^ n) :
    ((((fundamentalPell data.upperKernel
          allocation.upper_pellKernel).x : ZMod 9) = 3 ∧
        (n % 12 = 1 ∨ n % 12 = 11)) ∨
      (((fundamentalPell data.upperKernel
          allocation.upper_pellKernel).x : ZMod 9) = 6 ∧
        (n % 12 = 5 ∨ n % 12 = 7))) := by
  let K := data.upperKernel
  let hK : PellKernel K := allocation.upper_pellKernel
  let e := fundamentalPell K hK
  have hcenterSqModNine : data.center ^ 2 % 9 = 1 := by
    have hThirtySix := allocation.middle_mod_thirtySix
    have hmod :=
      Nat.mod_mod_of_dvd (data.center ^ 2)
        (by decide : 9 ∣ 36)
    rw [hThirtySix] at hmod
    omega
  have hcenterSqCast :
      ((data.center ^ 2 : Nat) : ZMod 9) = 1 := by
    apply
      (ZMod.natCast_eq_natCast_iff'
        (data.center ^ 2) 1 9).mpr
    simpa using hcenterSqModNine
  have hzXInt :
      (negativePellSquareSolution
        data.upper_negativePell.equation.symm).x =
          2 * (data.center : Int) ^ 2 + 1 := by
    simp only [negativePellSquareSolution, Pell.Solution₁.x_mk]
    have hPellInt :
        (data.center : Int) ^ 2 + 1 =
          data.upperKernel *
            (data.upperKernel * data.upperSquarePart : Int) ^ 2 := by
      exact_mod_cast data.upper_negativePell.equation.symm
    push_cast at hPellInt ⊢
    linarith
  have hzXNine :
      ((negativePellSquareSolution
        data.upper_negativePell.equation.symm).x : ZMod 9) = 3 := by
    rw [hzXInt]
    push_cast
    rw [show ((data.center : ZMod 9) ^ 2) =
        ((data.center ^ 2 : Nat) : ZMod 9) by simp]
    rw [hcenterSqCast]
    decide
  have hperiod :=
    (pellSolution_pow_modNine_periodic e).map_mod_nat n
  have hperiodX := congrArg Prod.fst hperiod
  simp only at hperiodX
  have hstate :=
    pellSolution_pow_state_modNine e (n % 36)
  have hstateX :
      (normOnePowerStateModNine
        (e.x : ZMod 9) (n % 36)).1 = 3 := by
    have hpow' :
        negativePellSquareSolution
            data.upper_negativePell.equation.symm =
          e ^ n := by
      simpa [K, hK, e] using hpow
    calc
      (normOnePowerStateModNine
          (e.x : ZMod 9) (n % 36)).1 =
          ((e ^ (n % 36)).x : ZMod 9) := hstate.1.symm
      _ = ((e ^ n).x : ZMod 9) := hperiodX
      _ =
          ((negativePellSquareSolution
            data.upper_negativePell.equation.symm).x :
              ZMod 9) := by rw [hpow']
      _ = 3 := hzXNine
  have hnTwo : n % 2 = 1 := Nat.odd_iff.mp hnOdd
  have hrOdd : n % 36 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 36)]
    exact hnTwo
  have hrLt : n % 36 < 36 := Nat.mod_lt _ (by decide)
  have hclass :=
    normOnePowerStateModNine_classifies_odd_trace_three
      (e.x : ZMod 9) (n % 36) hrLt hrOdd hstateX
  have hmodTwelve :
      n % 36 % 12 = n % 12 :=
    Nat.mod_mod_of_dvd n (by decide : 12 ∣ 36)
  rcases hclass with ⟨ha, hr⟩ | ⟨ha, hr⟩
  · exact Or.inl ⟨by simpa [K, hK, e] using ha,
      by simpa [hmodTwelve] using hr⟩
  · exact Or.inr ⟨by simpa [K, hK, e] using ha,
      by simpa [hmodTwelve] using hr⟩

/-- Combining the leaf's `9 mod 64` fundamental coordinate with the exact
modulo-nine trace table leaves two CRT classes modulo `576`. -/
theorem Sm2LowerSquareAllocation.upperFundamentalX_and_exponent_classes
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) {n : Nat}
    (hnOdd : Odd n)
    (hpow :
      negativePellSquareSolution
          data.upper_negativePell.equation.symm =
        fundamentalPell data.upperKernel
            allocation.upper_pellKernel ^ n) :
    ((fundamentalX data.upperKernel
          allocation.upper_pellKernel % 576 = 201 ∧
        (n % 12 = 1 ∨ n % 12 = 11)) ∨
      (fundamentalX data.upperKernel
          allocation.upper_pellKernel % 576 = 393 ∧
        (n % 12 = 5 ∨ n % 12 = 7))) := by
  let K := data.upperKernel
  let hK : PellKernel K := allocation.upper_pellKernel
  let e := fundamentalPell K hK
  let a := fundamentalX K hK
  have h64 : a % 64 = 9 := by
    simpa [K, hK, a] using
      allocation.upperFundamentalX_mod_sixtyFour
  have hfundCast :
      (a : ZMod 9) = (e.x : ZMod 9) := by
    have h :=
      congrArg (fun z : Int => (z : ZMod 9))
        (fundamentalX_intCast K hK)
    simpa [a, e] using h
  have hcrtThree :
      a % 9 = 3 → a % 576 = 201 := by
    intro h9
    have hlt : a % 576 < 576 := Nat.mod_lt _ (by decide)
    have hm64 : a % 576 % 64 = 9 := by
      rw [Nat.mod_mod_of_dvd a (by decide : 64 ∣ 576)]
      exact h64
    have hm9 : a % 576 % 9 = 3 := by
      rw [Nat.mod_mod_of_dvd a (by decide : 9 ∣ 576)]
      exact h9
    omega
  have hcrtSix :
      a % 9 = 6 → a % 576 = 393 := by
    intro h9
    have hlt : a % 576 < 576 := Nat.mod_lt _ (by decide)
    have hm64 : a % 576 % 64 = 9 := by
      rw [Nat.mod_mod_of_dvd a (by decide : 64 ∣ 576)]
      exact h64
    have hm9 : a % 576 % 9 = 6 := by
      rw [Nat.mod_mod_of_dvd a (by decide : 9 ∣ 576)]
      exact h9
    omega
  have hclass :=
    allocation.upperNormOne_exponent_classes hnOdd hpow
  rcases hclass with ⟨ha, hnClass⟩ | ⟨ha, hnClass⟩
  · apply Or.inl
    have haNat : a % 9 = 3 := by
      apply (ZMod.natCast_eq_natCast_iff' a 3 9).mp
      exact hfundCast.trans (by simpa [K, hK, e] using ha)
    exact
      ⟨by simpa [K, hK, a] using hcrtThree haNat, hnClass⟩
  · apply Or.inr
    have haNat : a % 9 = 6 := by
      apply (ZMod.natCast_eq_natCast_iff' a 6 9).mp
      exact hfundCast.trans (by simpa [K, hK, e] using ha)
    exact
      ⟨by simpa [K, hK, a] using hcrtSix haNat, hnClass⟩

/-- The positive fundamental norm-minus-one point, represented in the
quadratic ring used to recover the unsquared source orbit. -/
def sm2UpperNegativeUnit (K u v : Nat) : ℤ√(K : Int) :=
  ⟨u, v⟩

/-- The actual upper negative-Pell source point at the retained centre. -/
def sm2UpperSourcePoint (K X W : Nat) : ℤ√(K : Int) :=
  ⟨X, W⟩

private theorem sm2UpperNegativeUnit_sq
    {K u v : Nat} (hK : PellKernel K)
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hreal : fundamentalX K hK = 2 * u ^ 2 + 1)
    (himag : fundamentalY K hK = 2 * u * v) :
    sm2UpperNegativeUnit K u v ^ 2 =
      ((fundamentalPell K hK : Pell.Solution₁ (K : Int)) :
        ℤ√(K : Int)) := by
  apply Zsqrtd.ext
  · simp only [sm2UpperNegativeUnit, pow_two, Zsqrtd.re_mul]
    change
      (u : Int) * u + K * (v : Int) * v =
        (fundamentalPell K hK).x
    rw [← fundamentalX_intCast K hK]
    norm_cast
    rw [hreal]
    nlinarith
  · simp only [sm2UpperNegativeUnit, pow_two, Zsqrtd.im_mul]
    change
      (u : Int) * v + (v : Int) * u =
        (fundamentalPell K hK).y
    rw [← fundamentalY_intCast K hK]
    norm_cast
    rw [himag]
    ring

private theorem sm2UpperSourcePoint_sq
    {K X W : Nat} (hPell : X ^ 2 + 1 = K * W ^ 2) :
    sm2UpperSourcePoint K X W ^ 2 =
      ((negativePellSquareSolution hPell :
        Pell.Solution₁ (K : Int)) : ℤ√(K : Int)) := by
  apply Zsqrtd.ext
  · simp [sm2UpperSourcePoint,
      negativePellSquareSolution, pow_two, Zsqrtd.re_mul]
    ring
  · simp [sm2UpperSourcePoint,
      negativePellSquareSolution, pow_two, Zsqrtd.im_mul]
    ring

private theorem sm2UpperNegativeUnit_pow_coordinates
    {K u v : Nat} (hK : PellKernel K)
    (hu : 0 < u) (hv : 0 < v) (n : Nat) :
    0 < (sm2UpperNegativeUnit K u v ^ n).re ∧
      0 ≤ (sm2UpperNegativeUnit K u v ^ n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases ih with ⟨hre, him⟩
      rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
      change
        0 <
            (sm2UpperNegativeUnit K u v ^ n).re * u +
              K *
                (sm2UpperNegativeUnit K u v ^ n).im * v ∧
          0 ≤
            (sm2UpperNegativeUnit K u v ^ n).re * v +
              (sm2UpperNegativeUnit K u v ^ n).im * u
      have hKPos : 0 < K := Nat.zero_lt_of_lt hK.1
      constructor <;> positivity

/-- Squaring the source loses no sign: positivity recovers the actual
negative-Pell point as the same power of the fundamental norm-minus-one
root. -/
theorem sm2UpperSourcePoint_eq_root_pow
    {K X W u v n : Nat} (hK : PellKernel K)
    (hX : 0 < X) (hu : 0 < u) (hv : 0 < v)
    (hPell : X ^ 2 + 1 = K * W ^ 2)
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hreal : fundamentalX K hK = 2 * u ^ 2 + 1)
    (himag : fundamentalY K hK = 2 * u * v)
    (hpow :
      negativePellSquareSolution hPell =
        fundamentalPell K hK ^ n) :
    sm2UpperSourcePoint K X W =
      sm2UpperNegativeUnit K u v ^ n := by
  letI : Zsqrtd.Nonsquare K := by
    constructor
    intro m hm
    apply pellKernel_not_isSquare_nat hK
    exact ⟨m, by simpa [pow_two] using hm⟩
  have hsquares :
      sm2UpperSourcePoint K X W ^ 2 =
        (sm2UpperNegativeUnit K u v ^ n) ^ 2 := by
    calc
      sm2UpperSourcePoint K X W ^ 2 =
          ((negativePellSquareSolution hPell :
            Pell.Solution₁ (K : Int)) : ℤ√(K : Int)) :=
        sm2UpperSourcePoint_sq hPell
      _ =
          ((fundamentalPell K hK ^ n :
            Pell.Solution₁ (K : Int)) : ℤ√(K : Int)) := by
        exact congrArg
          (fun z : Pell.Solution₁ (K : Int) =>
            (z : ℤ√(K : Int))) hpow
      _ =
          (((fundamentalPell K hK :
            Pell.Solution₁ (K : Int)) : ℤ√(K : Int)) ^ n) := by
        rfl
      _ = (sm2UpperNegativeUnit K u v ^ 2) ^ n := by
        rw [sm2UpperNegativeUnit_sq hK hnegative hreal himag]
      _ = sm2UpperNegativeUnit K u v ^ (2 * n) :=
        (pow_mul (sm2UpperNegativeUnit K u v) 2 n).symm
      _ = sm2UpperNegativeUnit K u v ^ (n * 2) := by
        rw [Nat.mul_comm]
      _ = (sm2UpperNegativeUnit K u v ^ n) ^ 2 :=
        pow_mul (sm2UpperNegativeUnit K u v) n 2
  rcases eq_or_eq_neg_of_sq_eq_sq
      (sm2UpperSourcePoint K X W)
      (sm2UpperNegativeUnit K u v ^ n) hsquares with heq | hnegativeEq
  · exact heq
  · have hre := congrArg Zsqrtd.re hnegativeEq
    have horbitRe :=
      (sm2UpperNegativeUnit_pow_coordinates hK hu hv n).1
    change (X : Int) =
      -(sm2UpperNegativeUnit K u v ^ n).re at hre
    omega

/-- Complete upper negative-Pell source orbit retained by one
`sm2LowerSquare` allocation.  Both the squared norm-one power and the
unsquared norm-minus-one point remain in the package. -/
structure Sm2LowerSquareUpperNormOneOrbit
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) where
  rootX : Nat
  rootY : Nat
  index : Nat
  rootX_pos : 0 < rootX
  rootY_pos : 0 < rootY
  root_equation :
    rootX ^ 2 + 1 = data.upperKernel * rootY ^ 2
  fundamentalX_eq :
    fundamentalX data.upperKernel allocation.upper_pellKernel =
      2 * rootX ^ 2 + 1
  fundamentalY_eq :
    fundamentalY data.upperKernel allocation.upper_pellKernel =
      2 * rootX * rootY
  index_odd : Odd index
  squared_source_power :
    negativePellSquareSolution
        data.upper_negativePell.equation.symm =
      fundamentalPell data.upperKernel
          allocation.upper_pellKernel ^ index
  source_point_power :
    sm2UpperSourcePoint data.upperKernel data.center
        (data.upperKernel * data.upperSquarePart) =
      sm2UpperNegativeUnit data.upperKernel rootX rootY ^ index
  normOne_real_coordinate :
    pellX data.upperKernel allocation.upper_pellKernel index =
      2 * data.center ^ 2 + 1
  normOne_ordinate :
    pellY data.upperKernel allocation.upper_pellKernel index =
      2 * data.center *
        (data.upperKernel * data.upperSquarePart)
  source_depth :
    ∃! t : Nat,
      index =
        pellRank data.upperKernel allocation.upper_pellKernel *
          (2 * t + 1)
  fundamental_residue_and_index_class :
    ((fundamentalX data.upperKernel
          allocation.upper_pellKernel % 576 = 201 ∧
        (index % 12 = 1 ∨ index % 12 = 11)) ∨
      (fundamentalX data.upperKernel
          allocation.upper_pellKernel % 576 = 393 ∧
        (index % 12 = 5 ∨ index % 12 = 7)))

namespace Sm2LowerSquareAllocation

/-- Every complete allocation has a complete upper source orbit. -/
theorem upperNormOneOrbit_nonempty
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nonempty (Sm2LowerSquareUpperNormOneOrbit allocation) := by
  let hK : PellKernel data.upperKernel :=
    allocation.upper_pellKernel
  have hKOdd : Odd data.upperKernel := by
    rw [Nat.odd_iff]
    have hTwentyFour := allocation.kernel_residues.2
    omega
  have hKTwo : 2 < data.upperKernel := by
    have hTwentyFour := allocation.kernel_residues.2
    have hle := Nat.mod_le data.upperKernel 24
    omega
  obtain
      ⟨u, v, huPos, hvPos, hroot, hfundX, hfundY⟩ :=
    allocation.exists_upper_fundamental_negativePell_root
  obtain
      ⟨n, hnOdd, hpow, hreal, himag, hdepth⟩ :=
    divisibleNegativePell_exists_normOne_depth
      hK hKOdd hKTwo data.upper_negativePell
  have hpow' :
      negativePellSquareSolution
          data.upper_negativePell.equation.symm =
        fundamentalPell data.upperKernel hK ^ n := by
    simpa [pellSolution] using hpow
  have hsourcePoint :
      sm2UpperSourcePoint data.upperKernel data.center
          (data.upperKernel * data.upperSquarePart) =
        sm2UpperNegativeUnit data.upperKernel u v ^ n :=
    sm2UpperSourcePoint_eq_root_pow
      hK (Nat.zero_lt_of_lt data.center_one_lt)
      huPos hvPos data.upper_negativePell.equation.symm
      hroot hfundX hfundY hpow'
  have hclasses :=
    allocation.upperFundamentalX_and_exponent_classes
      hnOdd hpow'
  exact
    ⟨{
      rootX := u
      rootY := v
      index := n
      rootX_pos := huPos
      rootY_pos := hvPos
      root_equation := hroot
      fundamentalX_eq := hfundX
      fundamentalY_eq := hfundY
      index_odd := hnOdd
      squared_source_power := by
        simpa [hK] using hpow'
      source_point_power := hsourcePoint
      normOne_real_coordinate := by
        simpa [hK] using hreal
      normOne_ordinate := by
        simpa [hK] using himag
      source_depth := by
        simpa [hK] using hdepth
      fundamental_residue_and_index_class := by
        simpa [hK] using hclasses
    }⟩

end Sm2LowerSquareAllocation

/-- The exact residual carrying both the lower norm-minus-two source orbit
and the upper norm-minus-one source orbit at one unchanged centre. -/
structure Sm2LowerSquareDoubleOrbitResidual
    (data : PairPellCounterexampleData) where
  lowerResidual : Sm2LowerSquareLowerOrbitResidual data
  upperOrbit :
    Nonempty
      (Sm2LowerSquareUpperNormOneOrbit
        lowerResidual.residual.allocation)

namespace Sm2LowerSquareLowerOrbitResidual

/-- Every lower-orbit residual canonically refines to the double-orbit
residual. -/
noncomputable def toDoubleOrbitResidual
    {data : PairPellCounterexampleData}
    (residual : Sm2LowerSquareLowerOrbitResidual data) :
    Sm2LowerSquareDoubleOrbitResidual data :=
  { lowerResidual := residual
    upperOrbit :=
      residual.residual.allocation.upperNormOneOrbit_nonempty }

end Sm2LowerSquareLowerOrbitResidual

/-- Exact source-equivalent compiler into the coupled lower/upper orbit
residual.  This is the final representation before a terminal obstruction;
it is not an emptiness theorem. -/
theorem sm2LowerSquareSource_iff_exists_doubleOrbitResidual
    (X : Nat) :
    Sm2LowerSquareSource X ↔
      ∃ data : PairPellCounterexampleData,
        data.pell.Represents X ∧
          Nonempty (Sm2LowerSquareDoubleOrbitResidual data) := by
  constructor
  · intro hsource
    obtain ⟨data, hrep, ⟨residual⟩⟩ :=
      (sm2LowerSquareSource_iff_exists_lowerOrbitResidual X).mp
        hsource
    exact
      ⟨data, hrep, ⟨residual.toDoubleOrbitResidual⟩⟩
  · rintro ⟨data, hrep, ⟨residual⟩⟩
    apply
      (sm2LowerSquareSource_iff_exists_lowerOrbitResidual X).mpr
    exact ⟨data, hrep, ⟨residual.lowerResidual⟩⟩

end Erdos364
