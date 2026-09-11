import Erdos364.SquareMiddle.Sm2LowerSquareUpperNormOneOrbit
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace Erdos364

open Pell
open scoped jacobiSym

/-!
# Exact upper source generator for the `sm2LowerSquare` leaf

The complete upper source orbit is normalized at its exact divisibility rank.
For the fundamental norm-minus-one point `eta` and
`R = pellRank K`, this module constructs

```text
gamma = eta^R = P + Q*sqrt(K)
```

and writes the retained source point as `gamma^(2*t+1)`.  The same-centre
square-predecessor condition forces `P = 2 mod 8`, the outer exponent to be
`1 mod 4`, and then exactly one of the two oriented phases

```text
2*P^2+1 = 201 mod 576,  2*t+1 = 1 mod 12,
2*P^2+1 = 393 mod 576,  2*t+1 = 5 mod 12.
```

The final lemmas expose checked nonsquare phase certificates.  They are
sufficient obstruction interfaces, not an assertion that every residual
generator has such a certificate.
-/

private theorem zsqrtd_real_dvd_odd_power
    (K P Q t : Nat) :
    (P : Int) ∣
      ((⟨P, Q⟩ : ℤ√(K : Int)) ^ (2 * t + 1)).re := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      obtain ⟨c, hc⟩ := ih
      rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by omega,
        pow_add, Zsqrtd.re_mul, pow_two,
        Zsqrtd.re_mul, Zsqrtd.im_mul]
      refine
        ⟨c * ((P : Int) * P + K * (Q : Int) * Q) +
            K *
              ((⟨P, Q⟩ : ℤ√(K : Int)) ^
                (2 * t + 1)).im * (2 * Q), ?_⟩
      change
        ((⟨P, Q⟩ : ℤ√(K : Int)) ^
              (2 * t + 1)).re *
              ((P : Int) * P + K * (Q : Int) * Q) +
            K *
              ((⟨P, Q⟩ : ℤ√(K : Int)) ^
                (2 * t + 1)).im *
              ((P : Int) * Q + Q * P) =
          (P : Int) *
            (c * ((P : Int) * P + K * (Q : Int) * Q) +
              K *
                ((⟨P, Q⟩ : ℤ√(K : Int)) ^
                  (2 * t + 1)).im * (2 * Q))
      rw [hc]
      ring

private theorem no_square_neg_one_of_mod_four_eq_three
    {m : Nat} (hm : m % 4 = 3) :
    ¬ IsSquare (-1 : ZMod m) := by
  have hjac : jacobiSym (-1 : Int) m = -1 := by
    rw [jacobiSym.at_neg_one
        ((Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hm)),
      ZMod.χ₄_nat_three_mod_four hm]
  have hns :=
    ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac
  simpa using hns

private theorem no_square_predecessor_of_mod_eight_eq_six
    {P y : Nat} (hP : P % 8 = 6)
    (hdiv : P ∣ y ^ 2 + 1) :
    False := by
  let m := P / 2
  have hPdecomp : P = 8 * (P / 8) + 6 := by
    have h := (Nat.mod_add_div P 8).symm
    rw [hP] at h
    omega
  have hm : m % 4 = 3 := by
    dsimp [m]
    rw [hPdecomp]
    omega
  have hmDvdP : m ∣ P := by
    dsimp [m]
    exact Nat.div_dvd_of_dvd (by
      rw [hPdecomp]
      omega)
  have hmDvd : m ∣ y ^ 2 + 1 := hmDvdP.trans hdiv
  have hzero :
      ((y ^ 2 + 1 : Nat) : ZMod m) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hmDvd
  have hsquare : (y : ZMod m) ^ 2 = -1 := by
    push_cast at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  apply no_square_neg_one_of_mod_four_eq_three hm
  exact ⟨(y : ZMod m), by simpa [pow_two] using hsquare.symm⟩

/-- Symbolic norm-minus-one power state modulo eight.  The second
component is the coefficient of the generator ordinate. -/
private def normMinusOnePowerStateModEight (p : ZMod 8) :
    Nat → ZMod 8 × ZMod 8
  | 0 => (1, 0)
  | n + 1 =>
      let s := normMinusOnePowerStateModEight p n
      (p * s.1 + (p ^ 2 + 1) * s.2, s.1 + p * s.2)

private theorem zsqrtd_pow_state_modEight
    {K : Nat} (P Q n : Nat)
    (hnegative : P ^ 2 + 1 = K * Q ^ 2) :
    ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).re : Int) : ZMod 8) =
        (normMinusOnePowerStateModEight (P : ZMod 8) n).1 ∧
      ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).im : Int) : ZMod 8) =
        (normMinusOnePowerStateModEight (P : ZMod 8) n).2 *
          (Q : ZMod 8) := by
  have hnorm :
      (K : ZMod 8) * (Q : ZMod 8) ^ 2 =
        (P : ZMod 8) ^ 2 + 1 := by
    have h := congrArg (fun z : Nat => (z : ZMod 8)) hnegative
    push_cast at h
    exact h.symm
  induction n with
  | zero =>
      simp [normMinusOnePowerStateModEight]
  | succ n ih =>
      constructor
      · rw [pow_succ, Zsqrtd.re_mul]
        push_cast
        rw [ih.1, ih.2]
        simp only [normMinusOnePowerStateModEight]
        linear_combination
          (normMinusOnePowerStateModEight
            (P : ZMod 8) n).2 * hnorm
      · rw [pow_succ, Zsqrtd.im_mul]
        push_cast
        rw [ih.1, ih.2]
        simp only [normMinusOnePowerStateModEight]
        ring

private theorem normMinusOnePowerStateModEight_two_four :
    normMinusOnePowerStateModEight (2 : ZMod 8) 4 = (1, 0) := by
  decide

private theorem zsqrtd_pow_modEight_periodic_of_real_two
    {K P Q : Nat} (hP : P % 8 = 2)
    (hnegative : P ^ 2 + 1 = K * Q ^ 2) :
    Function.Periodic
      (fun n : Nat =>
        (((((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).re : Int) : ZMod 8),
          ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).im : Int) : ZMod 8))) 4 := by
  have hPcast : (P : ZMod 8) = 2 :=
    (ZMod.natCast_eq_natCast_iff' P 2 8).mpr hP
  have hstate := zsqrtd_pow_state_modEight P Q 4 hnegative
  rw [hPcast, normMinusOnePowerStateModEight_two_four] at hstate
  have hfour :
      (((((⟨P, Q⟩ : ℤ√(K : Int)) ^ 4).re : Int) : ZMod 8) = 1) ∧
        (((((⟨P, Q⟩ : ℤ√(K : Int)) ^ 4).im : Int) : ZMod 8) = 0) := by
    simpa using hstate
  intro n
  apply Prod.ext
  · change
      (((((⟨P, Q⟩ : ℤ√(K : Int)) ^ (n + 4)).re : Int) : ZMod 8) =
        ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).re : Int) : ZMod 8))
    rw [pow_add, Zsqrtd.re_mul]
    push_cast
    rw [hfour.1, hfour.2]
    ring
  · change
      (((((⟨P, Q⟩ : ℤ√(K : Int)) ^ (n + 4)).im : Int) : ZMod 8) =
        ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).im : Int) : ZMod 8))
    rw [pow_add, Zsqrtd.im_mul]
    push_cast
    rw [hfour.1, hfour.2]
    ring

private theorem odd_power_phase_mod_four_of_real_two
    {K P Q h X : Nat}
    (hP : P % 8 = 2)
    (hnegative : P ^ 2 + 1 = K * Q ^ 2)
    (hhOdd : Odd h) (hX : X % 8 = 2)
    (hsource :
      (X : Int) =
        ((⟨P, Q⟩ : ℤ√(K : Int)) ^ h).re) :
    h % 4 = 1 := by
  have hperiod :=
    (zsqrtd_pow_modEight_periodic_of_real_two hP hnegative).map_mod_nat h
  have hperiodRe := congrArg Prod.fst hperiod
  simp only at hperiodRe
  have hsourceCast :=
    congrArg (fun z : Int => (z : ZMod 8)) hsource
  have hXcast : (X : ZMod 8) = 2 :=
    (ZMod.natCast_eq_natCast_iff' X 2 8).mpr hX
  have hpowRe :
      ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ (h % 4)).re : Int) :
          ZMod 8) = 2 := by
    exact hperiodRe.trans (hsourceCast.symm.trans hXcast)
  have hstate :=
    zsqrtd_pow_state_modEight P Q (h % 4) hnegative
  have hPcast : (P : ZMod 8) = 2 :=
    (ZMod.natCast_eq_natCast_iff' P 2 8).mpr hP
  have hstateRe :
      (normMinusOnePowerStateModEight
        (2 : ZMod 8) (h % 4)).1 = 2 := by
    simpa only [hPcast] using hstate.1.symm.trans hpowRe
  have hhTwo : h % 2 = 1 := Nat.odd_iff.mp hhOdd
  have hrOdd : h % 4 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd h (by decide : 2 ∣ 4)]
    exact hhTwo
  have hrLt : h % 4 < 4 := Nat.mod_lt _ (by decide)
  have hclass :
      ∀ r : Fin 4,
        r.val % 2 = 1 →
          (normMinusOnePowerStateModEight
            (2 : ZMod 8) r.val).1 = 2 →
          r.val = 1 := by
    decide
  exact hclass ⟨h % 4, hrLt⟩ hrOdd hstateRe

private theorem sm2UpperNegativeUnit_pow_succ_coordinates
    {K u v : Nat} (hK : PellKernel K)
    (hu : 0 < u) (hv : 0 < v) (n : Nat) :
    0 < (sm2UpperNegativeUnit K u v ^ (n + 1)).re ∧
      0 < (sm2UpperNegativeUnit K u v ^ (n + 1)).im := by
  induction n with
  | zero =>
      simpa [sm2UpperNegativeUnit] using And.intro hu hv
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        pow_add, Zsqrtd.re_mul, Zsqrtd.im_mul]
      simp only [pow_one]
      change
        0 <
            (sm2UpperNegativeUnit K u v ^ (n + 1)).re * u +
              K *
                (sm2UpperNegativeUnit K u v ^ (n + 1)).im * v ∧
          0 <
            (sm2UpperNegativeUnit K u v ^ (n + 1)).re * v +
              (sm2UpperNegativeUnit K u v ^ (n + 1)).im * u
      have hKPos : 0 < K := Nat.zero_lt_of_lt hK.1
      have hKInt : (0 : Int) < K := by exact_mod_cast hKPos
      have huInt : (0 : Int) < u := by exact_mod_cast hu
      have hvInt : (0 : Int) < v := by exact_mod_cast hv
      constructor
      · exact
          add_pos (mul_pos ih.1 huInt)
            (mul_pos (mul_pos hKInt ih.2) hvInt)
      · exact
          add_pos (mul_pos ih.1 hvInt) (mul_pos ih.2 huInt)

private theorem negativePell_real_mod_four_local
    {K P Q : Nat} (hK : K % 8 = 5)
    (heq : P ^ 2 + 1 = K * Q ^ 2) :
    P % 4 = 2 := by
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
  rcases hclass (P : ZMod 8) (Q : ZMod 8) hcast with hP2 | hP6
  · have hP8 : P % 8 = 2 :=
      (ZMod.natCast_eq_natCast_iff' P 2 8).mp hP2
    have hm := Nat.mod_mod_of_dvd P (by decide : 4 ∣ 8)
    rw [hP8] at hm
    omega
  · have hP8 : P % 8 = 6 :=
      (ZMod.natCast_eq_natCast_iff' P 6 8).mp hP6
    have hm := Nat.mod_mod_of_dvd P (by decide : 4 ∣ 8)
    rw [hP8] at hm
    omega

/-- A norm-minus-one real coordinate over a kernel congruent to five
modulo eight is two modulo eight as soon as it divides a retained square
successor.  The other Pell-compatible class, six modulo eight, would make
minus one a square modulo an integer congruent to three modulo four. -/
theorem negativePell_real_mod_eight_two_of_dvd_square_add_one
    {K P Q y : Nat} (hK : K % 8 = 5)
    (hnegative : P ^ 2 + 1 = K * Q ^ 2)
    (hdiv : P ∣ y ^ 2 + 1) :
    P % 8 = 2 := by
  have hP4 : P % 4 = 2 :=
    negativePell_real_mod_four_local hK hnegative
  have hmod : P % 8 % 4 = P % 4 :=
    Nat.mod_mod_of_dvd P (by decide : 4 ∣ 8)
  have hlt : P % 8 < 8 := Nat.mod_lt _ (by decide)
  by_contra hnotTwo
  have hP8 : P % 8 = 6 := by
    rw [hP4] at hmod
    omega
  exact no_square_predecessor_of_mod_eight_eq_six hP8 hdiv

private theorem kernel_coprime_two_mul_negativePell_real
    {K P Q : Nat} (hKOdd : Odd K)
    (hnegative : P ^ 2 + 1 = K * Q ^ 2) :
    K.Coprime (2 * P) := by
  have hKP : K.Coprime P := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hdivP : K.gcd P ∣ P ^ 2 := by
      simpa [pow_two] using
        dvd_mul_of_dvd_left (Nat.gcd_dvd_right K P) P
    have hdivSum : K.gcd P ∣ P ^ 2 + 1 := by
      rw [hnegative]
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left K P) (Q ^ 2)
    exact
      Nat.eq_one_of_dvd_one
        ((Nat.dvd_add_iff_right hdivP).mpr hdivSum)
  exact
    (Nat.coprime_two_right.mpr hKOdd).mul_right hKP

theorem Sm2LowerSquareUpperNormOneOrbit.exists_source_generator
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (orbit : Sm2LowerSquareUpperNormOneOrbit allocation) :
    ∃ P Q t : Nat,
      0 < P ∧
        0 < Q ∧
          sm2UpperNegativeUnit
                data.upperKernel orbit.rootX orbit.rootY ^
              pellRank data.upperKernel allocation.upper_pellKernel =
            (⟨P, Q⟩ : ℤ√(data.upperKernel : Int)) ∧
          orbit.index =
            pellRank data.upperKernel allocation.upper_pellKernel *
              (2 * t + 1) ∧
          P ^ 2 + 1 = data.upperKernel * Q ^ 2 ∧
          sm2UpperSourcePoint data.upperKernel data.center
                (data.upperKernel * data.upperSquarePart) =
            (⟨P, Q⟩ : ℤ√(data.upperKernel : Int)) ^
              (2 * t + 1) ∧
          P ∣ data.center ∧
          P ∣ allocation.y ^ 2 + 1 ∧
          P % 8 = 2 ∧
          (2 * t + 1) % 4 = 1 := by
  let K := data.upperKernel
  let hK : PellKernel K := allocation.upper_pellKernel
  let eta : ℤ√(K : Int) :=
    sm2UpperNegativeUnit K orbit.rootX orbit.rootY
  let R := pellRank K hK
  let gamma : ℤ√(K : Int) := eta ^ R
  have hKOdd : Odd K := by
    rw [Nat.odd_iff]
    have hTwentyFour := allocation.kernel_residues.2
    omega
  have hROdd : Odd R := by
    simpa [R] using pellRank_odd_of_kernel_odd K hK hKOdd
  have hRPos : 0 < R := by
    simpa [R] using pellRank_pos K hK
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hRPos)
  have hgammaCoordinates :=
    sm2UpperNegativeUnit_pow_succ_coordinates
      hK orbit.rootX_pos orbit.rootY_pos r
  have hgammaRePos : 0 < gamma.re := by
    simpa [gamma, R, hr] using hgammaCoordinates.1
  have hgammaImPos : 0 < gamma.im := by
    simpa [gamma, R, hr] using hgammaCoordinates.2
  let P := Int.toNat gamma.re
  let Q := Int.toNat gamma.im
  have hPcast : (P : Int) = gamma.re := by
    exact Int.toNat_of_nonneg hgammaRePos.le
  have hQcast : (Q : Int) = gamma.im := by
    exact Int.toNat_of_nonneg hgammaImPos.le
  have hPPos : 0 < P := by
    rw [← hPcast] at hgammaRePos
    exact_mod_cast hgammaRePos
  have hQPos : 0 < Q := by
    rw [← hQcast] at hgammaImPos
    exact_mod_cast hgammaImPos
  have hgammaEq :
      gamma = (⟨P, Q⟩ : ℤ√(K : Int)) := by
    apply Zsqrtd.ext
    · exact hPcast.symm
    · exact hQcast.symm
  have hetaNorm : Zsqrtd.norm eta = -1 := by
    have hroot := orbit.root_equation
    have hrootInt :
        (orbit.rootX : Int) ^ 2 + 1 =
          K * (orbit.rootY : Int) ^ 2 := by
      exact_mod_cast hroot
    dsimp [eta, sm2UpperNegativeUnit]
    simp only [Zsqrtd.norm_def]
    nlinarith
  have hgammaNorm : Zsqrtd.norm gamma = -1 := by
    calc
      Zsqrtd.norm gamma = Zsqrtd.norm eta ^ R := by
        exact map_pow Zsqrtd.normMonoidHom eta R
      _ = (-1 : Int) ^ R := by rw [hetaNorm]
      _ = -1 :=
        (neg_one_pow_eq_neg_one_iff_odd
          (by norm_num : (-1 : Int) ≠ 1)).mpr hROdd
  have hnegative : P ^ 2 + 1 = K * Q ^ 2 := by
    have hnorm := hgammaNorm
    rw [hgammaEq] at hnorm
    have hnorm' :
        (P : Int) ^ 2 - K * (Q : Int) ^ 2 = -1 := by
      simpa [Zsqrtd.norm_def, pow_two, mul_assoc] using hnorm
    have hnegativeInt :
        (P : Int) ^ 2 + 1 = K * (Q : Int) ^ 2 := by
      nlinarith [hnorm']
    exact_mod_cast hnegativeInt
  obtain ⟨t, ht, _htUnique⟩ := orbit.source_depth
  have hsource :
      sm2UpperSourcePoint K data.center
            (K * data.upperSquarePart) =
        (⟨P, Q⟩ : ℤ√(K : Int)) ^ (2 * t + 1) := by
    calc
      sm2UpperSourcePoint K data.center
            (K * data.upperSquarePart) =
          eta ^ orbit.index := by
        simpa [K, eta] using orbit.source_point_power
      _ = eta ^ (R * (2 * t + 1)) := by rw [ht]
      _ = (eta ^ R) ^ (2 * t + 1) :=
        pow_mul eta R (2 * t + 1)
      _ = gamma ^ (2 * t + 1) := by rfl
      _ = (⟨P, Q⟩ : ℤ√(K : Int)) ^ (2 * t + 1) := by
        rw [hgammaEq]
  have hPdCenterInt :
      (P : Int) ∣ (data.center : Int) := by
    have hdvd :=
      zsqrtd_real_dvd_odd_power K P Q t
    have hsourceRe := congrArg Zsqrtd.re hsource
    change
      (data.center : Int) =
        ((⟨P, Q⟩ : ℤ√(K : Int)) ^ (2 * t + 1)).re
      at hsourceRe
    rwa [← hsourceRe] at hdvd
  have hPdCenter : P ∣ data.center := by
    exact_mod_cast hPdCenterInt
  have hPdPredecessor : P ∣ allocation.y ^ 2 + 1 := by
    simpa [allocation.center_eq] using hPdCenter
  have hKEight : K % 8 = 5 := by
    have hTwentyFour := allocation.kernel_residues.2
    have hm := Nat.mod_mod_of_dvd K (by decide : 8 ∣ 24)
    rw [hTwentyFour] at hm
    omega
  have hPFour : P % 4 = 2 :=
    negativePell_real_mod_four_local hKEight hnegative
  have hPcases : P % 8 = 2 ∨ P % 8 = 6 := by
    have hm := Nat.mod_mod_of_dvd P (by decide : 4 ∣ 8)
    have hlt := Nat.mod_lt P (by decide : 0 < 8)
    omega
  have hPEight : P % 8 = 2 := by
    rcases hPcases with hP2 | hP6
    · exact hP2
    · exact
        (no_square_predecessor_of_mod_eight_eq_six
          hP6 hPdPredecessor).elim
  have hphaseFour :
      (2 * t + 1) % 4 = 1 := by
    have hsourceRe := congrArg Zsqrtd.re hsource
    change
      (data.center : Int) =
        ((⟨P, Q⟩ : ℤ√(K : Int)) ^ (2 * t + 1)).re
      at hsourceRe
    exact
      odd_power_phase_mod_four_of_real_two
        hPEight hnegative (odd_two_mul_add_one t)
        allocation.center_mod_eight hsourceRe
  exact
    ⟨P, Q, t, hPPos, hQPos,
      by simpa [K, hK, eta, R, gamma] using hgammaEq,
      by simpa [R] using ht,
      by simpa [K] using hnegative,
      by simpa [K] using hsource,
      hPdCenter, hPdPredecessor, hPEight, hphaseFour⟩

private theorem normOnePowerStateModNine_thirtySix_local (a : ZMod 9) :
    normOnePowerStateModNine a 36 = (1, 0) := by
  set_option maxRecDepth 10000 in
    fin_cases a <;> decide

private theorem pellSolution_pow_state_modNine_local
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

private theorem pellSolution_pow_modNine_periodic_local
    {K : Nat} (e : Pell.Solution₁ (K : Int)) :
    Function.Periodic
      (fun n : Nat =>
        (((e ^ n).x : ZMod 9), ((e ^ n).y : ZMod 9))) 36 := by
  have hstate := pellSolution_pow_state_modNine_local e 36
  rw [normOnePowerStateModNine_thirtySix_local] at hstate
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

private theorem normOnePowerStateModNine_classification_table_local :
    ∀ (a : ZMod 9) (r : Fin 36),
      r.1 % 2 = 1 →
        (normOnePowerStateModNine a r.1).1 = 3 →
          (a = 3 ∧ (r.1 % 12 = 1 ∨ r.1 % 12 = 11)) ∨
            (a = 6 ∧ (r.1 % 12 = 5 ∨ r.1 % 12 = 7)) := by
  decide

private theorem normOneGenerator_phase_classes_of_trace_three
    {K h : Nat} (e : Pell.Solution₁ (K : Int))
    (hhOdd : Odd h)
    (htrace : ((e ^ h).x : ZMod 9) = 3) :
    (((e.x : ZMod 9) = 3 ∧
        (h % 12 = 1 ∨ h % 12 = 11)) ∨
      ((e.x : ZMod 9) = 6 ∧
        (h % 12 = 5 ∨ h % 12 = 7))) := by
  have hperiod :=
    (pellSolution_pow_modNine_periodic_local e).map_mod_nat h
  have hperiodX := congrArg Prod.fst hperiod
  simp only at hperiodX
  have hstate := pellSolution_pow_state_modNine_local e (h % 36)
  have hstateX :
      (normOnePowerStateModNine
        (e.x : ZMod 9) (h % 36)).1 = 3 := by
    calc
      (normOnePowerStateModNine
          (e.x : ZMod 9) (h % 36)).1 =
          ((e ^ (h % 36)).x : ZMod 9) := hstate.1.symm
      _ = ((e ^ h).x : ZMod 9) := hperiodX
      _ = 3 := htrace
  have hhTwo : h % 2 = 1 := Nat.odd_iff.mp hhOdd
  have hrOdd : h % 36 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd h (by decide : 2 ∣ 36)]
    exact hhTwo
  have hrLt : h % 36 < 36 := Nat.mod_lt _ (by decide)
  have hclass :=
    normOnePowerStateModNine_classification_table_local
      (e.x : ZMod 9) ⟨h % 36, hrLt⟩ hrOdd hstateX
  have hmodTwelve :
      h % 36 % 12 = h % 12 :=
    Nat.mod_mod_of_dvd h (by decide : 12 ∣ 36)
  rcases hclass with ⟨ha, hr⟩ | ⟨ha, hr⟩
  · exact Or.inl ⟨ha, by simpa [hmodTwelve] using hr⟩
  · exact Or.inr ⟨ha, by simpa [hmodTwelve] using hr⟩

private theorem twice_square_add_one_mod_sixtyFour_local
    {P : Nat} (hP : P % 8 = 2) :
    (2 * P ^ 2 + 1) % 64 = 9 := by
  have hPEq : P = 8 * (P / 8) + 2 := by
    have hdiv := (Nat.mod_add_div P 8).symm
    rw [hP] at hdiv
    omega
  apply (ZMod.natCast_eq_natCast_iff' _ 9 64).mp
  have hPCast :
      (P : ZMod 64) =
        (8 : ZMod 64) * ((P / 8 : Nat) : ZMod 64) + 2 := by
    have hcast :=
      congrArg (fun n : Nat => (n : ZMod 64)) hPEq
    push_cast at hcast
    exact hcast
  push_cast
  rw [hPCast]
  ring_nf
  rw [show (64 : ZMod 64) = 0 by decide,
    show (128 : ZMod 64) = 0 by decide]
  ring

private theorem sm2UpperNegativeUnit_sq_local
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

private theorem negativePellSquare_eq_rankPower
    {K P Q u v R : Nat} (hK : PellKernel K)
    (hnegative : P ^ 2 + 1 = K * Q ^ 2)
    (hroot : u ^ 2 + 1 = K * v ^ 2)
    (hreal : fundamentalX K hK = 2 * u ^ 2 + 1)
    (himag : fundamentalY K hK = 2 * u * v)
    (hgenerator :
      sm2UpperNegativeUnit K u v ^ R =
        (⟨P, Q⟩ : ℤ√(K : Int))) :
    negativePellSquareSolution hnegative =
      pellSolution K hK R := by
  have hgammaSq :
      (⟨P, Q⟩ : ℤ√(K : Int)) ^ 2 =
        ((pellSolution K hK R :
          Pell.Solution₁ (K : Int)) : ℤ√(K : Int)) := by
    calc
      (⟨P, Q⟩ : ℤ√(K : Int)) ^ 2 =
          (sm2UpperNegativeUnit K u v ^ R) ^ 2 := by
        rw [hgenerator]
      _ = sm2UpperNegativeUnit K u v ^ (R * 2) :=
        (pow_mul (sm2UpperNegativeUnit K u v) R 2).symm
      _ = sm2UpperNegativeUnit K u v ^ (2 * R) := by
        rw [Nat.mul_comm]
      _ = (sm2UpperNegativeUnit K u v ^ 2) ^ R :=
        pow_mul (sm2UpperNegativeUnit K u v) 2 R
      _ =
          (((fundamentalPell K hK :
            Pell.Solution₁ (K : Int)) : ℤ√(K : Int)) ^ R) := by
        rw [sm2UpperNegativeUnit_sq_local
          hK hroot hreal himag]
      _ =
          ((pellSolution K hK R :
            Pell.Solution₁ (K : Int)) : ℤ√(K : Int)) := by
        rfl
  apply Pell.Solution₁.ext
  · have hre := congrArg Zsqrtd.re hgammaSq
    rw [pow_two, Zsqrtd.re_mul] at hre
    simp only [negativePellSquareSolution, Pell.Solution₁.x_mk]
    change
      (P : Int) ^ 2 + K * (Q : Int) ^ 2 =
        (((pellSolution K hK R :
          Pell.Solution₁ (K : Int)) : ℤ√(K : Int))).re
    rw [← hre]
    ring
  · have him := congrArg Zsqrtd.im hgammaSq
    rw [pow_two, Zsqrtd.im_mul] at him
    simp only [negativePellSquareSolution, Pell.Solution₁.y_mk]
    change
      2 * (P : Int) * Q =
        (((pellSolution K hK R :
          Pell.Solution₁ (K : Int)) : ℤ√(K : Int))).im
    rw [← him]
    ring

/-- The source-depth generator has one of exactly two oriented CRT phases.
The outer source exponent is `1 mod 12` in the `201 mod 576` generator
class and `5 mod 12` in the `393 mod 576` generator class. -/
theorem Sm2LowerSquareUpperNormOneOrbit.exists_source_generator_phase
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (orbit : Sm2LowerSquareUpperNormOneOrbit allocation) :
    ∃ P Q t : Nat,
      0 < P ∧
        0 < Q ∧
          sm2UpperNegativeUnit
                data.upperKernel orbit.rootX orbit.rootY ^
              pellRank data.upperKernel allocation.upper_pellKernel =
            (⟨P, Q⟩ : ℤ√(data.upperKernel : Int)) ∧
          orbit.index =
            pellRank data.upperKernel allocation.upper_pellKernel *
              (2 * t + 1) ∧
          P ^ 2 + 1 = data.upperKernel * Q ^ 2 ∧
          sm2UpperSourcePoint data.upperKernel data.center
                (data.upperKernel * data.upperSquarePart) =
            (⟨P, Q⟩ : ℤ√(data.upperKernel : Int)) ^
              (2 * t + 1) ∧
          P ∣ data.center ∧
          P ∣ allocation.y ^ 2 + 1 ∧
          P % 8 = 2 ∧
          (2 * t + 1) % 4 = 1 ∧
          data.upperKernel ∣ Q ∧
          (((2 * P ^ 2 + 1) % 576 = 201 ∧
              (2 * t + 1) % 12 = 1) ∨
            ((2 * P ^ 2 + 1) % 576 = 393 ∧
              (2 * t + 1) % 12 = 5)) := by
  obtain
      ⟨P, Q, t, hPPos, hQPos, hgenerator, hdepth, hnegative,
        hsource, hPdCenter, hPdPredecessor, hPEight, hphaseFour⟩ :=
    orbit.exists_source_generator
  refine
    ⟨P, Q, t, hPPos, hQPos, hgenerator, hdepth, hnegative,
      hsource, hPdCenter, hPdPredecessor, hPEight, hphaseFour, ?_⟩
  let K := data.upperKernel
  let hK : PellKernel K := allocation.upper_pellKernel
  let R := pellRank K hK
  let h := 2 * t + 1
  let e : Pell.Solution₁ (K : Int) := pellSolution K hK R
  have ht : orbit.index = R * h := by
    simpa [K, hK, R, h] using hdepth
  have hpowRank :
      negativePellSquareSolution
          data.upper_negativePell.equation.symm =
        e ^ h := by
    calc
      negativePellSquareSolution
          data.upper_negativePell.equation.symm =
          fundamentalPell K hK ^ orbit.index := by
            simpa [K, hK] using orbit.squared_source_power
      _ = fundamentalPell K hK ^ (R * h) := by rw [ht]
      _ = (fundamentalPell K hK ^ R) ^ h := pow_mul _ R h
      _ = e ^ h := by rfl
  have hcenterSqModNine : data.center ^ 2 % 9 = 1 := by
    have hThirtySix := allocation.middle_mod_thirtySix
    have hmod :=
      Nat.mod_mod_of_dvd (data.center ^ 2)
        (by decide : 9 ∣ 36)
    rw [hThirtySix] at hmod
    omega
  have hcenterSqCast :
      ((data.center ^ 2 : Nat) : ZMod 9) = 1 := by
    exact
      (ZMod.natCast_eq_natCast_iff'
        (data.center ^ 2) 1 9).mpr hcenterSqModNine
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
  have htraceSource :
      ((negativePellSquareSolution
        data.upper_negativePell.equation.symm).x : ZMod 9) = 3 := by
    rw [hzXInt]
    push_cast
    rw [show ((data.center : ZMod 9) ^ 2) =
        ((data.center ^ 2 : Nat) : ZMod 9) by simp]
    rw [hcenterSqCast]
    decide
  have htrace : ((e ^ h).x : ZMod 9) = 3 := by
    rw [← hpowRank]
    exact htraceSource
  have hhOdd : Odd h := by
    simp [h]
  have hclasses :=
    normOneGenerator_phase_classes_of_trace_three e hhOdd htrace
  have hrankPower :
      negativePellSquareSolution hnegative =
        pellSolution K hK R := by
    exact
      negativePellSquare_eq_rankPower hK hnegative
        orbit.root_equation orbit.fundamentalX_eq
        orbit.fundamentalY_eq
        (by simpa [K, hK, R] using hgenerator)
  have hcoordinates :=
    negativePellSquareSolution_pellCoordinates
      hK hnegative R hrankPower
  have hKOdd : Odd K := by
    rw [Nat.odd_iff]
    have hTwentyFour := allocation.kernel_residues.2
    omega
  have hKDivTwoPQ : K ∣ (2 * P) * Q := by
    have hdiv :
        K ∣ pellY K hK R :=
      (D_dvd_pellY_iff_rank_dvd_index K hK R).mpr dvd_rfl
    rw [hcoordinates.2] at hdiv
    simpa [mul_assoc] using hdiv
  have hKDivQ : K ∣ Q :=
    (kernel_coprime_two_mul_negativePell_real
      hKOdd hnegative).dvd_of_dvd_mul_left hKDivTwoPQ
  refine ⟨by simpa [K] using hKDivQ, ?_⟩
  let C := 2 * P ^ 2 + 1
  have hCEq : pellX K hK R = C := by
    simpa [C] using hcoordinates.1
  have hC64 : C % 64 = 9 := by
    simpa [C] using
      twice_square_add_one_mod_sixtyFour_local hPEight
  have hPellCast :
      (C : ZMod 9) = (e.x : ZMod 9) := by
    have hcast :=
      congrArg (fun z : Int => (z : ZMod 9))
        (pellX_intCast K hK R)
    calc
      (C : ZMod 9) = (pellX K hK R : ZMod 9) := by rw [hCEq]
      _ = (e.x : ZMod 9) := by simpa [e] using hcast
  have hcrtThree :
      C % 9 = 3 → C % 576 = 201 := by
    intro h9
    have hlt : C % 576 < 576 := Nat.mod_lt _ (by decide)
    have hm64 : C % 576 % 64 = 9 := by
      rw [Nat.mod_mod_of_dvd C (by decide : 64 ∣ 576)]
      exact hC64
    have hm9 : C % 576 % 9 = 3 := by
      rw [Nat.mod_mod_of_dvd C (by decide : 9 ∣ 576)]
      exact h9
    omega
  have hcrtSix :
      C % 9 = 6 → C % 576 = 393 := by
    intro h9
    have hlt : C % 576 < 576 := Nat.mod_lt _ (by decide)
    have hm64 : C % 576 % 64 = 9 := by
      rw [Nat.mod_mod_of_dvd C (by decide : 64 ∣ 576)]
      exact hC64
    have hm9 : C % 576 % 9 = 6 := by
      rw [Nat.mod_mod_of_dvd C (by decide : 9 ∣ 576)]
      exact h9
    omega
  have hmodFourTwelve :
      h % 12 % 4 = h % 4 :=
    Nat.mod_mod_of_dvd h (by decide : 4 ∣ 12)
  have hhFour : h % 4 = 1 := by
    simpa [h] using hphaseFour
  rcases hclasses with ⟨ha, hh⟩ | ⟨ha, hh⟩
  · have hC9 : C % 9 = 3 := by
      apply (ZMod.natCast_eq_natCast_iff' C 3 9).mp
      exact hPellCast.trans ha
    have hhOne : h % 12 = 1 := by
      rcases hh with hhOne | hhEleven
      · exact hhOne
      · rw [hhEleven, hhFour] at hmodFourTwelve
        omega
    exact Or.inl
      ⟨by simpa [C] using hcrtThree hC9,
        by simpa [h] using hhOne⟩
  · have hC9 : C % 9 = 6 := by
      apply (ZMod.natCast_eq_natCast_iff' C 6 9).mp
      exact hPellCast.trans ha
    have hhFive : h % 12 = 5 := by
      rcases hh with hhFive | hhSeven
      · exact hhFive
      · rw [hhSeven, hhFour] at hmodFourTwelve
        omega
    exact Or.inr
      ⟨by simpa [C] using hcrtSix hC9,
        by simpa [h] using hhFive⟩

/-- Typed exact source-depth generator for one complete
`sm2LowerSquare` upper orbit.  It retains the original orbit and packages the
rank-normalized norm-minus-one generator together with the corrected oriented
phase. -/
structure Sm2LowerSquareUpperSourceGenerator
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) where
  upperOrbit : Sm2LowerSquareUpperNormOneOrbit allocation
  real : Nat
  ordinate : Nat
  outerIndex : Nat
  real_pos : 0 < real
  ordinate_pos : 0 < ordinate
  generator_power :
    sm2UpperNegativeUnit data.upperKernel
          upperOrbit.rootX upperOrbit.rootY ^
        pellRank data.upperKernel allocation.upper_pellKernel =
      (⟨real, ordinate⟩ : ℤ√(data.upperKernel : Int))
  total_index :
    upperOrbit.index =
      pellRank data.upperKernel allocation.upper_pellKernel *
        (2 * outerIndex + 1)
  negative_equation :
    real ^ 2 + 1 = data.upperKernel * ordinate ^ 2
  source_power :
    sm2UpperSourcePoint data.upperKernel data.center
          (data.upperKernel * data.upperSquarePart) =
      (⟨real, ordinate⟩ : ℤ√(data.upperKernel : Int)) ^
        (2 * outerIndex + 1)
  real_dvd_center : real ∣ data.center
  real_dvd_predecessor : real ∣ allocation.y ^ 2 + 1
  real_mod_eight : real % 8 = 2
  outer_phase_mod_four : (2 * outerIndex + 1) % 4 = 1
  kernel_dvd_ordinate : data.upperKernel ∣ ordinate
  oriented_phase :
    (((2 * real ^ 2 + 1) % 576 = 201 ∧
        (2 * outerIndex + 1) % 12 = 1) ∨
      ((2 * real ^ 2 + 1) % 576 = 393 ∧
        (2 * outerIndex + 1) % 12 = 5))

namespace Sm2LowerSquareUpperNormOneOrbit

/-- The existential phase compiler packaged as one exact typed generator. -/
theorem sourceGenerator_nonempty
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (orbit : Sm2LowerSquareUpperNormOneOrbit allocation) :
    Nonempty (Sm2LowerSquareUpperSourceGenerator allocation) := by
  obtain
      ⟨P, Q, t, hP, hQ, hgenerator, hindex, hnegative, hsource,
        hcenter, hpredecessor, hmodEight, hmodFour, hkernel, hphase⟩ :=
    orbit.exists_source_generator_phase
  exact
    ⟨{
      upperOrbit := orbit
      real := P
      ordinate := Q
      outerIndex := t
      real_pos := hP
      ordinate_pos := hQ
      generator_power := hgenerator
      total_index := hindex
      negative_equation := hnegative
      source_power := hsource
      real_dvd_center := hcenter
      real_dvd_predecessor := hpredecessor
      real_mod_eight := hmodEight
      outer_phase_mod_four := hmodFour
      kernel_dvd_ordinate := hkernel
      oriented_phase := hphase
    }⟩

end Sm2LowerSquareUpperNormOneOrbit

namespace Sm2LowerSquareAllocation

/-- Every canonical leaf allocation has its exact source-depth generator. -/
theorem upperSourceGenerator_nonempty
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nonempty (Sm2LowerSquareUpperSourceGenerator allocation) := by
  obtain ⟨orbit⟩ := allocation.upperNormOneOrbit_nonempty
  exact orbit.sourceGenerator_nonempty

end Sm2LowerSquareAllocation

/-- A complete oriented state at one period gives periodicity of every
subsequent quadratic-ring power modulo the same modulus. -/
private theorem zsqrtd_pow_mod_periodic_of_state
    {K q period : Nat} (g : ℤ√(K : Int))
    (hre :
      (((g ^ period).re : Int) : ZMod q) = 1)
    (him :
      (((g ^ period).im : Int) : ZMod q) = 0) :
    Function.Periodic
      (fun n : Nat =>
        (((((g ^ n).re : Int) : ZMod q)),
          ((((g ^ n).im : Int) : ZMod q)))) period := by
  intro n
  apply Prod.ext
  · change
      (((g ^ (n + period)).re : Int) : ZMod q) =
        (((g ^ n).re : Int) : ZMod q)
    rw [pow_add, Zsqrtd.re_mul]
    push_cast
    rw [hre, him]
    ring
  · change
      (((g ^ (n + period)).im : Int) : ZMod q) =
        (((g ^ n).im : Int) : ZMod q)
    rw [pow_add, Zsqrtd.im_mul]
    push_cast
    rw [hre, him]
    ring

private theorem zsqrtd_phase_state_periodic
    {K q c T : Nat} (g : ℤ√(K : Int))
    (hre :
      (((g ^ (12 * T)).re : Int) : ZMod q) = 1)
    (him :
      (((g ^ (12 * T)).im : Int) : ZMod q) = 0) :
    Function.Periodic
      (fun j : Nat =>
        (((((g ^ (c + 12 * j)).re : Int) : ZMod q)),
          ((((g ^ (c + 12 * j)).im : Int) : ZMod q)))) T := by
  intro j
  apply Prod.ext
  · change
      (((g ^ (c + 12 * (j + T))).re : Int) : ZMod q) =
        (((g ^ (c + 12 * j)).re : Int) : ZMod q)
    rw [show c + 12 * (j + T) =
        (c + 12 * j) + 12 * T by omega,
      pow_add, Zsqrtd.re_mul]
    push_cast
    rw [hre, him]
    ring
  · change
      (((g ^ (c + 12 * (j + T))).im : Int) : ZMod q) =
        (((g ^ (c + 12 * j)).im : Int) : ZMod q)
    rw [show c + 12 * (j + T) =
        (c + 12 * j) + 12 * T by omega,
      pow_add, Zsqrtd.im_mul]
    push_cast
    rw [hre, him]
    ring

/-- General finite phase-table certificate.  An oriented state of period
`12*T` reduces the selected `c mod 12` source phase to exactly `T` table
entries.  If every predecessor in that table is nonsquare modulo `q`, the
leaf source is impossible. -/
theorem no_sm2_source_of_finite_phase_certificate
    {K q y h c T : Nat} (g : ℤ√(K : Int))
    (hT : 0 < T)
    (hperiodRe :
      (((g ^ (12 * T)).re : Int) : ZMod q) = 1)
    (hperiodIm :
      (((g ^ (12 * T)).im : Int) : ZMod q) = 0)
    (hphase : h % 12 = c)
    (hsource :
      (y : Int) ^ 2 + 1 = (g ^ h).re)
    (hnonsquare :
      ∀ j : Nat, j < T →
        ¬ IsSquare
          (((((g ^ (c + 12 * j)).re : Int) : ZMod q) - 1))) :
    False := by
  let s := h / 12
  let j := s % T
  have hj : j < T := by
    exact Nat.mod_lt s hT
  have hdecomp : h = c + 12 * s := by
    have hsplit := Nat.mod_add_div h 12
    rw [hphase] at hsplit
    omega
  have hperiod :=
    (zsqrtd_phase_state_periodic (c := c)
      g hperiodRe hperiodIm).map_mod_nat s
  have hperiodReal := congrArg Prod.fst hperiod
  simp only at hperiodReal
  have hphaseReal :
      (((g ^ (c + 12 * j)).re : Int) : ZMod q) =
        (((g ^ h).re : Int) : ZMod q) := by
    change
      (((g ^ (c + 12 * (s % T))).re : Int) : ZMod q) =
        (((g ^ (c + 12 * s)).re : Int) : ZMod q)
      at hperiodReal
    rw [← hdecomp] at hperiodReal
    simpa only [j] using hperiodReal
  have hsourceCast :=
    congrArg (fun z : Int => (z : ZMod q)) hsource
  push_cast at hsourceCast
  apply hnonsquare j hj
  refine ⟨(y : ZMod q), ?_⟩
  calc
    ((((g ^ (c + 12 * j)).re : Int) : ZMod q) - 1) =
        (((g ^ h).re : Int) : ZMod q) - 1 := by
          rw [hphaseReal]
    _ = (y : ZMod q) ^ 2 := by
          linear_combination -hsourceCast
    _ = (y : ZMod q) * y := by ring


/-- Generic finite phase certificate.  If a quadratic-ring generator has
oriented period twelve modulo `q`, and the selected source phase is `c`,
then a source equation `y² + 1 = Re(g^h)` forces
`Re(g^c) - 1` to be a square modulo `q`.  A checked nonsquare therefore
eliminates that complete phase.  No primality assumption on `q` is needed. -/
theorem no_sm2_source_of_phase_certificate
    {K q y h c : Nat} (g : ℤ√(K : Int))
    (hperiodRe :
      (((g ^ 12).re : Int) : ZMod q) = 1)
    (hperiodIm :
      (((g ^ 12).im : Int) : ZMod q) = 0)
    (hphase : h % 12 = c)
    (hsource :
      (y : Int) ^ 2 + 1 = (g ^ h).re)
    (hnonsquare :
      ¬ IsSquare
        (((((g ^ c).re : Int) : ZMod q) - 1))) :
    False := by
  have hperiod :=
    (zsqrtd_pow_mod_periodic_of_state
      g hperiodRe hperiodIm).map_mod_nat h
  have hperiodReal := congrArg Prod.fst hperiod
  simp only at hperiodReal
  have hphaseReal :
      (((g ^ c).re : Int) : ZMod q) =
        (((g ^ h).re : Int) : ZMod q) := by
    simpa [hphase] using hperiodReal
  have hsourceCast :=
    congrArg (fun z : Int => (z : ZMod q)) hsource
  push_cast at hsourceCast
  apply hnonsquare
  refine ⟨(y : ZMod q), ?_⟩
  calc
    ((((g ^ c).re : Int) : ZMod q) - 1) =
        (((g ^ h).re : Int) : ZMod q) - 1 := by
          rw [hphaseReal]
    _ = (y : ZMod q) ^ 2 := by
          linear_combination -hsourceCast
    _ = (y : ZMod q) * y := by ring

/-- Convenient two-phase wrapper for the exact `1/5 mod 12` source split. -/
theorem no_sm2_source_of_two_phase_certificate
    {K q y h : Nat} (g : ℤ√(K : Int))
    (hperiodRe :
      (((g ^ 12).re : Int) : ZMod q) = 1)
    (hperiodIm :
      (((g ^ 12).im : Int) : ZMod q) = 0)
    (hphase : h % 12 = 1 ∨ h % 12 = 5)
    (hsource :
      (y : Int) ^ 2 + 1 = (g ^ h).re)
    (hnonsquareOne :
      ¬ IsSquare
        (((((g ^ 1).re : Int) : ZMod q) - 1)))
    (hnonsquareFive :
      ¬ IsSquare
        (((((g ^ 5).re : Int) : ZMod q) - 1))) :
    False := by
  rcases hphase with hOne | hFive
  · exact no_sm2_source_of_phase_certificate
      g hperiodRe hperiodIm hOne hsource hnonsquareOne
  · exact no_sm2_source_of_phase_certificate
      g hperiodRe hperiodIm hFive hsource hnonsquareFive

/-- The exact coupled residual refined by its typed upper source generator.
The complete lower orbit and the unchanged represented centre remain in the
embedded double-orbit residual. -/
structure Sm2LowerSquareGeneratorResidual
    (data : PairPellCounterexampleData) where
  doubleResidual : Sm2LowerSquareDoubleOrbitResidual data
  upperGenerator :
    Nonempty
      (Sm2LowerSquareUpperSourceGenerator
        doubleResidual.lowerResidual.residual.allocation)

namespace Sm2LowerSquareDoubleOrbitResidual

/-- Every exact double-orbit residual canonically refines to the typed
source-generator residual. -/
def toGeneratorResidual
    {data : PairPellCounterexampleData}
    (residual : Sm2LowerSquareDoubleOrbitResidual data) :
    Sm2LowerSquareGeneratorResidual data := by
  refine
    {
      doubleResidual := residual
      upperGenerator := ?_
    }
  obtain ⟨orbit⟩ := residual.upperOrbit
  exact orbit.sourceGenerator_nonempty

end Sm2LowerSquareDoubleOrbitResidual

/-- Exact source-equivalent compiler into the final typed generator residual.
The reverse direction uses the retained double-orbit residual and therefore
does not reconstruct from modular data. -/
theorem sm2LowerSquareSource_iff_exists_generatorResidual
    (X : Nat) :
    Sm2LowerSquareSource X ↔
      ∃ data : PairPellCounterexampleData,
        data.pell.Represents X ∧
          Nonempty (Sm2LowerSquareGeneratorResidual data) := by
  constructor
  · intro hsource
    obtain ⟨data, hrep, ⟨residual⟩⟩ :=
      (sm2LowerSquareSource_iff_exists_doubleOrbitResidual X).mp hsource
    exact ⟨data, hrep, ⟨residual.toGeneratorResidual⟩⟩
  · rintro ⟨data, hrep, ⟨residual⟩⟩
    apply
      (sm2LowerSquareSource_iff_exists_doubleOrbitResidual X).mpr
    exact ⟨data, hrep, ⟨residual.doubleResidual⟩⟩

private theorem zsqrtd_generator_ordinate_dvd_power_im
    (K P Q n : Nat) :
    (Q : Int) ∣
      ((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).im := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      rw [pow_succ, Zsqrtd.im_mul]
      refine
        ⟨((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).re + c * P, ?_⟩
      rw [hc]
      ring

private theorem zsqrtd_generator_power_real_mod
    {K P Q q : Nat}
    (hnegative : P ^ 2 + 1 = K * Q ^ 2)
    (hq : q ∣ P ^ 2 + 1) (n : Nat) :
    ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ n).re : Int) : ZMod q) =
      (P : ZMod q) ^ n := by
  have hzero :
      ((P ^ 2 + 1 : Nat) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (P ^ 2 + 1) q).mpr hq
  have hzero' : (P : ZMod q) ^ 2 + 1 = 0 := by
    simpa using hzero
  have hnegativeCast :=
    congrArg (fun z : Nat => (z : ZMod q)) hnegative
  push_cast at hnegativeCast
  have hnormZero :
      (K : ZMod q) * (Q : ZMod q) ^ 2 = 0 := by
    rw [← hnegativeCast]
    exact hzero'
  induction n with
  | zero =>
      simp
  | succ n ih =>
      obtain ⟨c, hc⟩ :=
        zsqrtd_generator_ordinate_dvd_power_im K P Q n
      rw [pow_succ, Zsqrtd.re_mul]
      push_cast
      rw [ih, hc]
      push_cast
      calc
        (P : ZMod q) ^ n * P + K * (Q * c) * Q =
            (P : ZMod q) ^ n * P +
              (c : ZMod q) * (K * Q ^ 2) := by ring
        _ = (P : ZMod q) ^ n * P := by rw [hnormZero]; ring
        _ = (P : ZMod q) ^ (n + 1) := by rw [pow_succ]

private theorem zmod_pow_eq_self_of_square_eq_neg_one_of_mod_four_one
    {q P h : Nat}
    (hsquare : (P : ZMod q) ^ 2 = -1)
    (hphase : h % 4 = 1) :
    (P : ZMod q) ^ h = P := by
  have hdecomp : h = 4 * (h / 4) + 1 := by
    have h := (Nat.mod_add_div h 4).symm
    rw [hphase] at h
    omega
  have hfour : (P : ZMod q) ^ 4 = 1 := by
    calc
      (P : ZMod q) ^ 4 = ((P : ZMod q) ^ 2) ^ 2 := by ring
      _ = (-1 : ZMod q) ^ 2 := by rw [hsquare]
      _ = 1 := by ring
  rw [hdecomp, pow_add, pow_mul]
  rw [hfour]
  simp

/-- Nested-square generator congruence.  If `q` divides the norm factor
`P²+1` and the outer exponent is `1 mod 4`, then the real coordinate of the
source power is congruent to the generator real coordinate `P` modulo `q`. -/
theorem zsqrtd_generator_real_mod_of_phase
    {K P Q q h : Nat}
    (hnegative : P ^ 2 + 1 = K * Q ^ 2)
    (hq : q ∣ P ^ 2 + 1)
    (hphase : h % 4 = 1) :
    ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ h).re : Int) : ZMod q) =
      (P : ZMod q) := by
  have hzero :
      ((P ^ 2 + 1 : Nat) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (P ^ 2 + 1) q).mpr hq
  have hsquare : (P : ZMod q) ^ 2 = -1 := by
    push_cast at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  exact
    (zsqrtd_generator_power_real_mod hnegative hq h).trans
      (zmod_pow_eq_self_of_square_eq_neg_one_of_mod_four_one
        hsquare hphase)

/-- A nonsquare divisor of the generator norm is a terminal obstruction for
the complete outer source phase: the leaf identity `X = y²+1` would make
`P-1` a square modulo the same divisor. -/
theorem no_sm2_source_of_generator_norm_nonsquare
    {K P Q q y h : Nat}
    (hnegative : P ^ 2 + 1 = K * Q ^ 2)
    (hq : q ∣ P ^ 2 + 1)
    (hphase : h % 4 = 1)
    (hsource :
      (y : Int) ^ 2 + 1 =
        ((⟨P, Q⟩ : ℤ√(K : Int)) ^ h).re)
    (hnonsquare :
      ¬ IsSquare (((P : ZMod q) - 1))) :
    False := by
  have hreal :=
    zsqrtd_generator_real_mod_of_phase
      hnegative hq hphase
  have hsourceCast :=
    congrArg (fun z : Int => (z : ZMod q)) hsource
  push_cast at hsourceCast
  apply hnonsquare
  refine ⟨(y : ZMod q), ?_⟩
  calc
    (P : ZMod q) - 1 =
        ((((⟨P, Q⟩ : ℤ√(K : Int)) ^ h).re : Int) :
          ZMod q) - 1 := by rw [hreal]
    _ = (y : ZMod q) ^ 2 := by
      linear_combination -hsourceCast
    _ = (y : ZMod q) * y := by ring

namespace Sm2LowerSquareUpperSourceGenerator

/-- Quadratic-ring point underlying a typed source generator. -/
def point
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    ℤ√(data.upperKernel : Int) :=
  ⟨generator.real, generator.ordinate⟩

/-- Real coordinate of a generator power, reduced modulo `q`. -/
def powerRealResidue
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (q n : Nat) : ZMod q :=
  ((generator.point ^ n).re : Int)

/-- Ordinate of a generator power, reduced modulo `q`. -/
def powerOrdinateResidue
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (q n : Nat) : ZMod q :=
  ((generator.point ^ n).im : Int)

/-- The predecessor of a generator power, reduced modulo `q`. -/
def predecessorResidue
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (q n : Nat) : ZMod q :=
  generator.powerRealResidue q n - 1

private theorem source_real_coordinate
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    (allocation.y : Int) ^ 2 + 1 =
      (generator.point ^
        (2 * generator.outerIndex + 1)).re := by
  have hpower := congrArg Zsqrtd.re generator.source_power
  change
    (data.center : Int) =
      (generator.point ^
        (2 * generator.outerIndex + 1)).re
    at hpower
  calc
    (allocation.y : Int) ^ 2 + 1 =
        (data.center : Int) := by
          rw [allocation.center_eq]
          push_cast
          ring
    _ =
        (generator.point ^
          (2 * generator.outerIndex + 1)).re := hpower

/-- Source-facing adapter for the generator-factor nonsquare certificate. -/
theorem false_of_factor_nonsquare
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {q : Nat} (hq : q ∣ generator.real ^ 2 + 1)
    (hnonsquare :
      ¬ IsSquare (((generator.real : ZMod q) - 1))) :
    False := by
  exact
    no_sm2_source_of_generator_norm_nonsquare
      generator.negative_equation hq generator.outer_phase_mod_four
      generator.source_real_coordinate hnonsquare

/-- Source-facing adapter for complete finite tables on both corrected
generator phases. -/
theorem false_of_finite_phase_tables
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {q T : Nat} (hT : 0 < T)
    (hperiodRe :
      generator.powerRealResidue q (12 * T) = 1)
    (hperiodIm :
      generator.powerOrdinateResidue q (12 * T) = 0)
    (hnonsquareOne :
      ∀ j : Nat, j < T →
        ¬ IsSquare
          (generator.predecessorResidue q (1 + 12 * j)))
    (hnonsquareFive :
      ∀ j : Nat, j < T →
        ¬ IsSquare
          (generator.predecessorResidue q (5 + 12 * j))) :
    False := by
  let g : ℤ√(data.upperKernel : Int) := generator.point
  have hsource :
      (allocation.y : Int) ^ 2 + 1 =
        (g ^ (2 * generator.outerIndex + 1)).re := by
    simpa [g] using generator.source_real_coordinate
  rcases generator.oriented_phase with hOne | hFive
  · exact
      no_sm2_source_of_finite_phase_certificate
        g hT
        (by simpa [g, powerRealResidue] using hperiodRe)
        (by simpa [g, powerOrdinateResidue] using hperiodIm)
        hOne.2 hsource
        (by
          simpa [g, predecessorResidue, powerRealResidue] using
            hnonsquareOne)
  · exact
      no_sm2_source_of_finite_phase_certificate
        g hT
        (by simpa [g, powerRealResidue] using hperiodRe)
        (by simpa [g, powerOrdinateResidue] using hperiodIm)
        hFive.2 hsource
        (by
          simpa [g, predecessorResidue, powerRealResidue] using
            hnonsquareFive)

end Sm2LowerSquareUpperSourceGenerator

end Erdos364
