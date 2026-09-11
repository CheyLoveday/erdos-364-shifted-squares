import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Erdos364.SquareMiddle.Sm2LowerSquareGeneratorRank
import Erdos364.SquareMiddle.Sm2LowerSquareOuterSeventeen
import Erdos364.SquareMiddle.Sm2LowerSquareOuterFortyOne

namespace Erdos364

/-!
# Shifted-square propagation in the Dickson--Lucas real recurrence

This module exports the source-independent propagation layer for the maintained
fixed-`17` and fixed-`41` shifted-square theorems.  It preserves the existing
recurrence and imports the fixed-prime results without changing their proofs.
-/

/-- An initial real coordinate congruent to two modulo four remains two modulo
four at every odd index. -/
theorem sm2LucasReal_mod_four_two_of_odd
    {A n : Nat}
    (hA : A % 4 = 2)
    (hn : Odd n) :
    sm2LucasReal A n % 4 = 2 := by
  have hACast : (A : ZMod 4) = 2 :=
    (ZMod.natCast_eq_natCast_iff' A 2 4).mpr hA
  have hCoeff : (2 * A : ZMod 4) = 0 := by
    rw [hACast]
    decide
  have hstep (j : Nat) :
      (sm2LucasReal A (j + 2) : ZMod 4) =
        (sm2LucasReal A j : ZMod 4) := by
    rw [sm2LucasReal_succ_succ]
    push_cast
    rw [hCoeff]
    ring
  obtain ⟨k, rfl⟩ := hn
  have hcast :
      (sm2LucasReal A (2 * k + 1) : ZMod 4) = 2 := by
    induction k with
    | zero =>
        simpa [sm2LucasReal] using hACast
    | succ k ih =>
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
          hstep, ih]
  exact
    (ZMod.natCast_eq_natCast_iff'
      (sm2LucasReal A (2 * k + 1)) 2 4).mp hcast

/-- In the complementary phase `A = 6 mod 8`, every index congruent to one
modulo four has real coordinate six modulo eight. -/
theorem sm2LucasReal_mod_eight_six_of_index_mod_four_one
    {A n : Nat}
    (hA : A % 8 = 6)
    (hn : n % 4 = 1) :
    sm2LucasReal A n % 8 = 6 := by
  have hACast : (A : ZMod 8) = 6 :=
    (ZMod.natCast_eq_natCast_iff' A 6 8).mpr hA
  have hCoeff : (2 * A : ZMod 8) = 4 := by
    rw [hACast]
    decide
  have hperiod :
      Function.Periodic
        (fun j : Nat => (sm2LucasReal A j : ZMod 8)) 4 := by
    intro j
    change
      (sm2LucasReal A (j + 4) : ZMod 8) =
        (sm2LucasReal A j : ZMod 8)
    rw [show j + 4 = (j + 2) + 2 by omega,
      sm2LucasReal_succ_succ,
      show j + 3 = (j + 1) + 2 by omega,
      sm2LucasReal_succ_succ,
      sm2LucasReal_succ_succ]
    push_cast
    rw [hCoeff]
    calc
      4 *
            (4 *
                (4 * (sm2LucasReal A (j + 1) : ZMod 8) +
                  sm2LucasReal A j) +
              sm2LucasReal A (j + 1)) +
          (4 * sm2LucasReal A (j + 1) +
            sm2LucasReal A j) =
          72 * sm2LucasReal A (j + 1) +
            17 * sm2LucasReal A j := by ring
      _ = sm2LucasReal A j := by
        rw [show (72 : ZMod 8) = 0 by decide,
          show (17 : ZMod 8) = 1 by decide]
        ring
  have hreduce := hperiod.map_mod_nat n
  have hcast :
      (sm2LucasReal A n : ZMod 8) = 6 := by
    rw [← hreduce, hn]
    simpa [sm2LucasReal] using hACast
  exact
    (ZMod.natCast_eq_natCast_iff'
      (sm2LucasReal A n) 6 8).mp hcast

private theorem no_square_add_one_of_mod_eight_six
    {X y : Nat}
    (hX : X % 8 = 6)
    (hxy : X = y ^ 2 + 1) :
    False := by
  have hxyMod := congrArg (fun z : Nat => z % 8) hxy
  rw [hX] at hxyMod
  have hrlt : y ^ 2 % 8 < 8 :=
    Nat.mod_lt _ (by decide)
  have hsquare : y ^ 2 % 8 = 5 := by
    interval_cases h : y ^ 2 % 8 <;>
      simp [Nat.add_mod, h] at hxyMod
    omega
  have hylt : y % 8 < 8 :=
    Nat.mod_lt y (by decide)
  have hs :
      y ^ 2 % 8 = (y % 8) ^ 2 % 8 :=
    Nat.pow_mod y 2 8
  rw [hs] at hsquare
  interval_cases hy : y % 8 <;>
    norm_num at hsquare

/-- The fixed-`17` shifted-square obstruction has the natural phase
`A = 2 mod 4`. -/
theorem no_sm2LucasReal_seventeen_square_of_mod_four_two
    {A y : Nat}
    (hA : A % 4 = 2)
    (hreal : sm2LucasReal A 17 = y ^ 2 + 1) :
    False := by
  have hmod : A % 8 % 4 = A % 4 :=
    Nat.mod_mod_of_dvd A (by decide : 4 ∣ 8)
  have hlt : A % 8 < 8 :=
    Nat.mod_lt A (by decide)
  have hcases : A % 8 = 2 ∨ A % 8 = 6 := by
    rw [hA] at hmod
    omega
  rcases hcases with htwo | hsix
  · exact
      no_sm2LucasReal_seventeen_square_of_mod_eight_two
        htwo hreal
  · exact
      no_square_add_one_of_mod_eight_six
        (sm2LucasReal_mod_eight_six_of_index_mod_four_one
          hsix (by decide : 17 % 4 = 1))
        hreal

/-- The fixed-`41` shifted-square obstruction has the natural phase
`A = 2 mod 4`. -/
theorem no_sm2LucasReal_fortyOne_square_of_mod_four_two
    {A y : Nat}
    (hA : A % 4 = 2)
    (hreal : sm2LucasReal A 41 = y ^ 2 + 1) :
    False := by
  have hmod : A % 8 % 4 = A % 4 :=
    Nat.mod_mod_of_dvd A (by decide : 4 ∣ 8)
  have hlt : A % 8 < 8 :=
    Nat.mod_lt A (by decide)
  have hcases : A % 8 = 2 ∨ A % 8 = 6 := by
    rw [hA] at hmod
    omega
  rcases hcases with htwo | hsix
  · exact ss41_shiftedSquare_impossible htwo hreal
  · exact
      no_square_add_one_of_mod_eight_six
        (sm2LucasReal_mod_eight_six_of_index_mod_four_one
          hsix (by decide : 41 % 4 = 1))
        hreal

/-- For an odd inner index, the real-coordinate recurrence composes under
index multiplication. -/
theorem sm2LucasReal_mul_of_odd_right
    (A m n : Nat)
    (hn : Odd n) :
    sm2LucasReal A (m * n) =
      sm2LucasReal (sm2LucasReal A n) m := by
  let K := A ^ 2 + 1
  let B := sm2LucasReal A n
  let C := sm2LucasCoeff A n
  let eta := sm2UpperNegativeUnit K A 1
  have hbase : A ^ 2 + 1 = K * 1 ^ 2 := by
    simp [K]
  have hcoords :
      eta ^ n = sm2UpperNegativeUnit K B C := by
    simpa [eta, B, C, sm2UpperNegativeUnit] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := K) (u := A) (v := 1) (n := n)
        hbase)
  have hnegativeB : B ^ 2 + 1 = K * C ^ 2 := by
    simpa [B, C] using
      (sm2LucasReal_odd_negative_equation
        (K := K) (u := A) (v := 1) (n := n)
        hbase hn)
  have heq :
      eta ^ (m * n) =
        sm2UpperNegativeUnit K B C ^ m := by
    calc
      eta ^ (m * n) = eta ^ (n * m) := by
        rw [Nat.mul_comm m n]
      _ = (eta ^ n) ^ m := by
        rw [pow_mul]
      _ = sm2UpperNegativeUnit K B C ^ m := by
        rw [hcoords]
  have hre := congrArg Zsqrtd.re heq
  rw [sm2UpperNegativeUnit_pow_re hbase (m * n),
    sm2UpperNegativeUnit_pow_re hnegativeB m] at hre
  exact_mod_cast hre

/-- Every odd index divisible by `17` or `41` inherits the corresponding
shifted-square obstruction. -/
theorem no_sm2LucasReal_shiftedSquare_of_odd_index_factor
    {A n y : Nat}
    (hA : A % 4 = 2)
    (hn : Odd n)
    (hfactor : 17 ∣ n ∨ 41 ∣ n)
    (hreal : sm2LucasReal A n = y ^ 2 + 1) :
    False := by
  rcases hfactor with h17 | h41
  · obtain ⟨q, hq⟩ := h17
    have hnProduct : Odd (17 * q) := by
      rw [← hq]
      exact hn
    have hqOdd : Odd q :=
      Nat.Odd.of_mul_right hnProduct
    apply
      no_sm2LucasReal_seventeen_square_of_mod_four_two
        (sm2LucasReal_mod_four_two_of_odd hA hqOdd)
    rw [← sm2LucasReal_mul_of_odd_right A 17 q hqOdd,
      ← hq]
    exact hreal
  · obtain ⟨q, hq⟩ := h41
    have hnProduct : Odd (41 * q) := by
      rw [← hq]
      exact hn
    have hqOdd : Odd q :=
      Nat.Odd.of_mul_right hnProduct
    apply
      no_sm2LucasReal_fortyOne_square_of_mod_four_two
        (sm2LucasReal_mod_four_two_of_odd hA hqOdd)
    rw [← sm2LucasReal_mul_of_odd_right A 41 q hqOdd,
      ← hq]
    exact hreal

/-- Source-independent norm-minus-one Pell-unit form of the odd-index
propagation theorem. -/
theorem normNegativeOneUnit_real_ne_square_add_one_of_index_factor
    {K u v n : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2)
    (hn : Odd n)
    (hfactor : 17 ∣ n ∨ 41 ∣ n)
    (y : Nat) :
    ((⟨u, v⟩ : ℤ√(K : Int)) ^ n).re ≠
      ((y ^ 2 + 1 : Nat) : Int) := by
  intro hreal
  change
    (sm2UpperNegativeUnit K u v ^ n).re = _ at hreal
  apply
    no_sm2LucasReal_shiftedSquare_of_odd_index_factor
      hu hn hfactor
  have hpow :
      (sm2UpperNegativeUnit K u v ^ n).re =
        (sm2LucasReal u n : Int) :=
    sm2UpperNegativeUnit_pow_re hnegative n
  exact_mod_cast hpow.symm.trans hreal

/-- Squaring a norm-minus-one unit at an odd inner index gives the first
doubling identity needed for the exact even-index valuation. -/
private theorem sm2LucasReal_double_sub_one_of_odd
    {A m : Nat} (hm : Odd m) :
    sm2LucasReal A (m + m) - 1 = 2 * sm2LucasReal A m ^ 2 := by
  let K := A ^ 2 + 1
  let eta := sm2UpperNegativeUnit K A 1
  have hbase : A ^ 2 + 1 = K * 1 ^ 2 := by
    simp [K]
  have hcoords :
      eta ^ m =
        (⟨sm2LucasReal A m, sm2LucasCoeff A m⟩ : ℤ√(K : Int)) := by
    simpa [eta, sm2UpperNegativeUnit] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := K) (u := A) (v := 1) (n := m) hbase)
  have hpow : eta ^ (m + m) = eta ^ m * eta ^ m := by
    rw [pow_add]
  have hre := congrArg Zsqrtd.re hpow
  rw [sm2UpperNegativeUnit_pow_re hbase (m + m), hcoords,
    Zsqrtd.re_mul] at hre
  norm_num at hre
  have hreNatRaw :
      sm2LucasReal A (m + m) =
        sm2LucasReal A m * sm2LucasReal A m +
          K * sm2LucasCoeff A m * sm2LucasCoeff A m := by
    exact_mod_cast hre
  have hreNat :
      sm2LucasReal A (m + m) =
        sm2LucasReal A m ^ 2 + K * sm2LucasCoeff A m ^ 2 := by
    simpa [pow_two, Nat.mul_assoc] using hreNatRaw
  have hnegative :
      sm2LucasReal A m ^ 2 + 1 = K * sm2LucasCoeff A m ^ 2 := by
    simpa [K] using
      (sm2LucasReal_odd_negative_equation
        (K := K) (u := A) (v := 1) (n := m) hbase hm)
  have hdouble :
      sm2LucasReal A (m + m) = 2 * sm2LucasReal A m ^ 2 + 1 := by
    nlinarith
  omega

/-- At an even index, a norm-minus-one unit has norm one. -/
private theorem sm2LucasReal_even_positive_equation
    {A m : Nat} (hm : Even m) :
    sm2LucasReal A m ^ 2 =
      (A ^ 2 + 1) * sm2LucasCoeff A m ^ 2 + 1 := by
  let K := A ^ 2 + 1
  let eta := sm2UpperNegativeUnit K A 1
  have hbase : A ^ 2 + 1 = K * 1 ^ 2 := by
    simp [K]
  have hetaNorm : Zsqrtd.norm eta = -1 := by
    simp only [eta, sm2UpperNegativeUnit, Zsqrtd.norm_def]
    have h := congrArg (fun z : Nat => (z : Int)) hbase
    norm_num [pow_two] at h ⊢
    nlinarith
  have hpowNorm : Zsqrtd.norm (eta ^ m) = (-1 : Int) ^ m := by
    calc
      Zsqrtd.norm (eta ^ m) = Zsqrtd.norm eta ^ m :=
        map_pow Zsqrtd.normMonoidHom eta m
      _ = (-1 : Int) ^ m := by rw [hetaNorm]
  have hplus : (-1 : Int) ^ m = 1 := by
    exact hm.neg_one_pow
  have hcoords :=
    sm2UpperNegativeUnit_pow_coordinates
      (K := K) (u := A) (v := 1) (n := m) hbase
  rw [hcoords, Zsqrtd.norm_def, hplus] at hpowNorm
  norm_num at hpowNorm
  have hnormInt :
      (sm2LucasReal A m : Int) ^ 2 =
        (K : Int) * (sm2LucasCoeff A m : Int) ^ 2 + 1 := by
    nlinarith
  exact_mod_cast hnormInt

/-- Squaring a norm-minus-one unit at an even inner index gives the second,
parity-specific doubling identity. -/
private theorem sm2LucasReal_double_sub_one_of_even
    {A m : Nat} (hm : Even m) :
    sm2LucasReal A (m + m) - 1 =
      2 * (sm2LucasReal A m - 1) * (sm2LucasReal A m + 1) := by
  let K := A ^ 2 + 1
  let eta := sm2UpperNegativeUnit K A 1
  have hbase : A ^ 2 + 1 = K * 1 ^ 2 := by
    simp [K]
  have hcoords :
      eta ^ m =
        (⟨sm2LucasReal A m, sm2LucasCoeff A m⟩ : ℤ√(K : Int)) := by
    simpa [eta, sm2UpperNegativeUnit] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := K) (u := A) (v := 1) (n := m) hbase)
  have hpow : eta ^ (m + m) = eta ^ m * eta ^ m := by
    rw [pow_add]
  have hre := congrArg Zsqrtd.re hpow
  rw [sm2UpperNegativeUnit_pow_re hbase (m + m), hcoords,
    Zsqrtd.re_mul] at hre
  norm_num at hre
  have hreNatRaw :
      sm2LucasReal A (m + m) =
        sm2LucasReal A m * sm2LucasReal A m +
          K * sm2LucasCoeff A m * sm2LucasCoeff A m := by
    exact_mod_cast hre
  have hreNat :
      sm2LucasReal A (m + m) =
        sm2LucasReal A m ^ 2 + K * sm2LucasCoeff A m ^ 2 := by
    simpa [pow_two, Nat.mul_assoc] using hreNatRaw
  have hnorm := sm2LucasReal_even_positive_equation (A := A) hm
  have hnormK :
      sm2LucasReal A m ^ 2 = K * sm2LucasCoeff A m ^ 2 + 1 := by
    simpa [K] using hnorm
  have hFone : 1 ≤ sm2LucasReal A m := by
    nlinarith
  have hprod :
      (sm2LucasReal A m - 1) * (sm2LucasReal A m + 1) =
        sm2LucasReal A m ^ 2 - 1 := by
    symm
    apply (Nat.sub_eq_iff_eq_add (by nlinarith : 1 ≤ sm2LucasReal A m ^ 2)).2
    have hsub : sm2LucasReal A m - 1 + 1 = sm2LucasReal A m :=
      Nat.sub_add_cancel hFone
    calc
      sm2LucasReal A m ^ 2 = (sm2LucasReal A m - 1 + 1) ^ 2 := by rw [hsub]
      _ = (sm2LucasReal A m - 1) *
            (sm2LucasReal A m - 1 + 1 + 1) + 1 := by ring
      _ = (sm2LucasReal A m - 1) * (sm2LucasReal A m + 1) + 1 := by rw [hsub]
  rw [Nat.mul_assoc, hprod]
  omega

private theorem padicValNat_two_eq_one_of_mod_four_two
    {n : Nat} (hn : n % 4 = 2) :
    padicValNat 2 n = 1 := by
  have hnzero : n ≠ 0 := by
    intro hzero
    subst n
    norm_num at hn
  have htwo : 2 ∣ n := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hmod : n % 4 % 2 = n % 2 :=
      Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 4)
    rw [hn] at hmod
    norm_num at hmod
    omega
  have hnotfour : ¬ 4 ∣ n := by
    intro hfour
    have hzero : n % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hfour
    omega
  have hlower : 1 ≤ padicValNat 2 n :=
    one_le_padicValNat_of_dvd hnzero htwo
  have hupper : padicValNat 2 n ≤ 1 := by
    by_contra hupper
    have htwole : 2 ≤ padicValNat 2 n := by omega
    have hfour : 2 ^ 2 ∣ n :=
      (padicValNat_dvd_iff_le hnzero).mpr htwole
    norm_num at hfour
    exact hnotfour hfour
  omega

/-- An initial real coordinate congruent to two modulo four is one modulo
four at every even index. -/
private theorem sm2LucasReal_mod_four_one_of_even
    {A n : Nat}
    (hA : A % 4 = 2)
    (hn : Even n) :
    sm2LucasReal A n % 4 = 1 := by
  have hACast : (A : ZMod 4) = 2 :=
    (ZMod.natCast_eq_natCast_iff' A 2 4).mpr hA
  have hCoeff : (2 * A : ZMod 4) = 0 := by
    rw [hACast]
    decide
  have hstep (j : Nat) :
      (sm2LucasReal A (j + 2) : ZMod 4) =
        (sm2LucasReal A j : ZMod 4) := by
    rw [sm2LucasReal_succ_succ]
    push_cast
    rw [hCoeff]
    ring
  obtain ⟨k, rfl⟩ := hn
  have hcast :
      (sm2LucasReal A (k + k) : ZMod 4) = 1 := by
    induction k with
    | zero => simp [sm2LucasReal]
    | succ k ih =>
        rw [show (k + 1) + (k + 1) = (k + k) + 2 by omega,
          hstep, ih]
  exact
    (ZMod.natCast_eq_natCast_iff'
      (sm2LucasReal A (k + k)) 1 4).mp hcast

private theorem padicValNat_two_mul
    {m : Nat} (hm : m ≠ 0) :
    padicValNat 2 (2 * m) = padicValNat 2 m + 1 := by
  rw [padicValNat.mul (by decide) hm, padicValNat_self]
  omega

/-- The exact two-adic valuation at every positive even index in the natural
`A = 2 mod 4` phase. -/
theorem sm2LucasReal_sub_one_padicVal_two_of_positive_even
    {A N : Nat}
    (hA : A % 4 = 2)
    (hNpos : 0 < N)
    (hNeven : Even N) :
    padicValNat 2 (sm2LucasReal A N - 1) =
      2 * padicValNat 2 N + 1 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      obtain ⟨m, rfl⟩ := hNeven
      have hmpos : 0 < m := by omega
      have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
      rcases Nat.even_or_odd m with hmEven | hmOdd
      · have hsmall : m < m + m := by omega
        have hvalm := ih m hsmall hmpos hmEven
        have hsubne : sm2LucasReal A m - 1 ≠ 0 := by
          intro hzero
          rw [hzero] at hvalm
          simp at hvalm
        have hmod : sm2LucasReal A m % 4 = 1 :=
          sm2LucasReal_mod_four_one_of_even hA hmEven
        have hplusmod : (sm2LucasReal A m + 1) % 4 = 2 := by
          rw [Nat.add_mod, hmod]
        have hplusval : padicValNat 2 (sm2LucasReal A m + 1) = 1 :=
          padicValNat_two_eq_one_of_mod_four_two hplusmod
        rw [sm2LucasReal_double_sub_one_of_even hmEven,
          padicValNat.mul
            (Nat.mul_ne_zero (by decide) hsubne)
            (Nat.succ_ne_zero _),
          padicValNat.mul (by decide) hsubne,
          padicValNat_self, hvalm, hplusval,
          show m + m = 2 * m by omega,
          padicValNat_two_mul hmne]
        ring
      · have hmod : sm2LucasReal A m % 4 = 2 :=
          sm2LucasReal_mod_four_two_of_odd hA hmOdd
        have hval : padicValNat 2 (sm2LucasReal A m) = 1 :=
          padicValNat_two_eq_one_of_mod_four_two hmod
        have hrealne : sm2LucasReal A m ≠ 0 := by
          intro hzero
          rw [hzero] at hmod
          norm_num at hmod
        have hnotdvd : ¬ 2 ∣ m := by
          rw [Nat.dvd_iff_mod_eq_zero]
          rw [Nat.odd_iff.mp hmOdd]
          decide
        have hmval : padicValNat 2 m = 0 :=
          padicValNat.eq_zero_of_not_dvd hnotdvd
        rw [sm2LucasReal_double_sub_one_of_odd hmOdd,
          padicValNat.mul (by decide) (pow_ne_zero 2 hrealne),
          padicValNat_self, padicValNat.pow, hval,
          show m + m = 2 * m by omega,
          padicValNat_two_mul hmne, hmval]

/-- A positive even index in the natural phase cannot have its real
coordinate equal to one more than a square. -/
theorem no_sm2LucasReal_shiftedSquare_of_positive_even_index
    {A N y : Nat}
    (hA : A % 4 = 2)
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hreal : sm2LucasReal A N = y ^ 2 + 1) :
    False := by
  have hvaluation :=
    sm2LucasReal_sub_one_padicVal_two_of_positive_even hA hNpos hNeven
  have hsquare : sm2LucasReal A N - 1 = y ^ 2 := by
    omega
  rw [hsquare, padicValNat.pow] at hvaluation
  omega

/-- Combining the existing odd-index propagation theorem with the free
even-index valuation obstruction gives the all-positive-index statement. -/
theorem no_sm2LucasReal_shiftedSquare_of_positive_index_factor
    {A N y : Nat}
    (hA : A % 4 = 2)
    (hNpos : 0 < N)
    (hfactor : 17 ∣ N ∨ 41 ∣ N)
    (hreal : sm2LucasReal A N = y ^ 2 + 1) :
    False := by
  rcases Nat.even_or_odd N with hEven | hOdd
  · exact
      no_sm2LucasReal_shiftedSquare_of_positive_even_index
        hA hNpos hEven hreal
  · exact
      no_sm2LucasReal_shiftedSquare_of_odd_index_factor
        hA hOdd hfactor hreal

/-- Pell-unit form of the free positive-even-index obstruction. -/
theorem normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index
    {K u v N : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2)
    (hNpos : 0 < N)
    (hNeven : Even N)
    (y : Nat) :
    ((⟨u, v⟩ : ℤ√(K : Int)) ^ N).re ≠
      ((y ^ 2 + 1 : Nat) : Int) := by
  intro hreal
  change
    (sm2UpperNegativeUnit K u v ^ N).re = _ at hreal
  apply
    no_sm2LucasReal_shiftedSquare_of_positive_even_index
      hu hNpos hNeven
  have hpow :
      (sm2UpperNegativeUnit K u v ^ N).re =
        (sm2LucasReal u N : Int) :=
    sm2UpperNegativeUnit_pow_re hnegative N
  exact_mod_cast hpow.symm.trans hreal

/-- Pell-unit form of the all-positive-index `17`/`41` factor theorem. -/
theorem normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor
    {K u v N : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2)
    (hNpos : 0 < N)
    (hfactor : 17 ∣ N ∨ 41 ∣ N)
    (y : Nat) :
    ((⟨u, v⟩ : ℤ√(K : Int)) ^ N).re ≠
      ((y ^ 2 + 1 : Nat) : Int) := by
  intro hreal
  change
    (sm2UpperNegativeUnit K u v ^ N).re = _ at hreal
  apply
    no_sm2LucasReal_shiftedSquare_of_positive_index_factor
      hu hNpos hfactor
  have hpow :
      (sm2UpperNegativeUnit K u v ^ N).re =
        (sm2LucasReal u N : Int) :=
    sm2UpperNegativeUnit_pow_re hnegative N
  exact_mod_cast hpow.symm.trans hreal

/-- The four-entry residue table for the complementary `A = 6 mod 8` phase. -/
private def sm2LucasRealResidueSix (n : Nat) : Nat :=
  match n % 4 with
  | 0 => 1
  | 1 => 6
  | 2 => 1
  | _ => 2

/-- The real-coordinate recurrence has period four modulo eight in the
complementary `A = 6 mod 8` phase. -/
private theorem sm2LucasReal_mod_eight_six
    {A n : Nat} (hA : A % 8 = 6) :
    sm2LucasReal A n % 8 = sm2LucasRealResidueSix n := by
  have hACast : (A : ZMod 8) = 6 :=
    (ZMod.natCast_eq_natCast_iff' A 6 8).mpr hA
  have hCoeff : (2 * A : ZMod 8) = 4 := by
    rw [hACast]
    decide
  have hperiod :
      Function.Periodic
        (fun j : Nat => (sm2LucasReal A j : ZMod 8)) 4 := by
    intro j
    change
      (sm2LucasReal A (j + 4) : ZMod 8) =
        (sm2LucasReal A j : ZMod 8)
    rw [show j + 4 = (j + 2) + 2 by omega,
      sm2LucasReal_succ_succ,
      show j + 3 = (j + 1) + 2 by omega,
      sm2LucasReal_succ_succ,
      sm2LucasReal_succ_succ]
    push_cast
    rw [hCoeff]
    calc
      4 *
            (4 *
                (4 * (sm2LucasReal A (j + 1) : ZMod 8) +
                  sm2LucasReal A j) +
              sm2LucasReal A (j + 1)) +
          (4 * sm2LucasReal A (j + 1) +
            sm2LucasReal A j) =
          72 * sm2LucasReal A (j + 1) +
            17 * sm2LucasReal A j := by ring
      _ = sm2LucasReal A j := by
        rw [show (72 : ZMod 8) = 0 by decide,
          show (17 : ZMod 8) = 1 by decide]
        ring
  have hreduce := hperiod.map_mod_nat n
  have hzero : (sm2LucasReal A 0 : ZMod 8) = 1 := by
    simp [sm2LucasReal]
  have hone : (sm2LucasReal A 1 : ZMod 8) = 6 := by
    simpa [sm2LucasReal] using hACast
  have htwo : (sm2LucasReal A 2 : ZMod 8) = 1 := by
    have hvalue :
        2 * (A : ZMod 8) * (A : ZMod 8) + 1 = 1 := by
      rw [hACast]
      decide
    simpa [sm2LucasReal] using hvalue
  have hthree : (sm2LucasReal A 3 : ZMod 8) = 2 := by
    have hvalue :
        2 * (A : ZMod 8) *
            (2 * (A : ZMod 8) * (A : ZMod 8) + 1) +
          (A : ZMod 8) = 2 := by
      rw [hACast]
      decide
    simpa [sm2LucasReal] using hvalue
  have hcast :
      (sm2LucasReal A n : ZMod 8) = (sm2LucasRealResidueSix n : ZMod 8) := by
    have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
    calc
      (sm2LucasReal A n : ZMod 8) = (sm2LucasReal A (n % 4) : ZMod 8) := hreduce.symm
      _ = (sm2LucasRealResidueSix n : ZMod 8) := by
        interval_cases h : n % 4 <;>
          simp [sm2LucasRealResidueSix, h, hACast] <;> norm_num <;> decide
  have hreslt : sm2LucasRealResidueSix n < 8 := by
    unfold sm2LucasRealResidueSix
    split <;> omega
  exact
    ((ZMod.natCast_eq_natCast_iff'
      (sm2LucasReal A n) (sm2LucasRealResidueSix n) 8).mp hcast).trans
      (Nat.mod_eq_of_lt hreslt)

/-- In the `A = 2 mod 8`, `n = 3 mod 4` cross-phase, the shifted real
coordinate is five modulo eight. -/
private theorem sm2LucasReal_sub_one_mod_eight_five_of_phase_two_index_mod_four_three
    {A n : Nat}
    (hA : A % 8 = 2)
    (hn : n % 4 = 3) :
    (sm2LucasReal A n - 1) % 8 = 5 := by
  have hres : sm2LucasReal A n % 8 = 6 :=
    sm2LucasReal_mod_eight_of_index_mod_four_three hA hn
  have hle : 1 ≤ sm2LucasReal A n % 8 := by
    rw [hres]
    norm_num
  rw [← Nat.mod_sub_of_le hle, hres]

/-- In the `A = 6 mod 8`, `n = 1 mod 4` cross-phase, the shifted real
coordinate is five modulo eight. -/
private theorem sm2LucasReal_sub_one_mod_eight_five_of_phase_six_index_mod_four_one
    {A n : Nat}
    (hA : A % 8 = 6)
    (hn : n % 4 = 1) :
    (sm2LucasReal A n - 1) % 8 = 5 := by
  have hres : sm2LucasReal A n % 8 = 6 :=
    sm2LucasReal_mod_eight_six_of_index_mod_four_one hA hn
  have hle : 1 ≤ sm2LucasReal A n % 8 := by
    rw [hres]
    norm_num
  rw [← Nat.mod_sub_of_le hle, hres]

/-- In the `A = 2 mod 8`, `n = 1 mod 4` surviving phase, the shifted real
coordinate is one modulo eight. -/
private theorem sm2LucasReal_sub_one_mod_eight_one_of_phase_two_index_mod_four_one
    {A n : Nat}
    (hA : A % 8 = 2)
    (hn : n % 4 = 1) :
    (sm2LucasReal A n - 1) % 8 = 1 := by
  have hres : sm2LucasReal A n % 8 = 2 := by
    rw [sm2LucasReal_mod_eight hA]
    simp [sm2LucasRealResidue, hn]
  have hle : 1 ≤ sm2LucasReal A n % 8 := by
    rw [hres]
    norm_num
  rw [← Nat.mod_sub_of_le hle, hres]

/-- In the `A = 6 mod 8`, `n = 3 mod 4` surviving phase, the shifted real
coordinate is one modulo eight. -/
private theorem sm2LucasReal_sub_one_mod_eight_one_of_phase_six_index_mod_four_three
    {A n : Nat}
    (hA : A % 8 = 6)
    (hn : n % 4 = 3) :
    (sm2LucasReal A n - 1) % 8 = 1 := by
  have hres : sm2LucasReal A n % 8 = 2 := by
    rw [sm2LucasReal_mod_eight_six hA]
    simp [sm2LucasRealResidueSix, hn]
  have hle : 1 ≤ sm2LucasReal A n % 8 := by
    rw [hres]
    norm_num
  rw [← Nat.mod_sub_of_le hle, hres]

/-- The `A = 2 mod 8`, `n = 3 mod 4` cross-phase has no integral
shifted-square solution. -/
private theorem no_sm2LucasReal_shiftedSquare_of_phase_two_index_mod_four_three
    {A n y : Nat}
    (hA : A % 8 = 2)
    (hn : n % 4 = 3)
    (hreal : sm2LucasReal A n = y ^ 2 + 1) :
    False :=
  no_square_add_one_of_mod_eight_six
    (sm2LucasReal_mod_eight_of_index_mod_four_three hA hn) hreal

/-- The `A = 6 mod 8`, `n = 1 mod 4` cross-phase has no integral
shifted-square solution. -/
private theorem no_sm2LucasReal_shiftedSquare_of_phase_six_index_mod_four_one
    {A n y : Nat}
    (hA : A % 8 = 6)
    (hn : n % 4 = 1)
    (hreal : sm2LucasReal A n = y ^ 2 + 1) :
    False :=
  no_square_add_one_of_mod_eight_six
    (sm2LucasReal_mod_eight_six_of_index_mod_four_one hA hn) hreal

#print axioms sm2LucasReal_mod_four_two_of_odd
#print axioms sm2LucasReal_mod_eight_six_of_index_mod_four_one
#print axioms no_sm2LucasReal_seventeen_square_of_mod_four_two
#print axioms no_sm2LucasReal_fortyOne_square_of_mod_four_two
#print axioms sm2LucasReal_mul_of_odd_right
#print axioms no_sm2LucasReal_shiftedSquare_of_odd_index_factor
#print axioms normNegativeOneUnit_real_ne_square_add_one_of_index_factor
#print axioms sm2LucasReal_sub_one_padicVal_two_of_positive_even
#print axioms no_sm2LucasReal_shiftedSquare_of_positive_even_index
#print axioms no_sm2LucasReal_shiftedSquare_of_positive_index_factor
#print axioms normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index
#print axioms normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor

end Erdos364
