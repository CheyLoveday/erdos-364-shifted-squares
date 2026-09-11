import Erdos364.SquareMiddle.Sm2LowerSquareUpperSourceGenerator
import Erdos364.SquareMiddle.QuarticPellCohn
import Erdos364.Foundations.TraceDepthGCD

namespace Erdos364

open Pell
open scoped jacobiSym

/-!
# Rank-sector obstruction for the `sm2LowerSquare` generator

For an even real coordinate `u`, let

```text
B₀ = 0,  B₁ = 1,  Bₙ₊₂ = 2u Bₙ₊₁ + Bₙ.
```

These are the normalized ordinates of powers of
`u + sqrt(u²+1)`.  The Lucas--Jacobi calculation below proves that a
rank-normalized upper generator whose Pell rank is `5 mod 8` has a
nonsquare predecessor modulo its normalized ordinate.  The existing exact
generator adapter then excludes that whole rank sector.

At outer prime divisors, the same calculation excludes the `3` and
`5 mod 8` classes.  A separate source-facing divisor argument excludes
`7 mod 8`: the intermediate real coordinate is `6 mod 8`, while its odd
half divides the retained value `y²+1`.

This is an infinite sector theorem.  It is not a complete exclusion of the
`sm2LowerSquare` leaf.
-/

/-- Normalized ordinate recurrence for powers of a norm-minus-one unit. -/
def sm2LucasCoeff (u : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      2 * u * sm2LucasCoeff u (n + 1) + sm2LucasCoeff u n

/-- Real-coordinate recurrence for powers of a norm-minus-one unit. -/
def sm2LucasReal (u : Nat) : Nat → Nat
  | 0 => 1
  | 1 => u
  | n + 2 =>
      2 * u * sm2LucasReal u (n + 1) + sm2LucasReal u n

/-- The four-entry residue table for the real-coordinate recurrence when
the initial real coordinate is two modulo eight. -/
def sm2LucasRealResidue (n : Nat) : Nat :=
  match n % 4 with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 6

@[simp]
theorem sm2LucasCoeff_zero (u : Nat) :
    sm2LucasCoeff u 0 = 0 := rfl

@[simp]
theorem sm2LucasCoeff_one (u : Nat) :
    sm2LucasCoeff u 1 = 1 := rfl

@[simp]
theorem sm2LucasCoeff_succ_succ (u n : Nat) :
    sm2LucasCoeff u (n + 2) =
      2 * u * sm2LucasCoeff u (n + 1) +
        sm2LucasCoeff u n := rfl

/-- Four consecutive recurrence steps compressed to the odd-index
subsequence. -/
private theorem sm2LucasCoeff_four_step (u n : Nat) :
    sm2LucasCoeff u (n + 4) + sm2LucasCoeff u n =
      (4 * u ^ 2 + 2) * sm2LucasCoeff u (n + 2) := by
  rw [show n + 4 = (n + 2) + 2 by omega,
    sm2LucasCoeff_succ_succ,
    show n + 3 = (n + 1) + 2 by omega,
    sm2LucasCoeff_succ_succ,
    sm2LucasCoeff_succ_succ]
  ring

/-- First-order expansion of an odd-index Lucas ordinate modulo the
square of a divisor of `u^2+1`.  The factor `6` keeps the identity
integral. -/
private theorem six_mul_sm2LucasCoeff_odd_mod_square
    {u d : Nat}
    (hd : d ∣ u ^ 2 + 1)
    (m : Nat) :
    (6 : ZMod (d ^ 2)) *
        (sm2LucasCoeff u (2 * m + 1) : ZMod (d ^ 2)) =
      (-1 : ZMod (d ^ 2)) ^ m *
        ((6 : ZMod (d ^ 2)) *
            (2 * (m : ZMod (d ^ 2)) + 1) -
          (2 * (m : ZMod (d ^ 2))) *
            (2 * (m : ZMod (d ^ 2)) + 1) *
            (2 * (m : ZMod (d ^ 2)) + 2) *
            ((u : ZMod (d ^ 2)) ^ 2 + 1)) := by
  let R := ZMod (d ^ 2)
  have hdSqZero : ((u : R) ^ 2 + 1) ^ 2 = 0 := by
    obtain ⟨e, he⟩ := hd
    have heCast :=
      congrArg (fun z : Nat => (z : R)) he
    push_cast at heCast
    have hdCastSq : (d : R) ^ 2 = 0 := by
      rw [← Nat.cast_pow]
      exact
        (ZMod.natCast_eq_zero_iff (d ^ 2) (d ^ 2)).mpr
          dvd_rfl
    rw [heCast, Nat.cast_mul, mul_pow, hdCastSq]
    simp
  induction m using Nat.twoStepInduction with
  | zero =>
      simp [sm2LucasCoeff]
  | one =>
      simp only [sm2LucasCoeff, pow_one]
      push_cast
      ring
  | more m h0 h1 =>
      have hmOneCast :
          ((m + 1 : Nat) : R) = (m : R) + 1 := by
        simpa using
          (Nat.cast_add m 1 :
            (((m + 1 : Nat) : R) =
              (m : R) + (1 : R)))
      rw [hmOneCast] at h1
      have hrecNat := sm2LucasCoeff_four_step u (2 * m + 1)
      have hrec :
          ((sm2LucasCoeff u (2 * (m + 2) + 1) +
              sm2LucasCoeff u (2 * m + 1) : Nat) : R) =
            (((4 * u ^ 2 + 2) *
              sm2LucasCoeff u (2 * (m + 1) + 1) : Nat) : R) := by
        have hrecCast :=
          congrArg (fun z : Nat => (z : R)) hrecNat
        simpa only [
          show 2 * (m + 2) + 1 = 2 * m + 1 + 4 by omega,
          show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega]
          using hrecCast
      calc
        (6 : R) * (sm2LucasCoeff u (2 * (m + 2) + 1) : R) =
            (((4 * u ^ 2 + 2) *
                sm2LucasCoeff u (2 * (m + 1) + 1) : Nat) : R) * 6 -
              (6 : R) *
                (sm2LucasCoeff u (2 * m + 1) : R) := by
                  rw [← hrec, Nat.cast_add]
                  ring
        _ =
            (-1 : R) ^ (m + 2) *
              ((6 : R) * (2 * (m : R) + 5) -
                (2 * (m : R) + 4) * (2 * (m : R) + 5) *
                    (2 * (m : R) + 6) * ((u : R) ^ 2 + 1)) := by
              rw [Nat.cast_mul]
              rw [show
                ((4 * u ^ 2 + 2 : Nat) : R) *
                      (sm2LucasCoeff u (2 * (m + 1) + 1) : R) * 6 =
                    ((4 * u ^ 2 + 2 : Nat) : R) *
                      (6 *
                        (sm2LucasCoeff u
                          (2 * (m + 1) + 1) : R)) by ring]
              rw [h1, h0, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
              have hsignOne :
                  (-1 : R) ^ (m + 1) =
                    -((-1 : R) ^ m) := by
                rw [pow_succ]
                ring
              have hsignTwo :
                  (-1 : R) ^ (m + 2) =
                    (-1 : R) ^ m := by
                calc
                  (-1 : R) ^ (m + 2) =
                      (-1 : R) ^ (m + 1) * (-1) := by
                        simpa only [show m + 2 = m + 1 + 1 by omega]
                          using pow_succ (-1 : R) (m + 1)
                  _ = (-1 : R) ^ m := by
                    rw [hsignOne]
                    ring
              rw [hsignOne, hsignTwo]
              linear_combination
                4 * (-1 : R) ^ m *
                  (2 * ((m : R) + 1)) *
                  (2 * ((m : R) + 1) + 1) *
                  (2 * ((m : R) + 1) + 2) *
                  hdSqZero
        _ =
            (-1 : R) ^ (m + 2) *
              ((6 : R) * (2 * ((m + 2 : Nat) : R) + 1) -
                (2 * ((m + 2 : Nat) : R)) *
                    (2 * ((m + 2 : Nat) : R) + 1) *
                    (2 * ((m + 2 : Nat) : R) + 2) *
                    ((u : R) ^ 2 + 1)) := by
              push_cast
              ring

/-- At a prime divisor of `A^2+1`, the first Lucas ordinate at that
prime depth has exact first-order residue `p` modulo `p^2`. -/
theorem sm2LucasCoeff_mod_prime_sq
    {p A : Nat}
    (hp : p.Prime)
    (hpFive : 5 ≤ p)
    (hdiv : p ∣ A ^ 2 + 1) :
    sm2LucasCoeff A p ≡ p [MOD p ^ 2] := by
  letI : Fact p.Prime := ⟨hp⟩
  have hASq : (A : ZMod p) ^ 2 = -1 := by
    have hzero :
        ((A ^ 2 + 1 : Nat) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (A ^ 2 + 1) p).mpr hdiv
    push_cast at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hpNotThree :
      p % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_one hASq
  have hpOdd : p % 2 = 1 :=
    hp.eq_two_or_odd.resolve_left (by omega)
  have hpFour : p % 4 = 1 := by
    have hpModTwo :=
      Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4)
    have hpLt : p % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [hpOdd] at hpModTwo
    omega
  obtain ⟨k, hpk⟩ : ∃ k : Nat, p = 4 * k + 1 := by
    refine ⟨p / 4, ?_⟩
    omega
  let R := ZMod (p ^ 2)
  have hpSqZero : ((p : Nat) : R) ^ 2 = 0 := by
    rw [← Nat.cast_pow]
    exact
      (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).mpr
        dvd_rfl
  have hscaled :
      (6 : R) * (sm2LucasCoeff A p : R) =
        (6 : R) * (p : R) := by
    have hodd :=
      six_mul_sm2LucasCoeff_odd_mod_square
        (u := A) (d := p) hdiv (2 * k)
    obtain ⟨e, he⟩ := hdiv
    rw [show 2 * (2 * k) + 1 = p by omega] at hodd
    rw [hodd]
    have heCast :
        (A : R) ^ 2 + 1 =
          (p : R) * (e : R) := by
      have heCastNat :=
        congrArg (fun z : Nat => (z : R)) he
      push_cast at heCastNat
      calc
        (A : R) ^ 2 + 1 = ((p * e : Nat) : R) :=
          heCastNat
        _ = (p : R) * (e : R) :=
          (Nat.cast_mul (α := R) p e :
            (((p * e : Nat) : R) =
              (p : R) * (e : R)))
    have htwoK :
        ((2 * k : Nat) : R) =
          (2 : R) * (k : R) := by
      change
        ((2 * k : Nat) : R) =
          ((2 : Nat) : R) * (k : R)
      exact
        (Nat.cast_mul (α := R) 2 k :
          (((2 * k : Nat) : R) =
            ((2 : Nat) : R) * (k : R)))
    have hindexCast :
        (2 : R) * ((2 * k : Nat) : R) + 1 =
          (p : R) := by
      have hindexNat :
          2 * (2 * k) + 1 = p := by omega
      calc
        (2 : R) * ((2 * k : Nat) : R) + 1 =
            (2 : R) * (2 * (k : R)) + 1 := by
              rw [htwoK]
        _ = ((2 * (2 * k) + 1 : Nat) : R) := by
              rw [Nat.cast_add (R := R),
                Nat.cast_mul (α := R), Nat.cast_one]
              rw [htwoK]
              norm_num
        _ = (p : R) :=
          congrArg (fun z : Nat => (z : R)) hindexNat
    rw [heCast, hindexCast]
    have hsign :
        (-1 : R) ^ (2 * k) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hsign]
    ring_nf
    rw [hpSqZero]
    simpa [mul_comm]
  have hpNotDvdSix : ¬ p ∣ 6 := by
    intro h
    have hpLeSix : p ≤ 6 := Nat.le_of_dvd (by norm_num) h
    have hpEqFiveOrSix : p = 5 ∨ p = 6 := by omega
    rcases hpEqFiveOrSix with rfl | rfl
    · norm_num at h
    · norm_num at hp
  have hSixUnit : IsUnit (6 : R) :=
    (ZMod.isUnit_iff_coprime 6 (p ^ 2)).mpr
      (hp.coprime_pow_of_not_dvd hpNotDvdSix)
  have hcast :
      (sm2LucasCoeff A p : R) = (p : R) :=
    hSixUnit.mul_left_cancel hscaled
  change
    sm2LucasCoeff A p % p ^ 2 =
      p % p ^ 2
  exact
    (ZMod.natCast_eq_natCast_iff'
      (sm2LucasCoeff A p) p (p ^ 2)).mp hcast

@[simp]
theorem sm2LucasReal_zero (u : Nat) :
    sm2LucasReal u 0 = 1 := rfl

@[simp]
theorem sm2LucasReal_one (u : Nat) :
    sm2LucasReal u 1 = u := rfl

@[simp]
theorem sm2LucasReal_succ_succ (u n : Nat) :
    sm2LucasReal u (n + 2) =
      2 * u * sm2LucasReal u (n + 1) +
        sm2LucasReal u n := rfl

/-- Modulo every divisor of the negative-Pell kernel, the normalized
ordinate is the exponent times the corresponding power of the root real
coordinate.  This is the local arithmetic input for the exact intermediate
depth profile below. -/
theorem sm2LucasCoeff_mod_of_dvd_kernel
    {K u v d n : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hd : d ∣ K) :
    (sm2LucasCoeff u n : ZMod d) =
      (n : ZMod d) * (u : ZMod d) ^ (n - 1) := by
  have hKzero : (K : ZMod d) = 0 :=
    (ZMod.natCast_eq_zero_iff K d).mpr hd
  have hnegativeCast :=
    congrArg (fun z : Nat => (z : ZMod d)) hnegative
  push_cast at hnegativeCast
  rw [hKzero] at hnegativeCast
  have huSq : (u : ZMod d) ^ 2 = -1 := by
    exact eq_neg_of_add_eq_zero_left (by simpa using hnegativeCast)
  induction n using Nat.twoStepInduction with
  | zero =>
      simp
  | one =>
      simp
  | more n h0 h1 =>
      rw [sm2LucasCoeff_succ_succ]
      push_cast
      rw [h0, h1]
      by_cases hn : n = 0
      · subst n
        simp
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        push_cast
        rw [show (u : ZMod d) ^ (k + 2) =
              (u : ZMod d) ^ k * u ^ 2 by ring,
          show (u : ZMod d) ^ (k + 1) =
              (u : ZMod d) ^ k * u by ring,
          huSq]
        ring_nf
        rw [huSq]
        ring

/-- Divisibility of the normalized ordinate by a kernel divisor is exactly
divisibility of the exponent.  Unlike the later norm equation, this statement
does not require the exponent to be odd. -/
theorem dvd_sm2LucasCoeff_iff_dvd_index
    {K u v d n : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hd : d ∣ K) :
    d ∣ sm2LucasCoeff u n ↔ d ∣ n := by
  have hKzero : (K : ZMod d) = 0 :=
    (ZMod.natCast_eq_zero_iff K d).mpr hd
  have hnegativeCast :=
    congrArg (fun z : Nat => (z : ZMod d)) hnegative
  push_cast at hnegativeCast
  rw [hKzero] at hnegativeCast
  have huSq : (u : ZMod d) ^ 2 = -1 := by
    exact eq_neg_of_add_eq_zero_left (by simpa using hnegativeCast)
  have huInv : (u : ZMod d) * (-u) = 1 := by
    calc
      (u : ZMod d) * (-u) = -(u : ZMod d) ^ 2 := by ring
      _ = 1 := by rw [huSq]; ring
  constructor
  · intro hcoeff
    have hzero :
        (n : ZMod d) * (u : ZMod d) ^ (n - 1) = 0 := by
      rw [← sm2LucasCoeff_mod_of_dvd_kernel hnegative hd]
      exact (ZMod.natCast_eq_zero_iff
        (sm2LucasCoeff u n) d).mpr hcoeff
    have hnzero : (n : ZMod d) = 0 := by
      calc
        (n : ZMod d) =
            (n : ZMod d) * 1 := by ring
        _ =
            (n : ZMod d) *
              ((u : ZMod d) * (-u)) ^ (n - 1) := by
                rw [huInv, one_pow]
        _ =
            ((n : ZMod d) * (u : ZMod d) ^ (n - 1)) *
              (-u) ^ (n - 1) := by
                rw [mul_pow]
                ring
        _ = 0 := by rw [hzero]; ring
    exact (ZMod.natCast_eq_zero_iff n d).mp hnzero
  · intro hn
    apply (ZMod.natCast_eq_zero_iff (sm2LucasCoeff u n) d).mp
    rw [sm2LucasCoeff_mod_of_dvd_kernel hnegative hd]
    rw [(ZMod.natCast_eq_zero_iff n d).mpr hn]
    simp

/-- A kernel divisor has the same GCD with the normalized ordinate as with
the exponent. -/
theorem gcd_sm2LucasCoeff_eq_gcd_index
    {K u v d n : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hd : d ∣ K) :
    d.gcd (sm2LucasCoeff u n) = d.gcd n := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · exact
        (dvd_sm2LucasCoeff_iff_dvd_index
          hnegative
          ((Nat.gcd_dvd_left d (sm2LucasCoeff u n)).trans hd)).mp
          (Nat.gcd_dvd_right d (sm2LucasCoeff u n))
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · exact
        (dvd_sm2LucasCoeff_iff_dvd_index
          hnegative
          ((Nat.gcd_dvd_left d n).trans hd)).mpr
          (Nat.gcd_dvd_right d n)

/-- Complete partial kernel-depth profile for powers of a norm-minus-one
unit over a squarefree kernel. -/
theorem sm2NegativeUnit_ordinate_gcd_profile
    {K u v n : Nat}
    (hKsf : Squarefree K)
    (hv : 0 < v)
    (hnegative : u ^ 2 + 1 = K * v ^ 2) :
    K.gcd (v * sm2LucasCoeff u n) =
      K.gcd v * (K / K.gcd v).gcd n := by
  let G := K.gcd v
  let R := K / G
  let B := sm2LucasCoeff u n
  have hGdvdK : G ∣ K := Nat.gcd_dvd_left _ _
  have hGdvdV : G ∣ v := Nat.gcd_dvd_right _ _
  obtain ⟨w, hw⟩ := hGdvdV
  have hKsplit : K = R * G := by
    simpa [R] using (Nat.div_mul_cancel hGdvdK).symm
  have hRdvdK : R ∣ K := by
    exact Nat.div_dvd_of_dvd hGdvdK
  have hRcopV : R.Coprime v := by
    simpa [R, G] using
      Nat.coprime_div_gcd_of_squarefree hKsf (Nat.ne_of_gt hv)
  have hRcopW : R.Coprime w := by
    apply hRcopV.of_dvd_right
    exact ⟨G, by simpa [mul_comm] using hw⟩
  have hRB : R.gcd B = R.gcd n := by
    exact gcd_sm2LucasCoeff_eq_gcd_index hnegative hRdvdK
  calc
    K.gcd (v * sm2LucasCoeff u n) =
        (G * R).gcd (G * (w * B)) := by
          rw [hKsplit, hw]
          simp only [B]
          congr 1 <;> ac_rfl
    _ = G * R.gcd (w * B) := by
      simpa using Nat.gcd_mul_left G R (w * B)
    _ = G * R.gcd B := by
      rw [hRcopW.symm.gcd_mul_left_cancel_right B]
    _ = G * R.gcd n := by rw [hRB]

/-- The real-coordinate recurrence has period four modulo eight when its
initial real coordinate is two modulo eight. -/
theorem sm2LucasReal_mod_eight
    {u n : Nat} (hu : u % 8 = 2) :
    sm2LucasReal u n % 8 =
      sm2LucasRealResidue n := by
  have huBaseCast : (u : ZMod 8) = 2 :=
    (ZMod.natCast_eq_natCast_iff' u 2 8).mpr hu
  have huCast : (2 * u : ZMod 8) = 4 := by
    have h :=
      (ZMod.natCast_eq_natCast_iff' (2 * u) 4 8).mpr
        (by omega)
    push_cast at h
    exact h
  have hperiod :
      Function.Periodic
        (fun j : Nat => (sm2LucasReal u j : ZMod 8)) 4 := by
    intro j
    change
      (sm2LucasReal u (j + 4) : ZMod 8) =
        (sm2LucasReal u j : ZMod 8)
    rw [show j + 4 = ((j + 2) + 2) by omega,
      sm2LucasReal_succ_succ,
      show j + 2 + 1 = (j + 1) + 2 by omega,
      sm2LucasReal_succ_succ,
      sm2LucasReal_succ_succ]
    push_cast
    rw [huCast]
    calc
      4 *
            (4 *
                (4 * (sm2LucasReal u (j + 1) : ZMod 8) +
                  sm2LucasReal u j) +
              sm2LucasReal u (j + 1)) +
          (4 * sm2LucasReal u (j + 1) +
            sm2LucasReal u j) =
          72 * sm2LucasReal u (j + 1) +
            17 * sm2LucasReal u j := by ring
      _ = sm2LucasReal u j := by
        rw [show (72 : ZMod 8) = 0 by decide,
          show (17 : ZMod 8) = 1 by decide]
        ring
  have hreduce := hperiod.map_mod_nat n
  have hcast :
      (sm2LucasReal u n : ZMod 8) =
        (sm2LucasRealResidue n : ZMod 8) := by
    rw [← hreduce]
    have hlt : n % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases h : n % 4 <;>
      simp [sm2LucasRealResidue, sm2LucasReal, huBaseCast, h]
    all_goals decide
  have hmod :=
    (ZMod.natCast_eq_natCast_iff'
      (sm2LucasReal u n) (sm2LucasRealResidue n) 8).mp hcast
  have hresidue_lt : sm2LucasRealResidue n < 8 := by
    simp only [sm2LucasRealResidue]
    split <;> omega
  exact hmod.trans (Nat.mod_eq_of_lt hresidue_lt)

/-- In the phase used by the outer-prime obstruction, the intermediate real
coordinate is six modulo eight. -/
theorem sm2LucasReal_mod_eight_of_index_mod_four_three
    {u n : Nat} (hu : u % 8 = 2) (hn : n % 4 = 3) :
    sm2LucasReal u n % 8 = 6 := by
  rw [sm2LucasReal_mod_eight hu]
  simp [sm2LucasRealResidue, hn]

/-- Addition law for the normalized ordinate recurrence. -/
theorem sm2LucasCoeff_add_succ
    (u m n : Nat) :
    sm2LucasCoeff u (m + n + 1) =
      sm2LucasCoeff u (m + 1) * sm2LucasCoeff u (n + 1) +
        sm2LucasCoeff u m * sm2LucasCoeff u n := by
  induction m using Nat.twoStepInduction with
  | zero =>
      simp
  | one =>
      simp [show 1 + n + 1 = n + 2 by omega,
        sm2LucasCoeff_succ_succ]
  | more m h0 h1 =>
      have h1' :
          sm2LucasCoeff u (m + n + 2) =
            sm2LucasCoeff u (m + 2) *
                sm2LucasCoeff u (n + 1) +
              sm2LucasCoeff u (m + 1) *
                sm2LucasCoeff u n := by
        simpa only
          [show m + 1 + n + 1 = m + n + 2 by omega,
            show m + 1 + 1 = m + 2 by omega] using h1
      have hleft :
          sm2LucasCoeff u (m + n + 3) =
            2 * u * sm2LucasCoeff u (m + n + 2) +
              sm2LucasCoeff u (m + n + 1) := by
        simpa only [show m + n + 3 = (m + n + 1) + 2 by omega]
          using sm2LucasCoeff_succ_succ u (m + n + 1)
      have hright :
          sm2LucasCoeff u (m + 3) =
            2 * u * sm2LucasCoeff u (m + 2) +
              sm2LucasCoeff u (m + 1) := by
        simpa only [show m + 3 = (m + 1) + 2 by omega]
          using sm2LucasCoeff_succ_succ u (m + 1)
      have hright0 :
          sm2LucasCoeff u (m + 2) =
            2 * u * sm2LucasCoeff u (m + 1) +
              sm2LucasCoeff u m :=
        sm2LucasCoeff_succ_succ u m
      calc
        sm2LucasCoeff u (m + 2 + n + 1) =
            2 * u * sm2LucasCoeff u (m + n + 2) +
              sm2LucasCoeff u (m + n + 1) := by
                simpa only
                  [show m + 2 + n + 1 = m + n + 3 by omega]
                  using hleft
        _ =
            2 * u *
                (sm2LucasCoeff u (m + 2) *
                    sm2LucasCoeff u (n + 1) +
                  sm2LucasCoeff u (m + 1) *
                    sm2LucasCoeff u n) +
              (sm2LucasCoeff u (m + 1) *
                    sm2LucasCoeff u (n + 1) +
                  sm2LucasCoeff u m *
                    sm2LucasCoeff u n) := by rw [h1', h0]
        _ =
            sm2LucasCoeff u (m + 2 + 1) *
                sm2LucasCoeff u (n + 1) +
              sm2LucasCoeff u (m + 2) *
                sm2LucasCoeff u n := by
                  rw [show m + 2 + 1 = m + 3 by omega, hright]
                  simp only [hright0]
                  ring

/-- Odd doubling law. -/
theorem sm2LucasCoeff_two_mul_add_one
    (u n : Nat) :
    sm2LucasCoeff u (2 * n + 1) =
      sm2LucasCoeff u (n + 1) ^ 2 +
        sm2LucasCoeff u n ^ 2 := by
  simpa [two_mul, pow_two] using
    sm2LucasCoeff_add_succ u n n

/-- Signed Cassini identity for the normalized ordinate recurrence. -/
theorem sm2LucasCoeff_cassini_int
    (u n : Nat) :
    (sm2LucasCoeff u (n + 1) : Int) ^ 2 -
        2 * u *
          sm2LucasCoeff u (n + 1) *
            sm2LucasCoeff u n -
        sm2LucasCoeff u n ^ 2 =
      (-1 : Int) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega,
        sm2LucasCoeff_succ_succ]
      push_cast
      calc
        (2 * (u : Int) * sm2LucasCoeff u (n + 1) +
                sm2LucasCoeff u n) ^ 2 -
              2 * u *
                (2 * u * sm2LucasCoeff u (n + 1) +
                  sm2LucasCoeff u n) *
                sm2LucasCoeff u (n + 1) -
              sm2LucasCoeff u (n + 1) ^ 2 =
            -((sm2LucasCoeff u (n + 1) : Int) ^ 2 -
              2 * u *
                sm2LucasCoeff u (n + 1) *
                  sm2LucasCoeff u n -
              sm2LucasCoeff u n ^ 2) := by ring
        _ = -((-1 : Int) ^ n) := by rw [ih]
        _ = (-1 : Int) ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- Cassini identity in the even-index orientation used below. -/
theorem sm2LucasCoeff_cassini_even
    (u m : Nat) :
    sm2LucasCoeff u (2 * m + 1) ^ 2 =
      sm2LucasCoeff u (2 * m) ^ 2 +
        2 * u *
          sm2LucasCoeff u (2 * m + 1) *
            sm2LucasCoeff u (2 * m) +
        1 := by
  have h := sm2LucasCoeff_cassini_int u (2 * m)
  norm_num [pow_mul] at h
  exact_mod_cast (by nlinarith :
    (sm2LucasCoeff u (2 * m + 1) : Int) ^ 2 =
      sm2LucasCoeff u (2 * m) ^ 2 +
        2 * u *
          sm2LucasCoeff u (2 * m + 1) *
            sm2LucasCoeff u (2 * m) + 1)

/-- The four-entry residue table for the normalized ordinate recurrence. -/
def sm2LucasResidue (n : Nat) : Nat :=
  match n % 4 with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | _ => 1

/-- The recurrence state has period four modulo eight when `u = 2 mod 4`. -/
theorem sm2LucasCoeff_mod_eight
    {u n : Nat} (hu : u % 4 = 2) :
    sm2LucasCoeff u n % 8 =
      sm2LucasResidue n := by
  have huCast : (2 * u : ZMod 8) = 4 := by
    have h :=
      (ZMod.natCast_eq_natCast_iff' (2 * u) 4 8).mpr
        (by omega)
    push_cast at h
    exact h
  have hperiod :
      Function.Periodic
        (fun j : Nat => (sm2LucasCoeff u j : ZMod 8)) 4 := by
    intro j
    change
      (sm2LucasCoeff u (j + 4) : ZMod 8) =
        (sm2LucasCoeff u j : ZMod 8)
    rw [show j + 4 = ((j + 2) + 2) by omega,
      sm2LucasCoeff_succ_succ,
      show j + 2 + 1 = (j + 1) + 2 by omega,
      sm2LucasCoeff_succ_succ,
      sm2LucasCoeff_succ_succ]
    push_cast
    rw [huCast]
    calc
      4 *
            (4 *
                (4 * (sm2LucasCoeff u (j + 1) : ZMod 8) +
                  sm2LucasCoeff u j) +
              sm2LucasCoeff u (j + 1)) +
          (4 * sm2LucasCoeff u (j + 1) +
            sm2LucasCoeff u j) =
          72 * sm2LucasCoeff u (j + 1) +
            17 * sm2LucasCoeff u j := by ring
      _ = sm2LucasCoeff u j := by
        rw [show (72 : ZMod 8) = 0 by decide,
          show (17 : ZMod 8) = 1 by decide]
        ring
  have hreduce := hperiod.map_mod_nat n
  have hcast :
      (sm2LucasCoeff u n : ZMod 8) =
        (sm2LucasResidue n : ZMod 8) := by
    rw [← hreduce]
    have hlt : n % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases h : n % 4 <;>
      simp [sm2LucasResidue, sm2LucasCoeff, huCast, h]
    all_goals decide
  have hmod :=
    (ZMod.natCast_eq_natCast_iff'
      (sm2LucasCoeff u n) (sm2LucasResidue n) 8).mp hcast
  have hresidue_lt : sm2LucasResidue n < 8 := by
    simp only [sm2LucasResidue]
    split <;> omega
  exact hmod.trans (Nat.mod_eq_of_lt hresidue_lt)

/-- The norm-minus-one unit satisfies its quadratic recurrence relation. -/
private theorem sm2UpperNegativeUnit_square
    {K u v : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2) :
    sm2UpperNegativeUnit K u v ^ 2 =
      (⟨2 * u, 0⟩ : ℤ√(K : Int)) *
          sm2UpperNegativeUnit K u v +
        1 := by
  apply Zsqrtd.ext
  · simp only [pow_two, Zsqrtd.re_mul, Zsqrtd.re_add,
      Zsqrtd.re_one, sm2UpperNegativeUnit]
    have h := congrArg (fun n : Nat => (n : Int)) hnegative
    push_cast at h
    nlinarith [h]
  · simp only [pow_two, Zsqrtd.im_mul, Zsqrtd.im_add,
      Zsqrtd.im_one, sm2UpperNegativeUnit]
    ring

/-- Powers of the selected norm-minus-one unit obey the same second-order
recurrence as their normalized ordinates. -/
private theorem sm2UpperNegativeUnit_pow_succ_succ
    {K u v : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (n : Nat) :
    sm2UpperNegativeUnit K u v ^ (n + 2) =
      (⟨2 * u, 0⟩ : ℤ√(K : Int)) *
          sm2UpperNegativeUnit K u v ^ (n + 1) +
        sm2UpperNegativeUnit K u v ^ n := by
  let eta := sm2UpperNegativeUnit K u v
  calc
    eta ^ (n + 2) = eta ^ n * eta ^ 2 := by
      rw [show n + 2 = n + 2 by rfl, pow_add]
    _ = eta ^ n * ((⟨2 * u, 0⟩ : ℤ√(K : Int)) * eta + 1) := by
      rw [sm2UpperNegativeUnit_square hnegative]
    _ =
        (⟨2 * u, 0⟩ : ℤ√(K : Int)) * eta ^ (n + 1) +
          eta ^ n := by
      rw [pow_succ]
      ring

/-- The ordinate of the `n`th norm-minus-one power is the root ordinate
times the normalized Lucas coefficient. -/
theorem sm2UpperNegativeUnit_pow_im
    {K u v : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (n : Nat) :
    (sm2UpperNegativeUnit K u v ^ n).im =
      (v : Int) * sm2LucasCoeff u n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [sm2UpperNegativeUnit]
  | one =>
      simp [sm2UpperNegativeUnit]
  | more n h0 h1 =>
      rw [sm2UpperNegativeUnit_pow_succ_succ hnegative]
      simp only [Zsqrtd.im_add, Zsqrtd.im_mul]
      rw [h1, h0, sm2LucasCoeff_succ_succ]
      push_cast
      ring

/-- The real coordinate of the `n`th norm-minus-one power is the companion
Lucas recurrence. -/
theorem sm2UpperNegativeUnit_pow_re
    {K u v : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (n : Nat) :
    (sm2UpperNegativeUnit K u v ^ n).re =
      sm2LucasReal u n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [sm2UpperNegativeUnit]
  | one =>
      simp [sm2UpperNegativeUnit]
  | more n h0 h1 =>
      rw [sm2UpperNegativeUnit_pow_succ_succ hnegative]
      simp only [Zsqrtd.re_add, Zsqrtd.re_mul]
      rw [h1, h0, sm2LucasReal_succ_succ]
      push_cast
      ring

/-- Both coordinates of a norm-minus-one power in the natural Lucas
normalization. -/
theorem sm2UpperNegativeUnit_pow_coordinates
    {K u v n : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2) :
    sm2UpperNegativeUnit K u v ^ n =
      (⟨sm2LucasReal u n,
          v * sm2LucasCoeff u n⟩ : ℤ√(K : Int)) := by
  apply Zsqrtd.ext
  · simpa using sm2UpperNegativeUnit_pow_re hnegative n
  · simpa using sm2UpperNegativeUnit_pow_im hnegative n

/-- The real coordinate of every odd power is divisible by the real
coordinate of its base point. -/
private theorem zsqrtd_real_dvd_odd_power_local
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

/-- Every odd power remains a positive natural norm-minus-one solution. -/
theorem sm2LucasReal_odd_negative_equation
    {K u v n : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hn : Odd n) :
    sm2LucasReal u n ^ 2 + 1 =
      K * (v * sm2LucasCoeff u n) ^ 2 := by
  let eta := sm2UpperNegativeUnit K u v
  have hetaNorm : Zsqrtd.norm eta = -1 := by
    simp only [eta, sm2UpperNegativeUnit, Zsqrtd.norm_def]
    have h := congrArg (fun z : Nat => (z : Int)) hnegative
    push_cast at h
    nlinarith
  have hpowNorm :
      Zsqrtd.norm (eta ^ n) = (-1 : Int) ^ n := by
    calc
      Zsqrtd.norm (eta ^ n) = Zsqrtd.norm eta ^ n :=
        map_pow Zsqrtd.normMonoidHom eta n
      _ = (-1 : Int) ^ n := by rw [hetaNorm]
  obtain ⟨m, hm⟩ := hn
  have hminus : (-1 : Int) ^ n = -1 := by
    rw [hm, pow_succ, pow_mul]
    norm_num
  have hcoords :=
    sm2UpperNegativeUnit_pow_coordinates
      (K := K) (u := u) (v := v) (n := n) hnegative
  rw [hcoords, Zsqrtd.norm_def, hminus] at hpowNorm
  push_cast at hpowNorm
  exact_mod_cast (by nlinarith :
    (sm2LucasReal u n : Int) ^ 2 + 1 =
      (K : Int) *
        ((v : Int) * sm2LucasCoeff u n) ^ 2)

/-- Canonical partial-powerful normal form at an odd intermediate power.
The factor `e` is precisely the squarefree part of the kernel depth not yet
acquired by the exponent. -/
theorem sm2NegativeUnit_odd_partial_depth_normal_form
    {K u v n : Nat}
    (hKsf : Squarefree K)
    (hv : 0 < v)
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hn : Odd n) :
    ∃ d e c : Nat,
      d = K.gcd (v * sm2LucasCoeff u n) ∧
        d =
          K.gcd v * (K / K.gcd v).gcd n ∧
        e = K / d ∧
        v * sm2LucasCoeff u n = d * c ∧
        K = e * d ∧
        e.Coprime d ∧
        e.Coprime c ∧
        sm2LucasReal u n ^ 2 + 1 =
          e * d ^ 3 * c ^ 2 := by
  let I := v * sm2LucasCoeff u n
  let d := K.gcd I
  let e := K / d
  have hdK : d ∣ K := Nat.gcd_dvd_left _ _
  have hdI : d ∣ I := Nat.gcd_dvd_right _ _
  obtain ⟨c, hc⟩ := hdI
  have hKed : K = e * d := by
    simpa [e] using (Nat.div_mul_cancel hdK).symm
  have hed : e.Coprime d := by
    apply Nat.coprime_of_squarefree_mul
    rw [← hKed]
    exact hKsf
  have hec : e.Coprime c := by
    rw [Nat.coprime_iff_gcd_eq_one]
    apply Nat.dvd_one.mp
    rw [← hed.gcd_eq_one]
    apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left e c
    · have hgd : e.gcd c ∣ d := by
        change e.gcd c ∣ K.gcd I
        apply Nat.dvd_gcd
        · exact (Nat.gcd_dvd_left e c).trans
            ⟨d, hKed⟩
        · exact (Nat.gcd_dvd_right e c).trans
            ⟨d, by simpa [mul_comm] using hc⟩
      exact hgd
  have hprofile :
      d = K.gcd v * (K / K.gcd v).gcd n := by
    simpa [d, I] using
      sm2NegativeUnit_ordinate_gcd_profile
        hKsf hv hnegative
  have hequation :
      sm2LucasReal u n ^ 2 + 1 =
        e * d ^ 3 * c ^ 2 := by
    calc
      sm2LucasReal u n ^ 2 + 1 =
          K * I ^ 2 := by
            simpa [I] using
              sm2LucasReal_odd_negative_equation hnegative hn
      _ = (e * d) * (d * c) ^ 2 := by rw [← hKed, ← hc]
      _ = e * d ^ 3 * c ^ 2 := by ring
  exact
    ⟨d, e, c, rfl, hprofile, rfl, hc, hKed, hed, hec,
      hequation⟩

/-- Modulo the normalized ordinate of an intermediate power, the real
coordinate of a further power is the corresponding power of the
intermediate real coordinate. -/
theorem sm2UpperNegativeUnit_mul_power_real_mod_coeff
    {K u v n s : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2) :
    ((((sm2UpperNegativeUnit K u v ^ (n * s)).re : Int) :
        ZMod (sm2LucasCoeff u n))) =
      (sm2LucasReal u n : ZMod (sm2LucasCoeff u n)) ^ s := by
  rw [pow_mul, sm2UpperNegativeUnit_pow_coordinates hnegative]
  induction s with
  | zero =>
      simp
  | succ s ih =>
      rw [pow_succ, Zsqrtd.re_mul]
      push_cast
      rw [ih]
      simp
      ring

/-- A square root of minus one is fixed by exponents one modulo four. -/
private theorem zmod_pow_eq_self_of_square_eq_neg_one_local
    {q A s : Nat}
    (hsquare : (A : ZMod q) ^ 2 = -1)
    (hphase : s % 4 = 1) :
    (A : ZMod q) ^ s = A := by
  have hs : s = 4 * (s / 4) + 1 := by
    have h := (Nat.mod_add_div s 4).symm
    rw [hphase] at h
    omega
  have hfour : (A : ZMod q) ^ 4 = 1 := by
    calc
      (A : ZMod q) ^ 4 = ((A : ZMod q) ^ 2) ^ 2 := by ring
      _ = (-1 : ZMod q) ^ 2 := by rw [hsquare]
      _ = 1 := by ring
  rw [hs, pow_add, pow_mul, hfour]
  simp

/-- A square root of minus one is negated by exponents three modulo four. -/
private theorem zmod_pow_eq_neg_self_of_square_eq_neg_one_local
    {q A s : Nat}
    (hsquare : (A : ZMod q) ^ 2 = -1)
    (hphase : s % 4 = 3) :
    (A : ZMod q) ^ s = -A := by
  have hs : s = 4 * (s / 4) + 3 := by
    have h := (Nat.mod_add_div s 4).symm
    rw [hphase] at h
    omega
  have hfour : (A : ZMod q) ^ 4 = 1 := by
    calc
      (A : ZMod q) ^ 4 = ((A : ZMod q) ^ 2) ^ 2 := by ring
      _ = (-1 : ZMod q) ^ 2 := by rw [hsquare]
      _ = 1 := by ring
  rw [hs, pow_add, pow_mul, hfour]
  calc
    (1 : ZMod q) ^ (s / 4) * (A : ZMod q) ^ 3 =
        (A : ZMod q) ^ 3 := by simp
    _ = (A : ZMod q) ^ 2 * A := by ring
    _ = -(A : ZMod q) := by rw [hsquare]; ring

/-- An odd intermediate norm-minus-one real coordinate is a square root of
minus one modulo its normalized ordinate. -/
theorem sm2LucasReal_sq_eq_neg_one_mod_coeff
    {K u v n : Nat}
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hn : Odd n) :
    (sm2LucasReal u n : ZMod (sm2LucasCoeff u n)) ^ 2 = -1 := by
  have heq :=
    congrArg
      (fun z : Nat => (z : ZMod (sm2LucasCoeff u n)))
      (sm2LucasReal_odd_negative_equation hnegative hn)
  push_cast at heq
  simpa using (eq_neg_of_add_eq_zero_left (by
    simpa using heq))

/-- Consecutive normalized ordinates are coprime. -/
theorem sm2LucasCoeff_consecutive_coprime
    (u n : Nat) :
    Nat.Coprime
      (sm2LucasCoeff u (n + 1))
      (sm2LucasCoeff u n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega,
        sm2LucasCoeff_succ_succ]
      have h :=
        (Nat.coprime_add_mul_left_left
          (sm2LucasCoeff u n)
          (sm2LucasCoeff u (n + 1))
          (2 * u)).mpr ih.symm
      simpa [mul_comm, add_comm] using h

/-- Consecutive normalized ordinates at the even half-index are coprime. -/
theorem sm2LucasCoeff_even_consecutive_coprime
    (u m : Nat) :
    Nat.Coprime
      (sm2LucasCoeff u (2 * m + 1))
      (sm2LucasCoeff u (2 * m)) := by
  let S := sm2LucasCoeff u (2 * m + 1)
  let T := sm2LucasCoeff u (2 * m)
  let g := Nat.gcd S T
  have hS : g ∣ S := Nat.gcd_dvd_left S T
  have hT : g ∣ T := Nat.gcd_dvd_right S T
  have hSsq : g ∣ S ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hS S
  have hTsq : g ∣ T ^ 2 := by
    simpa [pow_two] using dvd_mul_of_dvd_left hT T
  have hcross : g ∣ 2 * u * S * T := by
    exact dvd_mul_of_dvd_right hT _
  have hrest : g ∣ T ^ 2 + 2 * u * S * T :=
    Nat.dvd_add hTsq hcross
  have htotal : g ∣ T ^ 2 + 2 * u * S * T + 1 := by
    rw [← sm2LucasCoeff_cassini_even u m]
    exact hSsq
  have hone : g ∣ 1 :=
    (Nat.dvd_add_iff_left hrest).mpr
      (by simpa [Nat.add_comm] using htotal)
  have hg : g = 1 := Nat.eq_one_of_dvd_one hone
  exact (Nat.coprime_iff_gcd_eq_one).mpr hg

/-- Pure Jacobi endpoint for the `5 mod 8` half-power shell. -/
theorem jacobi_predecessor_eq_neg_one_of_half_shell
    {P S T U : Nat}
    (hS : S % 8 = 1)
    (hT : T % 8 = 4)
    (hUeq : U = S ^ 2 + T ^ 2)
    (hcoprime : Nat.Coprime S T)
    (hsource :
      Int.ModEq U
        (((P : Int) - 1) * T)
        (-(S + T : Nat))) :
    jacobiSym ((P : Int) - 1) U = -1 := by
  let t := T / 4
  have hTform : T = 8 * (T / 8) + 4 := by
    have h := (Nat.mod_add_div T 8).symm
    rw [hT] at h
    omega
  have htEq : t = 2 * (T / 8) + 1 := by
    dsimp [t]
    rw [hTform]
    omega
  have htOdd : Odd t := by
    rw [Nat.odd_iff, htEq]
    omega
  have htPos : 0 < t := by omega
  have htDvdT : t ∣ T := by
    rw [hTform, htEq]
    exact ⟨4, by ring⟩
  have hTFour : T = 4 * t := by
    rw [hTform, htEq]
    ring
  have hSt : Nat.Coprime S t :=
    hcoprime.of_dvd_right htDvdT
  have hHcoprime : Nat.Coprime T (S + T) := by
    exact (Nat.coprime_add_self_right).mpr hcoprime.symm
  have hU8 : U % 8 = 1 := by
    rw [hUeq]
    have hScast : (S : ZMod 8) = 1 :=
      (ZMod.natCast_eq_natCast_iff' S 1 8).mpr hS
    have hTcast : (T : ZMod 8) = 4 :=
      (ZMod.natCast_eq_natCast_iff' T 4 8).mpr hT
    apply (ZMod.natCast_eq_natCast_iff' _ 1 8).mp
    push_cast
    rw [hScast, hTcast]
    decide
  have hU4 : U % 4 = 1 := by
    have hmod := Nat.mod_mod_of_dvd U (by decide : 4 ∣ 8)
    rw [hU8] at hmod
    omega
  have hUOdd : Odd U :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hU4)
  have hH8 : (S + T) % 8 = 5 := by omega
  have hH4 : (S + T) % 4 = 1 := by
    have hmod :=
      Nat.mod_mod_of_dvd (S + T) (by decide : 4 ∣ 8)
    rw [hH8] at hmod
    omega
  have hHOdd : Odd (S + T) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hH4)
  have hTU' : Nat.Coprime T U := by
    rw [hUeq, pow_two T,
      Nat.coprime_add_mul_left_right,
      Nat.coprime_pow_right_iff (by decide : 0 < 2)]
    exact hcoprime.symm
  have htU : Int.gcd (t : Int) U = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact (hTU'.of_dvd_left htDvdT).gcd_eq_one
  have hTH : Int.gcd (T : Int) (S + T) = 1 := by
    change Int.gcd (T : Int) ((S + T : Nat) : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact hHcoprime.gcd_eq_one
  have hJtU : jacobiSym (t : Int) U = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four'
      htOdd hU4]
    have hmod :
        Int.ModEq t (U : Int) ((S : Int) ^ 2) := by
      rw [Int.modEq_iff_dvd, hUeq]
      push_cast
      have htDvdTInt : (t : Int) ∣ (T : Int) := by
        exact_mod_cast htDvdT
      have htDvdTsq : (t : Int) ∣ (T : Int) ^ 2 := by
        simpa [pow_two] using
          dvd_mul_of_dvd_left htDvdTInt (T : Int)
      rw [show (S : Int) ^ 2 -
          ((S : Int) ^ 2 + (T : Int) ^ 2) =
        -(T : Int) ^ 2 by ring]
      exact dvd_neg.mpr htDvdTsq
    rw [jacobiSym.mod_left' hmod]
    exact jacobiSym.sq_one' (by
      rw [Int.gcd_natCast_natCast]
      exact hSt.gcd_eq_one)
  have hJTU : jacobiSym (T : Int) U = 1 := by
    rw [hTFour]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.at_four hUOdd, hJtU]
    norm_num
  have hJHU : jacobiSym (S + T : Int) U = -1 := by
    change jacobiSym ((S + T : Nat) : Int) U = -1
    rw [jacobiSym.quadratic_reciprocity_one_mod_four'
      hHOdd hU4]
    have hmod :
        Int.ModEq (S + T) (U : Int)
          (2 * (T : Int) ^ 2) := by
      apply Int.modEq_of_dvd
      rw [hUeq]
      push_cast
      exact ⟨(T : Int) - S, by ring⟩
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left,
      jacobiSym.sq_one' hTH, mul_one,
      jacobiSym.at_two hHOdd,
      ZMod.χ₈_nat_eq_if_mod_eight]
    have hH2 : (S + T) % 2 = 1 := Nat.odd_iff.mp hHOdd
    simp [hH8, hH2]
  calc
    jacobiSym ((P : Int) - 1) U =
        jacobiSym (((P : Int) - 1) * T) U := by
          rw [jacobiSym.mul_left, hJTU, mul_one]
    _ = jacobiSym (-(S + T : Nat) : Int) U :=
      jacobiSym.mod_left' hsource
    _ = jacobiSym (S + T : Int) U := by
      rw [jacobiSym.neg _ hUOdd,
        ZMod.χ₄_nat_one_mod_four hU4, one_mul]
      rfl
    _ = -1 := hJHU

/-- Pure Jacobi endpoint for the signed successor at the complementary
`3 mod 8` half-power shell. -/
theorem jacobi_signed_successor_eq_neg_one_of_half_shell
    {P S T U : Nat}
    (hS : S % 8 = 4)
    (hT : T % 8 = 1)
    (hUeq : U = S ^ 2 + T ^ 2)
    (hcoprime : Nat.Coprime S T)
    (hsource :
      Int.ModEq U
        (-(((P : Int) + 1) * T))
        (-(S + T : Nat))) :
    jacobiSym (-((P : Int) + 1)) U = -1 := by
  have hU8 : U % 8 = 1 := by
    rw [hUeq]
    have hScast : (S : ZMod 8) = 4 :=
      (ZMod.natCast_eq_natCast_iff' S 4 8).mpr hS
    have hTcast : (T : ZMod 8) = 1 :=
      (ZMod.natCast_eq_natCast_iff' T 1 8).mpr hT
    apply (ZMod.natCast_eq_natCast_iff' _ 1 8).mp
    push_cast
    rw [hScast, hTcast]
    decide
  have hU4 : U % 4 = 1 := by
    have hmod := Nat.mod_mod_of_dvd U (by decide : 4 ∣ 8)
    rw [hU8] at hmod
    omega
  have hUOdd : Odd U :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hU4)
  have hTOdd : Odd T := by
    rw [Nat.odd_iff]
    omega
  have hH8 : (S + T) % 8 = 5 := by omega
  have hH4 : (S + T) % 4 = 1 := by
    have hmod :=
      Nat.mod_mod_of_dvd (S + T) (by decide : 4 ∣ 8)
    rw [hH8] at hmod
    omega
  have hHOdd : Odd (S + T) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hH4)
  have hTU : Nat.Coprime T U := by
    rw [hUeq, pow_two T,
      Nat.coprime_add_mul_left_right,
      Nat.coprime_pow_right_iff (by decide : 0 < 2)]
    exact hcoprime.symm
  have hTH : Int.gcd (T : Int) (S + T) = 1 := by
    change Int.gcd (T : Int) ((S + T : Nat) : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.coprime_add_self_right).mpr
      hcoprime.symm).gcd_eq_one
  have hJTU : jacobiSym (T : Int) U = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four'
      hTOdd hU4]
    have hmod :
        Int.ModEq T (U : Int) ((S : Int) ^ 2) := by
      apply Int.modEq_of_dvd
      rw [hUeq]
      push_cast
      exact ⟨-(T : Int), by ring⟩
    rw [jacobiSym.mod_left' hmod]
    exact jacobiSym.sq_one' (by
      rw [Int.gcd_natCast_natCast]
      exact hcoprime.gcd_eq_one)
  have hJHU : jacobiSym (S + T : Int) U = -1 := by
    change jacobiSym ((S + T : Nat) : Int) U = -1
    rw [jacobiSym.quadratic_reciprocity_one_mod_four'
      hHOdd hU4]
    have hmod :
        Int.ModEq (S + T) (U : Int)
          (2 * (T : Int) ^ 2) := by
      apply Int.modEq_of_dvd
      rw [hUeq]
      push_cast
      exact ⟨(T : Int) - S, by ring⟩
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left,
      jacobiSym.sq_one' hTH, mul_one,
      jacobiSym.at_two hHOdd,
      ZMod.χ₈_nat_eq_if_mod_eight]
    have hH2 : (S + T) % 2 = 1 := Nat.odd_iff.mp hHOdd
    simp [hH8, hH2]
  calc
    jacobiSym (-((P : Int) + 1)) U =
        jacobiSym (-((P : Int) + 1) * T) U := by
          rw [jacobiSym.mul_left, hJTU, mul_one]
    _ = jacobiSym (-(S + T : Nat) : Int) U :=
      jacobiSym.mod_left' hsource
    _ = jacobiSym (S + T : Int) U := by
      rw [jacobiSym.neg _ hUOdd,
        ZMod.χ₄_nat_one_mod_four hU4, one_mul]
      rfl
    _ = -1 := hJHU

/-- The half-power identity which supplies the Jacobi congruence at an
exponent `8*s+5`. -/
theorem sm2UpperNegativeUnit_rank_five_half_shell
    {K u v P Q s : Nat}
    (hv : 0 < v)
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hpower :
      sm2UpperNegativeUnit K u v ^ (8 * s + 5) =
        (⟨P, Q⟩ : ℤ√(K : Int))) :
    let T := sm2LucasCoeff u (4 * s + 2)
    let S := sm2LucasCoeff u (4 * s + 3)
    let U := S ^ 2 + T ^ 2
    Q = v * U ∧
      Int.ModEq U
        (((P : Int) - 1) * T)
        (-(S + T : Nat)) := by
  let eta := sm2UpperNegativeUnit K u v
  let n := 4 * s + 2
  let T := sm2LucasCoeff u n
  let S := sm2LucasCoeff u (n + 1)
  let U := S ^ 2 + T ^ 2
  let A : Int := (eta ^ n).re
  let C : Int := (eta ^ (n + 1)).re
  have hR : 8 * s + 5 = 2 * n + 1 := by
    dsimp [n]
    omega
  have hTIm : (eta ^ n).im = (v : Int) * T := by
    simpa [eta, T] using
      sm2UpperNegativeUnit_pow_im hnegative n
  have hSIm : (eta ^ (n + 1)).im = (v : Int) * S := by
    simpa [eta, S] using
      sm2UpperNegativeUnit_pow_im hnegative (n + 1)
  have hUeq :
      sm2LucasCoeff u (2 * n + 1) = U := by
    simpa [U, S, T] using
      sm2LucasCoeff_two_mul_add_one u n
  have hQInt :
      (Q : Int) = (v : Int) * U := by
    have him := congrArg Zsqrtd.im hpower
    have hfullIm :=
      sm2UpperNegativeUnit_pow_im hnegative (2 * n + 1)
    rw [hR] at him
    change (eta ^ (2 * n + 1)).im = (Q : Int) at him
    rw [hfullIm, hUeq] at him
    exact him.symm
  have hQ : Q = v * U := by
    exact_mod_cast hQInt
  have hnext :
      eta ^ (n + 1) = eta ^ n * eta := by
    simp [pow_succ]
  have hSscaled :
      (v : Int) * S =
        (v : Int) * (A + (u : Int) * T) := by
    have him := congrArg Zsqrtd.im hnext
    simp only [Zsqrtd.im_mul] at him
    rw [hTIm, hSIm] at him
    change
      (v : Int) * S =
        A * v + (v : Int) * T * u at him
    calc
      (v : Int) * S = A * v + (v : Int) * T * u := him
      _ = (v : Int) * (A + (u : Int) * T) := by ring
  have hvInt : (v : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  have hSrel :
      (S : Int) = A + (u : Int) * T :=
    mul_left_cancel₀ hvInt hSscaled
  have hCrel :
      C =
        (u : Int) * A +
          (K : Int) * v ^ 2 * T := by
    have hre := congrArg Zsqrtd.re hnext
    simp only [Zsqrtd.re_mul] at hre
    rw [hTIm] at hre
    change
      C = A * u + (K : Int) * ((v : Int) * T) * v at hre
    calc
      C = A * u + (K : Int) * ((v : Int) * T) * v := hre
      _ = (u : Int) * A + (K : Int) * v ^ 2 * T := by ring
  have hfull :
      eta ^ (2 * n + 1) = eta ^ n * eta ^ (n + 1) := by
    rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
  have hPrel :
      (P : Int) =
        A * C +
          (K : Int) * v ^ 2 * T * S := by
    have hre := congrArg Zsqrtd.re hfull
    simp only [Zsqrtd.re_mul] at hre
    rw [hTIm, hSIm] at hre
    have hpRe := congrArg Zsqrtd.re hpower
    rw [hR] at hpRe
    change (eta ^ (2 * n + 1)).re = (P : Int) at hpRe
    rw [hpRe] at hre
    change
      (P : Int) =
        A * C +
          (K : Int) * ((v : Int) * T) * ((v : Int) * S)
      at hre
    calc
      (P : Int) =
          A * C +
            (K : Int) * ((v : Int) * T) * ((v : Int) * S) := hre
      _ = A * C + (K : Int) * v ^ 2 * T * S := by ring
  have hetaNorm : Zsqrtd.norm eta = -1 := by
    simp only [eta, sm2UpperNegativeUnit, Zsqrtd.norm_def]
    have h := congrArg (fun z : Nat => (z : Int)) hnegative
    push_cast at h
    nlinarith
  have hdeltaNorm : Zsqrtd.norm (eta ^ n) = 1 := by
    calc
      Zsqrtd.norm (eta ^ n) = Zsqrtd.norm eta ^ n :=
        map_pow Zsqrtd.normMonoidHom eta n
      _ = (-1 : Int) ^ n := by rw [hetaNorm]
      _ = 1 := by
        dsimp [n]
        rw [show 4 * s + 2 = 2 * (2 * s + 1) by omega,
          pow_mul]
        norm_num
  have hnorm :
      A ^ 2 - (K : Int) * v ^ 2 * T ^ 2 = 1 := by
    rw [Zsqrtd.norm_def] at hdeltaNorm
    rw [hTIm] at hdeltaNorm
    change
      A * A - (K : Int) * ((v : Int) * T) * ((v : Int) * T) =
        1 at hdeltaNorm
    nlinarith
  have hnegativeInt :
      (u : Int) ^ 2 + 1 = (K : Int) * v ^ 2 := by
    exact_mod_cast hnegative
  have hkey :
      (P : Int) * T + S = A * U := by
    dsimp [U]
    rw [hPrel, hCrel, hSrel]
    linear_combination
      -(A + (u : Int) * T) * hnorm -
        A * T ^ 2 * hnegativeInt
  refine ⟨hQ, ?_⟩
  apply Int.modEq_of_dvd
  change
    (U : Int) ∣
      (-(S + T : Nat) : Int) -
        (((P : Int) - 1) * T)
  refine ⟨-A, ?_⟩
  push_cast
  linear_combination -hkey

/-- The complementary half-power identity at an exponent `8*s+3`.  Its
signed-successor congruence is the second Jacobi orientation needed for
divisor-block transfer. -/
theorem sm2UpperNegativeUnit_rank_three_half_shell
    {K u v P Q s : Nat}
    (hv : 0 < v)
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hpower :
      sm2UpperNegativeUnit K u v ^ (8 * s + 3) =
        (⟨P, Q⟩ : ℤ√(K : Int))) :
    let T := sm2LucasCoeff u (4 * s + 1)
    let S := sm2LucasCoeff u (4 * s + 2)
    let U := S ^ 2 + T ^ 2
    Q = v * U ∧
      Int.ModEq U
        (-(((P : Int) + 1) * T))
        (-(S + T : Nat)) := by
  let eta := sm2UpperNegativeUnit K u v
  let n := 4 * s + 1
  let T := sm2LucasCoeff u n
  let S := sm2LucasCoeff u (n + 1)
  let U := S ^ 2 + T ^ 2
  let A : Int := (eta ^ n).re
  let C : Int := (eta ^ (n + 1)).re
  have hR : 8 * s + 3 = 2 * n + 1 := by
    dsimp [n]
    omega
  have hTIm : (eta ^ n).im = (v : Int) * T := by
    simpa [eta, T] using
      sm2UpperNegativeUnit_pow_im hnegative n
  have hSIm : (eta ^ (n + 1)).im = (v : Int) * S := by
    simpa [eta, S] using
      sm2UpperNegativeUnit_pow_im hnegative (n + 1)
  have hUeq :
      sm2LucasCoeff u (2 * n + 1) = U := by
    simpa [U, S, T] using
      sm2LucasCoeff_two_mul_add_one u n
  have hQInt :
      (Q : Int) = (v : Int) * U := by
    have him := congrArg Zsqrtd.im hpower
    have hfullIm :=
      sm2UpperNegativeUnit_pow_im hnegative (2 * n + 1)
    rw [hR] at him
    change (eta ^ (2 * n + 1)).im = (Q : Int) at him
    rw [hfullIm, hUeq] at him
    exact him.symm
  have hQ : Q = v * U := by
    exact_mod_cast hQInt
  have hnext :
      eta ^ (n + 1) = eta ^ n * eta := by
    simp [pow_succ]
  have hSscaled :
      (v : Int) * S =
        (v : Int) * (A + (u : Int) * T) := by
    have him := congrArg Zsqrtd.im hnext
    simp only [Zsqrtd.im_mul] at him
    rw [hTIm, hSIm] at him
    change
      (v : Int) * S =
        A * v + (v : Int) * T * u at him
    calc
      (v : Int) * S = A * v + (v : Int) * T * u := him
      _ = (v : Int) * (A + (u : Int) * T) := by ring
  have hvInt : (v : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv)
  have hSrel :
      (S : Int) = A + (u : Int) * T :=
    mul_left_cancel₀ hvInt hSscaled
  have hCrel :
      C =
        (u : Int) * A +
          (K : Int) * v ^ 2 * T := by
    have hre := congrArg Zsqrtd.re hnext
    simp only [Zsqrtd.re_mul] at hre
    rw [hTIm] at hre
    change
      C = A * u + (K : Int) * ((v : Int) * T) * v at hre
    calc
      C = A * u + (K : Int) * ((v : Int) * T) * v := hre
      _ = (u : Int) * A + (K : Int) * v ^ 2 * T := by ring
  have hfull :
      eta ^ (2 * n + 1) = eta ^ n * eta ^ (n + 1) := by
    rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
  have hPrel :
      (P : Int) =
        A * C +
          (K : Int) * v ^ 2 * T * S := by
    have hre := congrArg Zsqrtd.re hfull
    simp only [Zsqrtd.re_mul] at hre
    rw [hTIm, hSIm] at hre
    have hpRe := congrArg Zsqrtd.re hpower
    rw [hR] at hpRe
    change (eta ^ (2 * n + 1)).re = (P : Int) at hpRe
    rw [hpRe] at hre
    change
      (P : Int) =
        A * C +
          (K : Int) * ((v : Int) * T) * ((v : Int) * S)
      at hre
    calc
      (P : Int) =
          A * C +
            (K : Int) * ((v : Int) * T) * ((v : Int) * S) := hre
      _ = A * C + (K : Int) * v ^ 2 * T * S := by ring
  have hetaNorm : Zsqrtd.norm eta = -1 := by
    simp only [eta, sm2UpperNegativeUnit, Zsqrtd.norm_def]
    have h := congrArg (fun z : Nat => (z : Int)) hnegative
    push_cast at h
    nlinarith
  have hdeltaNorm : Zsqrtd.norm (eta ^ n) = -1 := by
    calc
      Zsqrtd.norm (eta ^ n) = Zsqrtd.norm eta ^ n :=
        map_pow Zsqrtd.normMonoidHom eta n
      _ = (-1 : Int) ^ n := by rw [hetaNorm]
      _ = -1 := by
        dsimp [n]
        rw [show 4 * s + 1 = 2 * (2 * s) + 1 by omega,
          pow_succ, pow_mul]
        norm_num
  have hnorm :
      A ^ 2 - (K : Int) * v ^ 2 * T ^ 2 = -1 := by
    rw [Zsqrtd.norm_def] at hdeltaNorm
    rw [hTIm] at hdeltaNorm
    change
      A * A - (K : Int) * ((v : Int) * T) * ((v : Int) * T) =
        -1 at hdeltaNorm
    nlinarith
  have hnegativeInt :
      (u : Int) ^ 2 + 1 = (K : Int) * v ^ 2 := by
    exact_mod_cast hnegative
  have hkey :
      (P : Int) * T - S = A * U := by
    dsimp [U]
    rw [hPrel, hCrel, hSrel]
    linear_combination
      -(A + (u : Int) * T) * hnorm -
        A * T ^ 2 * hnegativeInt
  refine ⟨hQ, ?_⟩
  apply Int.modEq_of_dvd
  change
    (U : Int) ∣
      (-(S + T : Nat) : Int) -
        (-(((P : Int) + 1) * T))
  refine ⟨A, ?_⟩
  push_cast
  linear_combination hkey

/-- The normalized predecessor has Jacobi symbol minus one at every
`5 mod 8` odd power. -/
theorem jacobi_sm2LucasReal_predecessor_of_mod_eight_five
    {K u v n : Nat}
    (hv : 0 < v)
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2)
    (hn : n % 8 = 5) :
    jacobiSym ((sm2LucasReal u n : Int) - 1)
        (sm2LucasCoeff u n) = -1 := by
  let s := n / 8
  let T := sm2LucasCoeff u (4 * s + 2)
  let S := sm2LucasCoeff u (4 * s + 3)
  let U := S ^ 2 + T ^ 2
  have hnform : n = 8 * s + 5 := by
    have h := (Nat.mod_add_div n 8).symm
    rw [hn] at h
    dsimp [s]
    omega
  have hpower :
      sm2UpperNegativeUnit K u v ^ (8 * s + 5) =
        (⟨sm2LucasReal u n,
            v * sm2LucasCoeff u n⟩ : ℤ√(K : Int)) := by
    rw [← hnform]
    exact sm2UpperNegativeUnit_pow_coordinates hnegative
  have hshell :=
    sm2UpperNegativeUnit_rank_five_half_shell
      hv hnegative hpower
  have hshellMod :
      Int.ModEq U
        (((sm2LucasReal u n : Int) - 1) * T)
        (-(S + T : Nat)) := by
    simpa [T, S, U] using hshell.2
  have hT : T % 8 = 4 := by
    have hmod :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 2) hu
    simpa [T, sm2LucasResidue,
      show (4 * s + 2) % 4 = 2 by omega] using hmod
  have hS : S % 8 = 1 := by
    have hmod :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 3) hu
    simpa [S, sm2LucasResidue,
      show (4 * s + 3) % 4 = 3 by omega] using hmod
  have hcoprime : Nat.Coprime S T := by
    simpa only [S, T] using
      sm2LucasCoeff_consecutive_coprime u (4 * s + 2)
  have hJ :
      jacobiSym ((sm2LucasReal u n : Int) - 1) U = -1 :=
    jacobi_predecessor_eq_neg_one_of_half_shell
      hS hT rfl hcoprime hshellMod
  have hCoeff :
      sm2LucasCoeff u n = U := by
    rw [hnform]
    simpa [T, S, U,
      show 8 * s + 5 = 2 * (4 * s + 2) + 1 by omega] using
        sm2LucasCoeff_two_mul_add_one u (4 * s + 2)
  rw [hCoeff]
  exact hJ

/-- The signed successor has Jacobi symbol minus one at every `3 mod 8`
odd power. -/
theorem jacobi_sm2LucasReal_signed_successor_of_mod_eight_three
    {K u v n : Nat}
    (hv : 0 < v)
    (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2)
    (hn : n % 8 = 3) :
    jacobiSym (-((sm2LucasReal u n : Int) + 1))
        (sm2LucasCoeff u n) = -1 := by
  let s := n / 8
  let T := sm2LucasCoeff u (4 * s + 1)
  let S := sm2LucasCoeff u (4 * s + 2)
  let U := S ^ 2 + T ^ 2
  have hnform : n = 8 * s + 3 := by
    have h := (Nat.mod_add_div n 8).symm
    rw [hn] at h
    dsimp [s]
    omega
  have hpower :
      sm2UpperNegativeUnit K u v ^ (8 * s + 3) =
        (⟨sm2LucasReal u n,
            v * sm2LucasCoeff u n⟩ : ℤ√(K : Int)) := by
    rw [← hnform]
    exact sm2UpperNegativeUnit_pow_coordinates hnegative
  have hshell :=
    sm2UpperNegativeUnit_rank_three_half_shell
      hv hnegative hpower
  have hshellMod :
      Int.ModEq U
        (-(((sm2LucasReal u n : Int) + 1) * T))
        (-(S + T : Nat)) := by
    simpa [T, S, U] using hshell.2
  have hT : T % 8 = 1 := by
    have hmod :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 1) hu
    simpa [T, sm2LucasResidue,
      show (4 * s + 1) % 4 = 1 by omega] using hmod
  have hS : S % 8 = 4 := by
    have hmod :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 2) hu
    simpa [S, sm2LucasResidue,
      show (4 * s + 2) % 4 = 2 by omega] using hmod
  have hcoprime : Nat.Coprime S T := by
    simpa only [S, T] using
      sm2LucasCoeff_consecutive_coprime u (4 * s + 1)
  have hJ :
      jacobiSym (-((sm2LucasReal u n : Int) + 1)) U = -1 :=
    jacobi_signed_successor_eq_neg_one_of_half_shell
      hS hT rfl hcoprime hshellMod
  have hCoeff :
      sm2LucasCoeff u n = U := by
    rw [hnform]
    simpa [T, S, U,
      show 8 * s + 3 = 2 * (4 * s + 1) + 1 by omega] using
        sm2LucasCoeff_two_mul_add_one u (4 * s + 1)
  rw [hCoeff]
  exact hJ

/-- A positive negative-Pell real coordinate over a `5 mod 8` kernel is
`2 mod 4`. -/
theorem negativePell_real_mod_four_of_kernel_mod_eight_five
    {K u v : Nat}
    (hK : K % 8 = 5)
    (hnegative : u ^ 2 + 1 = K * v ^ 2) :
    u % 4 = 2 := by
  have hcast :=
    congrArg (fun n : Nat => (n : ZMod 8)) hnegative
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

private theorem divisor_mod_four_eq_one_of_prime_support
    {K R : Nat} (hKsf : Squarefree K) (hR : R ∣ K)
    (hprime : ∀ p : Nat, p.Prime → p ∣ K → p % 4 = 1) :
    R % 4 = 1 := by
  have hRsf : Squarefree R := hKsf.squarefree_of_dvd hR
  have hprod : ∏ p ∈ R.primeFactors, p = R :=
    Nat.prod_primeFactors_of_squarefree hRsf
  apply (ZMod.natCast_eq_natCast_iff' R 1 4).mp
  rw [← hprod]
  push_cast
  apply Finset.prod_eq_one
  intro p hp
  apply (ZMod.natCast_eq_natCast_iff' p 1 4).mpr
  exact hprime p (Nat.prime_of_mem_primeFactors hp)
    ((Nat.dvd_of_mem_primeFactors hp).trans hR)

private theorem gcd_mul_eq_right_of_coprime_left
    {K a b : Nat} (hcop : K.Coprime a) :
    K.gcd (a * b) = K.gcd b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · have hdCop : (K.gcd (a * b)).Coprime a :=
        hcop.of_dvd_left (Nat.gcd_dvd_left _ _)
      exact hdCop.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · exact (Nat.gcd_dvd_right _ _).trans
        (dvd_mul_of_dvd_right dvd_rfl a)

private theorem kernel_coprime_two_mul_negativePell_root
    {K u v : Nat} (hKOdd : Odd K)
    (hnegative : u ^ 2 + 1 = K * v ^ 2) :
    K.Coprime (2 * u) := by
  have hKu : K.Coprime u := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hdivu : K.gcd u ∣ u ^ 2 := by
      simpa [pow_two] using
        dvd_mul_of_dvd_left (Nat.gcd_dvd_right K u) u
    have hdivsum : K.gcd u ∣ u ^ 2 + 1 := by
      rw [hnegative]
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left K u) (v ^ 2)
    exact Nat.eq_one_of_dvd_one
      ((Nat.dvd_add_iff_right hdivu).mpr hdivsum)
  exact (Nat.coprime_two_right.mpr hKOdd).mul_right hKu

private theorem exists_prime_mod_eight_five_of_squarefree
    {G : Nat} (hGsf : Squarefree G) (hG8 : G % 8 = 5)
    (hprime :
      ∀ p : Nat, p.Prime → p ∣ G → p % 4 = 1) :
    ∃ q : Nat, q.Prime ∧ q ∣ G ∧ q % 8 = 5 := by
  by_contra hnone
  have hnot :
      ∀ q : Nat, q.Prime → q ∣ G → q % 8 ≠ 5 := by
    intro q hq hqG hqFive
    exact hnone ⟨q, hq, hqG, hqFive⟩
  have hall :
      ∀ p ∈ G.primeFactors, p % 8 = 1 := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    have hpFour := hprime p hpPrime hpDvd
    have hpMod :=
      Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
    have hpLt : p % 8 < 8 := Nat.mod_lt _ (by decide)
    have hpNotFive := hnot p hpPrime hpDvd
    rw [hpFour] at hpMod
    omega
  have hprod : ∏ p ∈ G.primeFactors, p = G :=
    Nat.prod_primeFactors_of_squarefree hGsf
  have hcast : (G : ZMod 8) = 1 := by
    rw [← hprod]
    push_cast
    apply Finset.prod_eq_one
    intro p hp
    apply (ZMod.natCast_eq_natCast_iff' p 1 8).mpr
    exact hall p hp
  have hGone :
      G % 8 = 1 :=
    (ZMod.natCast_eq_natCast_iff' G 1 8).mp hcast
  omega

namespace Sm2LowerSquareAllocation

/-- Every canonical upper Pell rank on this leaf is one modulo four. -/
theorem upperPellRank_mod_four_eq_one
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    pellRank data.upperKernel allocation.upper_pellKernel % 4 = 1 := by
  apply divisor_mod_four_eq_one_of_prime_support
    allocation.upper_pellKernel.2
    (pellRank_dvd_kernel data.upperKernel allocation.upper_pellKernel)
  intro p hp hpRank
  apply data.upperSupport_prime_mod_four_eq_one hp
  exact dvd_mul_of_dvd_left hpRank data.upperSquarePart

/-- The exact two polynomial normal forms force both composite cross-kernel
Jacobi symbols to be minus one.

The proof uses the complete square-cube quotients, not merely divisibility
of the two polynomial values by `D` and `K`.  No primality assumption on
either kernel is used. -/
theorem kernel_jacobi_symbols_eq_neg_one
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    jacobiSym (data.pell.D : Int) data.upperKernel = -1 ∧
      jacobiSym (data.upperKernel : Int) data.pell.D = -1 := by
  have hresidues := allocation.kernel_residues
  have hD8 : data.pell.D % 8 = 3 := hresidues.1
  have hK24 : data.upperKernel % 24 = 5 := hresidues.2
  have hD2 : data.pell.D % 2 = 1 := by
    have hmod :=
      Nat.mod_mod_of_dvd data.pell.D (by decide : 2 ∣ 8)
    rw [hD8] at hmod
    simpa using hmod.symm
  have hK8 : data.upperKernel % 8 = 5 := by
    have hmod :=
      Nat.mod_mod_of_dvd data.upperKernel (by decide : 8 ∣ 24)
    rw [hK24] at hmod
    simpa using hmod.symm
  have hK4 : data.upperKernel % 4 = 1 := by
    have hmod :=
      Nat.mod_mod_of_dvd data.upperKernel (by decide : 4 ∣ 24)
    rw [hK24] at hmod
    simpa using hmod.symm
  have hDOdd : Odd data.pell.D := Nat.odd_iff.mpr hD2
  have hKOdd : Odd data.upperKernel := by
    rw [Nat.odd_iff]
    have hmod :=
      Nat.mod_mod_of_dvd data.upperKernel (by decide : 2 ∣ 8)
    rw [hK8] at hmod
    simpa using hmod.symm
  have hsupport := allocation.source_supports_coprime
  have hyK :
      Nat.Coprime allocation.y data.upperKernel := by
    apply hsupport.of_dvd
    · exact
        ⟨data.pell.D * allocation.linearUpperSquarePart,
          by ring⟩
    · exact ⟨data.upperSquarePart, rfl⟩
  have hzK :
      Nat.Coprime allocation.linearUpperSquarePart
        data.upperKernel := by
    apply hsupport.of_dvd
    · exact ⟨data.pell.D * allocation.y, by ring⟩
    · exact ⟨data.upperSquarePart, rfl⟩
  have hDK :
      Nat.Coprime data.pell.D data.upperKernel := by
    apply hsupport.of_dvd
    · exact
        ⟨allocation.y * allocation.linearUpperSquarePart, rfl⟩
    · exact ⟨data.upperSquarePart, rfl⟩
  have hyKInt :
      Int.gcd (allocation.y : Int) data.upperKernel = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hyK.gcd_eq_one
  have hzKInt :
      Int.gcd (allocation.linearUpperSquarePart : Int)
        data.upperKernel = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hzK.gcd_eq_one
  have hDKInt :
      Int.gcd (data.pell.D : Int) data.upperKernel = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hDK.gcd_eq_one
  have hlinearEq :
      (allocation.y : Int) ^ 2 + 2 =
        (allocation.linearUpperSquarePart : Int) ^ 2 *
          (data.pell.D : Int) ^ 3 := by
    exact_mod_cast allocation.linearUpperNormalForm.2.2.1
  have hlinearMod :
      Int.ModEq data.upperKernel
        ((allocation.y : Int) ^ 2 + 2)
        ((allocation.linearUpperSquarePart : Int) ^ 2 *
          (data.pell.D : Int) ^ 3) := by
    rw [hlinearEq]
  have hupperEq :
      (allocation.y : Int) ^ 4 +
          2 * (allocation.y : Int) ^ 2 + 2 =
        (data.upperSquarePart : Int) ^ 2 *
          (data.upperKernel : Int) ^ 3 := by
    exact_mod_cast allocation.upperPolynomialNormalForm.2.2.1
  have hproductMod :
      Int.ModEq data.upperKernel
        ((allocation.y : Int) ^ 2 *
          ((allocation.y : Int) ^ 2 + 2))
        (-2) := by
    apply Int.modEq_of_dvd
    rw [show
      (-2 : Int) -
          (allocation.y : Int) ^ 2 *
            ((allocation.y : Int) ^ 2 + 2) =
        -((allocation.y : Int) ^ 4 +
          2 * (allocation.y : Int) ^ 2 + 2) by ring,
      hupperEq]
    exact
      ⟨-((data.upperSquarePart : Int) ^ 2 *
          (data.upperKernel : Int) ^ 2), by ring⟩
  have hlinearJacobi :
      jacobiSym
          ((allocation.y : Int) ^ 2 + 2)
          data.upperKernel =
        jacobiSym (data.pell.D : Int) data.upperKernel := by
    calc
      jacobiSym
          ((allocation.y : Int) ^ 2 + 2)
          data.upperKernel =
          jacobiSym
            ((allocation.linearUpperSquarePart : Int) ^ 2 *
              (data.pell.D : Int) ^ 3)
            data.upperKernel :=
        jacobiSym.mod_left' hlinearMod
      _ =
          jacobiSym (data.pell.D : Int) data.upperKernel := by
        rw [jacobiSym.mul_left,
          jacobiSym.sq_one' hzKInt, one_mul,
          show (data.pell.D : Int) ^ 3 =
            (data.pell.D : Int) *
              (data.pell.D : Int) ^ 2 by ring,
          jacobiSym.mul_left,
          jacobiSym.sq_one' hDKInt, mul_one]
  have hproductJacobi :
      jacobiSym
          ((allocation.y : Int) ^ 2 + 2)
          data.upperKernel =
        jacobiSym (-2 : Int) data.upperKernel := by
    calc
      jacobiSym
          ((allocation.y : Int) ^ 2 + 2)
          data.upperKernel =
          jacobiSym
            ((allocation.y : Int) ^ 2 *
              ((allocation.y : Int) ^ 2 + 2))
            data.upperKernel := by
        symm
        rw [jacobiSym.mul_left,
          jacobiSym.sq_one' hyKInt, one_mul]
      _ = jacobiSym (-2 : Int) data.upperKernel :=
        jacobiSym.mod_left' hproductMod
  have hnegTwo :
      jacobiSym (-2 : Int) data.upperKernel = -1 := by
    rw [jacobiSym.at_neg_two hKOdd,
      ZMod.χ₈'_nat_eq_if_mod_eight]
    simp [Nat.odd_iff.mp hKOdd, hK8]
  have hDKJacobi :
      jacobiSym (data.pell.D : Int) data.upperKernel = -1 := by
    calc
      jacobiSym (data.pell.D : Int) data.upperKernel =
          jacobiSym
            ((allocation.y : Int) ^ 2 + 2)
            data.upperKernel :=
        hlinearJacobi.symm
      _ = jacobiSym (-2 : Int) data.upperKernel :=
        hproductJacobi
      _ = -1 := hnegTwo
  have hreciprocity :
      jacobiSym (data.pell.D : Int) data.upperKernel =
        jacobiSym (data.upperKernel : Int) data.pell.D :=
    jacobiSym.quadratic_reciprocity_one_mod_four'
      hDOdd hK4
  exact ⟨hDKJacobi, hreciprocity.symm.trans hDKJacobi⟩

end Sm2LowerSquareAllocation

namespace Sm2LowerSquareUpperSourceGenerator

/-- No exact `sm2LowerSquare` upper source generator can have canonical
Pell divisibility rank congruent to `5 mod 8`. -/
theorem false_of_rank_mod_eight_five
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hRank :
      pellRank data.upperKernel allocation.upper_pellKernel % 8 = 5) :
    False := by
  let K := data.upperKernel
  let u := generator.upperOrbit.rootX
  let v := generator.upperOrbit.rootY
  let R := pellRank K allocation.upper_pellKernel
  let s := R / 8
  let T := sm2LucasCoeff u (4 * s + 2)
  let S := sm2LucasCoeff u (4 * s + 3)
  let U := S ^ 2 + T ^ 2
  have hRform : R = 8 * s + 5 := by
    have h := (Nat.mod_add_div R 8).symm
    rw [hRank] at h
    dsimp [s]
    omega
  have hK8 : K % 8 = 5 := by
    have hK24 := allocation.kernel_residues.2
    have hmod := Nat.mod_mod_of_dvd K (by decide : 8 ∣ 24)
    rw [hK24] at hmod
    simpa [K] using hmod.symm
  have hu :
      u % 4 = 2 :=
    negativePell_real_mod_four_of_kernel_mod_eight_five
      hK8 generator.upperOrbit.root_equation
  have hpower :
      sm2UpperNegativeUnit K u v ^ (8 * s + 5) =
        (⟨generator.real, generator.ordinate⟩ :
          ℤ√(K : Int)) := by
    simpa [K, u, v, R, hRform] using generator.generator_power
  have hshell :=
    sm2UpperNegativeUnit_rank_five_half_shell
      generator.upperOrbit.rootY_pos
      generator.upperOrbit.root_equation hpower
  have hshell' :
      generator.ordinate = v * U ∧
        Int.ModEq U
          (((generator.real : Int) - 1) * T)
          (-(S + T : Nat)) := by
    simpa [T, S, U, u, v] using hshell
  have hT : T % 8 = 4 := by
    have h :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 2) hu
    simpa [T, sm2LucasResidue,
      show (4 * s + 2) % 4 = 2 by omega] using h
  have hS : S % 8 = 1 := by
    have h :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 3) hu
    simpa [S, sm2LucasResidue,
      show (4 * s + 3) % 4 = 3 by omega] using h
  have hcoprime : Nat.Coprime S T := by
    simpa only [S, T,
      show 4 * s + 3 = 2 * (2 * s + 1) + 1 by omega,
      show 4 * s + 2 = 2 * (2 * s + 1) by omega] using
        sm2LucasCoeff_even_consecutive_coprime u (2 * s + 1)
  have hjac :
      jacobiSym ((generator.real : Int) - 1) U = -1 :=
    jacobi_predecessor_eq_neg_one_of_half_shell
      hS hT rfl hcoprime hshell'.2
  have hnonsquare :
      ¬ IsSquare
        ((((generator.real : Int) - 1 : Int) : ZMod U)) :=
    ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac
  apply generator.false_of_factor_nonsquare (q := U)
  · refine ⟨K * v ^ 2 * U, ?_⟩
    rw [generator.negative_equation, hshell'.1]
    ring
  · simpa using hnonsquare

/-- After the rank-five obstruction, every exact source generator has rank
one modulo eight. -/
theorem rank_mod_eight_eq_one
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    pellRank data.upperKernel allocation.upper_pellKernel % 8 = 1 := by
  let R := pellRank data.upperKernel allocation.upper_pellKernel
  have hR4 : R % 4 = 1 := by
    simpa [R] using allocation.upperPellRank_mod_four_eq_one
  have hnot : R % 8 ≠ 5 := by
    intro hfive
    exact generator.false_of_rank_mod_eight_five
      (by simpa [R] using hfive)
  have hlt : R % 8 < 8 := Nat.mod_lt _ (by decide)
  have hmod : R % 8 % 4 = R % 4 :=
    Nat.mod_mod_of_dvd R (by decide : 4 ∣ 8)
  rw [hR4] at hmod
  simpa [R] using (by omega : R % 8 = 1)

/-- No prime divisor of the exact upper Pell rank can be five modulo eight.
The obstruction is first produced at the corresponding intermediate
negative-Pell power and then transferred through the complementary
one-modulo-four exponent to the rank-normalized generator. -/
theorem false_of_rank_prime_mod_eight_five
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {p : Nat}
    (_hp : p.Prime)
    (hpR :
      p ∣ pellRank data.upperKernel allocation.upper_pellKernel)
    (hpEight : p % 8 = 5) :
    False := by
  let K := data.upperKernel
  let u := generator.upperOrbit.rootX
  let v := generator.upperOrbit.rootY
  let R := pellRank K allocation.upper_pellKernel
  let s := R / p
  let A := sm2LucasReal u p
  let B := sm2LucasCoeff u p
  have hpOdd : Odd p := by
    rw [Nat.odd_iff]
    omega
  have hRform : R = p * s := by
    simpa [s, mul_comm] using (Nat.div_mul_cancel hpR).symm
  have hK8 : K % 8 = 5 := by
    have hK24 := allocation.kernel_residues.2
    have hmod := Nat.mod_mod_of_dvd K (by decide : 8 ∣ 24)
    rw [hK24] at hmod
    simpa [K] using hmod.symm
  have hu : u % 4 = 2 :=
    negativePell_real_mod_four_of_kernel_mod_eight_five
      hK8 generator.upperOrbit.root_equation
  have hR4 : R % 4 = 1 := by
    simpa [K, R] using allocation.upperPellRank_mod_four_eq_one
  have hp4 : p % 4 = 1 := by
    have hmod := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
    rw [hpEight] at hmod
    omega
  have hs4 : s % 4 = 1 := by
    have hmod := congrArg (fun z : Nat => z % 4) hRform
    rw [hR4, Nat.mul_mod, hp4] at hmod
    have hslt : s % 4 < 4 := Nat.mod_lt _ (by decide)
    omega
  have hsquare :
      (A : ZMod B) ^ 2 = -1 := by
    simpa [A, B] using
      sm2LucasReal_sq_eq_neg_one_mod_coeff
        generator.upperOrbit.root_equation hpOdd
  have hpower :
      sm2UpperNegativeUnit K u v ^ (p * s) =
        (⟨generator.real, generator.ordinate⟩ :
          ℤ√(K : Int)) := by
    rw [← hRform]
    simpa [K, u, v, R] using generator.generator_power
  have hre := congrArg Zsqrtd.re hpower
  have hre' :
      (sm2UpperNegativeUnit K u v ^ (p * s)).re =
        (generator.real : Int) := by
    simpa using hre
  have hpowMod :=
    sm2UpperNegativeUnit_mul_power_real_mod_coeff
      (K := K) (u := u) (v := v) (n := p) (s := s)
      generator.upperOrbit.root_equation
  have hgenMod :
      (generator.real : ZMod B) = (A : ZMod B) := by
    calc
      (generator.real : ZMod B) =
          ((((sm2UpperNegativeUnit K u v ^ (p * s)).re : Int) :
            ZMod B)) := by
              have hcast :=
                congrArg (fun z : Int => (z : ZMod B)) hre'.symm
              push_cast at hcast
              exact hcast
      _ = (A : ZMod B) ^ s := by simpa [A, B] using hpowMod
      _ = A :=
        zmod_pow_eq_self_of_square_eq_neg_one_local hsquare hs4
  have hjac :
      jacobiSym ((A : Int) - 1) B = -1 := by
    simpa [A, B] using
      jacobi_sm2LucasReal_predecessor_of_mod_eight_five
        generator.upperOrbit.rootY_pos
        generator.upperOrbit.root_equation hu hpEight
  have hnonsquareA :
      ¬ IsSquare (((A : Int) - 1 : Int) : ZMod B) :=
    ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac
  have hnormZero :
      (generator.real : ZMod B) ^ 2 + 1 = 0 := by
    rw [hgenMod, hsquare]
    ring
  have hBdNorm : B ∣ generator.real ^ 2 + 1 := by
    apply
      (ZMod.natCast_eq_zero_iff
        (generator.real ^ 2 + 1) B).mp
    push_cast
    exact hnormZero
  have hpredEq :
      ((((generator.real : Int) - 1 : Int) : ZMod B)) =
        (((A : Int) - 1 : Int) : ZMod B) := by
    push_cast
    rw [hgenMod]
  have hnonsquareGenerator :
      ¬ IsSquare
        ((((generator.real : Int) - 1 : Int) : ZMod B)) := by
    intro hsquareGenerator
    apply hnonsquareA
    rw [← hpredEq]
    exact hsquareGenerator
  apply generator.false_of_factor_nonsquare hBdNorm
  simpa using hnonsquareGenerator

/-- Every prime divisor of the exact upper Pell rank is one modulo eight. -/
theorem rank_prime_mod_eight_one
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {p : Nat}
    (hp : p.Prime)
    (hpR :
      p ∣ pellRank data.upperKernel allocation.upper_pellKernel) :
    p % 8 = 1 := by
  have hpFour : p % 4 = 1 := by
    apply data.upperSupport_prime_mod_four_eq_one hp
    have hpK : p ∣ data.upperKernel :=
      hpR.trans
        (pellRank_dvd_kernel
          data.upperKernel allocation.upper_pellKernel)
    exact dvd_mul_of_dvd_left hpK data.upperSquarePart
  have hpMod :=
    Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
  have hpLt : p % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [hpFour] at hpMod
  by_contra hnot
  have hpFive : p % 8 = 5 := by omega
  exact generator.false_of_rank_prime_mod_eight_five
    hp hpR hpFive

/-- Every prime divisor of the rank-normalized generator real coordinate is
either two or one modulo four.  This uses the retained source divisibility
`P ∣ y² + 1`, not only the ambient negative-Pell equation. -/
theorem generator_real_prime_eq_two_or_mod_four_one
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {q : Nat}
    (hq : q.Prime)
    (hqP : q ∣ generator.real) :
    q = 2 ∨ q % 4 = 1 := by
  rcases hq.eq_two_or_odd' with hTwo | hOdd
  · exact Or.inl hTwo
  · right
    letI : Fact q.Prime := ⟨hq⟩
    have hqPred : q ∣ allocation.y ^ 2 + 1 :=
      hqP.trans generator.real_dvd_predecessor
    have hzero :
        ((allocation.y ^ 2 + 1 : Nat) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff
        (allocation.y ^ 2 + 1) q).mpr hqPred
    have hsquare :
        (allocation.y : ZMod q) ^ 2 = -1 := by
      push_cast at hzero
      exact eq_neg_of_add_eq_zero_left hzero
    have hnotThree : q % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_one hsquare
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hOdd) with
      hOne | hThree
    · exact hOne
    · exact (hnotThree hThree).elim

/-- The fundamental norm-minus-one real coordinate divides the
rank-normalized generator real coordinate.  This uses that the exact Pell
rank is odd; it is not a statement about arbitrary powers. -/
theorem root_real_dvd_generator_real
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    generator.upperOrbit.rootX ∣ generator.real := by
  let K := data.upperKernel
  let R := pellRank K allocation.upper_pellKernel
  have hR8 : R % 8 = 1 := by
    simpa [K, R] using generator.rank_mod_eight_eq_one
  have hROdd : Odd R := by
    rw [Nat.odd_iff]
    omega
  obtain ⟨t, ht⟩ := hROdd
  have hdivInt :=
    zsqrtd_real_dvd_odd_power_local K
      generator.upperOrbit.rootX generator.upperOrbit.rootY t
  rw [← ht] at hdivInt
  have hpowerRe := congrArg Zsqrtd.re generator.generator_power
  have hre :
      (sm2UpperNegativeUnit K generator.upperOrbit.rootX
            generator.upperOrbit.rootY ^ R).re =
        (generator.real : Int) := by
    simpa [K, R] using hpowerRe
  rw [show
      (⟨generator.upperOrbit.rootX,
          generator.upperOrbit.rootY⟩ : ℤ√(K : Int)) =
        sm2UpperNegativeUnit K generator.upperOrbit.rootX
          generator.upperOrbit.rootY by
        rfl,
    hre] at hdivInt
  exact Int.natCast_dvd_natCast.mp hdivInt

/-- The fundamental norm-minus-one real coordinate inherits the retained
square-successor divisibility from the rank-normalized generator. -/
theorem root_real_dvd_predecessor
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    generator.upperOrbit.rootX ∣ allocation.y ^ 2 + 1 :=
  generator.root_real_dvd_generator_real.trans
    generator.real_dvd_predecessor

/-- The exact source eliminates the otherwise possible six-modulo-eight
fundamental norm-minus-one real coordinate. -/
theorem root_real_mod_eight
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    generator.upperOrbit.rootX % 8 = 2 := by
  have hK8 : data.upperKernel % 8 = 5 := by
    have hK24 := allocation.kernel_residues.2
    have hmod :=
      Nat.mod_mod_of_dvd data.upperKernel (by decide : 8 ∣ 24)
    rw [hK24] at hmod
    omega
  exact
    negativePell_real_mod_eight_two_of_dvd_square_add_one
      hK8 generator.upperOrbit.root_equation
      generator.root_real_dvd_predecessor

/-- Every prime divisor of the fundamental norm-minus-one real coordinate
is either two or one modulo four. -/
theorem root_real_prime_eq_two_or_mod_four_one
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {q : Nat}
    (hq : q.Prime)
    (hqRoot : q ∣ generator.upperOrbit.rootX) :
    q = 2 ∨ q % 4 = 1 :=
  generator.generator_real_prime_eq_two_or_mod_four_one hq
    (hqRoot.trans generator.root_real_dvd_generator_real)

/-- Elementary quartic residue filter.  Over a prime field of order
`q = 8m+1`, a square root `P` of minus one whose predecessor is itself a
square forces the displayed quartic character of two. -/
theorem quartic_two_condition_of_square_predecessor
    {q m P : Nat}
    (hq : q.Prime)
    (hqForm : q = 8 * m + 1)
    (hnegative : (P : ZMod q) ^ 2 = -1)
    (hpredecessor : IsSquare ((P : ZMod q) - 1)) :
    (2 : ZMod q) ^ (2 * m) = (-1 : ZMod q) ^ m := by
  letI : Fact q.Prime := ⟨hq⟩
  have hmPos : 0 < m := by
    by_contra hnot
    have hmZero : m = 0 := by omega
    subst m
    norm_num at hqForm
    subst q
    norm_num at hq
  obtain ⟨a, ha⟩ := hpredecessor
  have haNe : a ≠ 0 := by
    intro haZero
    subst a
    have hPOne : (P : ZMod q) = 1 := by
      have haZero : (P : ZMod q) - 1 = 0 := by
        simpa using ha
      exact sub_eq_zero.mp haZero
    have htwoZero : (2 : ZMod q) = 0 := by
      calc
        (2 : ZMod q) = (P : ZMod q) ^ 2 + 1 := by
          rw [hPOne]
          norm_num
        _ = 0 := by rw [hnegative]; ring
    have hqDvdTwo : q ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 q).mp htwoZero
    have hqLeTwo : q ≤ 2 :=
      Nat.le_of_dvd (by decide : 0 < 2) hqDvdTwo
    omega
  have haFourth : a ^ 4 = -2 * (P : ZMod q) := by
    calc
      a ^ 4 = (a * a) ^ 2 := by ring
      _ = ((P : ZMod q) - 1) ^ 2 := by rw [ha]
      _ = (P : ZMod q) ^ 2 - 2 * P + 1 := by ring
      _ = -2 * (P : ZMod q) := by rw [hnegative]; ring
  have haFermat : a ^ (8 * m) = 1 := by
    simpa [hqForm] using ZMod.pow_card_sub_one_eq_one haNe
  have hpower :
      (-2 * (P : ZMod q)) ^ (2 * m) = 1 := by
    calc
      (-2 * (P : ZMod q)) ^ (2 * m) =
          (a ^ 4) ^ (2 * m) := by rw [haFourth]
      _ = a ^ (8 * m) := by
        rw [← pow_mul]
        congr 1
        omega
      _ = 1 := haFermat
  have hexpand :
      (-2 * (P : ZMod q)) ^ (2 * m) =
        (2 : ZMod q) ^ (2 * m) * (-1 : ZMod q) ^ m := by
    calc
      (-2 * (P : ZMod q)) ^ (2 * m) =
          ((-2 * (P : ZMod q)) ^ 2) ^ m := by
            rw [pow_mul]
      _ = (4 * (P : ZMod q) ^ 2) ^ m := by
        congr 1
        ring
      _ = (4 * (-1 : ZMod q)) ^ m := by rw [hnegative]
      _ = (4 : ZMod q) ^ m * (-1 : ZMod q) ^ m := by
        rw [mul_pow]
      _ = (2 : ZMod q) ^ (2 * m) * (-1 : ZMod q) ^ m := by
        rw [show (4 : ZMod q) = 2 ^ 2 by norm_num, pow_mul]
  have hproduct :
      (2 : ZMod q) ^ (2 * m) * (-1 : ZMod q) ^ m = 1 := by
    rw [← hexpand]
    exact hpower
  have hsign :
      (-1 : ZMod q) ^ m * (-1 : ZMod q) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (2 : ZMod q) ^ (2 * m) =
        (2 : ZMod q) ^ (2 * m) * 1 := by ring
    _ =
        (2 : ZMod q) ^ (2 * m) *
          ((-1 : ZMod q) ^ m * (-1 : ZMod q) ^ m) := by
            rw [hsign]
    _ =
        ((2 : ZMod q) ^ (2 * m) * (-1 : ZMod q) ^ m) *
          (-1 : ZMod q) ^ m := by ring
    _ = (-1 : ZMod q) ^ m := by rw [hproduct]; ring

/-- Every prime divisor of the upper kernel which is one modulo eight
satisfies the source-forced quartic character condition for two. -/
theorem kernel_prime_quartic_two_condition
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {q : Nat}
    (hq : q.Prime)
    (hqK : q ∣ data.upperKernel)
    (hqEight : q % 8 = 1) :
    (2 : ZMod q) ^ ((q - 1) / 4) =
      (-1 : ZMod q) ^ ((q - 1) / 8) := by
  let m := q / 8
  have hqForm : q = 8 * m + 1 := by
    have hdecomp := (Nat.mod_add_div q 8).symm
    rw [hqEight] at hdecomp
    dsimp [m]
    omega
  have hqNorm : q ∣ generator.real ^ 2 + 1 := by
    rw [generator.negative_equation]
    exact dvd_mul_of_dvd_left hqK (generator.ordinate ^ 2)
  have hnegative : (generator.real : ZMod q) ^ 2 = -1 := by
    have hzero :
        ((generator.real ^ 2 + 1 : Nat) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff
        (generator.real ^ 2 + 1) q).mpr hqNorm
    push_cast at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hpredecessor :
      IsSquare ((generator.real : ZMod q) - 1) := by
    refine ⟨(allocation.y : ZMod q), ?_⟩
    have hsourceInt :
        (allocation.y : Int) ^ 2 + 1 =
          (generator.point ^
            (2 * generator.outerIndex + 1)).re := by
      calc
        (allocation.y : Int) ^ 2 + 1 =
            (data.center : Int) := by
              exact_mod_cast allocation.center_eq.symm
        _ =
            (generator.point ^
              (2 * generator.outerIndex + 1)).re := by
                have hpower :=
                  congrArg Zsqrtd.re generator.source_power
                simpa [Sm2LowerSquareUpperSourceGenerator.point,
                  sm2UpperSourcePoint] using hpower
    have hsource :=
      congrArg (fun z : Int => (z : ZMod q))
        hsourceInt
    push_cast at hsource
    have hreal :=
      zsqrtd_generator_real_mod_of_phase
        generator.negative_equation hqNorm
        generator.outer_phase_mod_four
    have hreal' :
        (((generator.point ^
            (2 * generator.outerIndex + 1)).re : Int) : ZMod q) =
          (generator.real : ZMod q) := by
      simpa [Sm2LowerSquareUpperSourceGenerator.point] using hreal
    calc
      (generator.real : ZMod q) - 1 =
          (((generator.point ^
              (2 * generator.outerIndex + 1)).re : Int) : ZMod q) -
            1 := by rw [hreal']
      _ = (allocation.y : ZMod q) ^ 2 := by
        rw [← hsource]
        ring
      _ = (allocation.y : ZMod q) * allocation.y := by ring
  have hquartic :=
    quartic_two_condition_of_square_predecessor
      hq hqForm hnegative hpredecessor
  have hquarter : (q - 1) / 4 = 2 * m := by
    omega
  have heighth : (q - 1) / 8 = m := by
    omega
  simpa [hquarter, heighth] using hquartic

/-- In particular, every prime divisor of the exact upper Pell rank obeys
the quartic character condition for two. -/
theorem rank_prime_quartic_two_condition
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {q : Nat}
    (hq : q.Prime)
    (hqRank :
      q ∣ pellRank data.upperKernel allocation.upper_pellKernel) :
    (2 : ZMod q) ^ ((q - 1) / 4) =
      (-1 : ZMod q) ^ ((q - 1) / 8) := by
  apply generator.kernel_prime_quartic_two_condition hq
  · exact
      hqRank.trans
        (pellRank_dvd_kernel
          data.upperKernel allocation.upper_pellKernel)
  · exact generator.rank_prime_mod_eight_one hq hqRank

/-- The first hostile quartic control: seventeen cannot divide the
canonical upper kernel of an exact residual source. -/
theorem seventeen_not_dvd_upperKernel
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    ¬ 17 ∣ data.upperKernel := by
  intro hseventeen
  have hquartic :=
    generator.kernel_prime_quartic_two_condition
      (q := 17) (by norm_num) hseventeen (by norm_num)
  norm_num at hquartic
  exact (by decide : (16 : ZMod 17) ≠ 1) hquartic

/-- Every surviving source generator has a nontrivial ramified deficit
`G = K / R = gcd(K, v)` congruent to five modulo eight.  The fundamental
negative-Pell equation therefore has the sharpened cubic shell
`u² + 1 = R * G³ * w²`. -/
theorem exists_rank_deficit_shell
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    ∃ G w : Nat,
      G = data.upperKernel.gcd generator.upperOrbit.rootY ∧
      G = data.upperKernel /
        pellRank data.upperKernel allocation.upper_pellKernel ∧
      1 < G ∧ G % 8 = 5 ∧
      data.upperKernel =
        pellRank data.upperKernel allocation.upper_pellKernel * G ∧
      generator.upperOrbit.rootY = G * w ∧
      generator.upperOrbit.rootX ^ 2 + 1 =
        pellRank data.upperKernel allocation.upper_pellKernel *
          G ^ 3 * w ^ 2 := by
  let K := data.upperKernel
  let u := generator.upperOrbit.rootX
  let v := generator.upperOrbit.rootY
  let R := pellRank K allocation.upper_pellKernel
  let G := K.gcd v
  have hR8 : R % 8 = 1 := by
    simpa [K, R] using generator.rank_mod_eight_eq_one
  have hK8 : K % 8 = 5 := by
    have hK24 := allocation.kernel_residues.2
    have hmod := Nat.mod_mod_of_dvd K (by decide : 8 ∣ 24)
    rw [hK24] at hmod
    simpa [K] using hmod.symm
  have hKOdd : Odd K := by
    rw [Nat.odd_iff]
    omega
  have hcop : K.Coprime (2 * u) :=
    kernel_coprime_two_mul_negativePell_root
      hKOdd generator.upperOrbit.root_equation
  have hgcdFund :
      K.gcd (fundamentalY K allocation.upper_pellKernel) = G := by
    rw [generator.upperOrbit.fundamentalY_eq]
    simpa [G, K, u, v, mul_assoc] using
      (gcd_mul_eq_right_of_coprime_left
        (K := K) (a := 2 * u) (b := v) hcop)
  have hRdef : R = K / G := by
    simp [R, pellRank, hgcdFund]
  have hGdvdK : G ∣ K := Nat.gcd_dvd_left K v
  have hKsplit : K = R * G := by
    rw [hRdef]
    exact (Nat.div_mul_cancel hGdvdK).symm
  have hRPos : 0 < R :=
    pellRank_pos K allocation.upper_pellKernel
  have hRdvd : R ∣ K :=
    pellRank_dvd_kernel K allocation.upper_pellKernel
  have hGQuot : G = K / R := by
    symm
    apply (Nat.div_eq_iff_eq_mul_left hRPos hRdvd).2
    simpa [mul_comm] using hKsplit
  have hGPos : 0 < G :=
    Nat.gcd_pos_of_pos_left v
      (Nat.zero_lt_of_lt allocation.upper_pellKernel.1)
  have hGOneLt : 1 < G := by
    by_contra hnot
    have hGOne : G = 1 := by omega
    have hKR : K = R := by simpa [hGOne] using hKsplit
    rw [hKR] at hK8
    omega
  have hG8 : G % 8 = 5 := by
    have h := congrArg (fun n : Nat => n % 8) hKsplit
    rw [Nat.mul_mod, hK8, hR8] at h
    simpa using h.symm
  obtain ⟨w, hv⟩ := Nat.gcd_dvd_right K v
  refine ⟨G, w, rfl, ?_, hGOneLt, hG8, ?_, ?_, ?_⟩
  · simpa [K, R] using hGQuot
  · simpa [K, R] using hKsplit
  · simpa [G, v] using hv
  · calc
      generator.upperOrbit.rootX ^ 2 + 1 = K * v ^ 2 :=
        generator.upperOrbit.root_equation
      _ = R * G ^ 3 * w ^ 2 := by rw [hKsplit, hv]; ring
      _ =
          pellRank data.upperKernel allocation.upper_pellKernel *
            G ^ 3 * w ^ 2 := by
        rfl

/-- For the selected fundamental norm-minus-one root, the direct ordinate
quotient agrees with the repository's canonical Pell divisibility rank. -/
theorem pellRank_eq_kernel_div_gcd_rootY
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    pellRank data.upperKernel allocation.upper_pellKernel =
      data.upperKernel /
        data.upperKernel.gcd generator.upperOrbit.rootY := by
  obtain
      ⟨G, _w, hGgcd, _hGquot, hGOneLt, _hG8,
        hKsplit, _hv, _hshell⟩ :=
    generator.exists_rank_deficit_shell
  have hGPos : 0 < G := by omega
  calc
    pellRank data.upperKernel allocation.upper_pellKernel =
        (pellRank data.upperKernel allocation.upper_pellKernel * G) /
          G := by
            rw [Nat.mul_div_cancel _ hGPos]
    _ = data.upperKernel / G := by rw [← hKsplit]
    _ =
        data.upperKernel /
          data.upperKernel.gcd generator.upperOrbit.rootY := by
            rw [← hGgcd]

/-- A surviving rank-deficit shell contains a ramified prime congruent to
five modulo eight.  This prime divides both the upper kernel and the
fundamental norm-minus-one ordinate. -/
theorem exists_ramified_prime_mod_eight_five
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    ∃ q : Nat,
      q.Prime ∧ q % 8 = 5 ∧
      q ∣ data.upperKernel ∧
      q ∣ generator.upperOrbit.rootY := by
  obtain
      ⟨G, w, _hGgcd, _hGquot, _hGOneLt, hG8,
        hKsplit, hv, _hshell⟩ :=
    generator.exists_rank_deficit_shell
  have hGdvdK : G ∣ data.upperKernel := by
    refine ⟨pellRank data.upperKernel allocation.upper_pellKernel, ?_⟩
    simpa [mul_comm] using hKsplit
  have hGsf : Squarefree G :=
    allocation.upper_pellKernel.2.squarefree_of_dvd hGdvdK
  have hprime :
      ∀ p : Nat, p.Prime → p ∣ G → p % 4 = 1 := by
    intro p hp hpG
    apply data.upperSupport_prime_mod_four_eq_one hp
    exact dvd_mul_of_dvd_left (hpG.trans hGdvdK)
      data.upperSquarePart
  obtain ⟨q, hqPrime, hqG, hq8⟩ :=
    exists_prime_mod_eight_five_of_squarefree hGsf hG8 hprime
  exact
    ⟨q, hqPrime, hq8, hqG.trans hGdvdK,
      hqG.trans ⟨w, hv⟩⟩

/-- The same Lucas--Jacobi obstruction eliminates an outer source exponent
congruent to five modulo eight. -/
theorem false_of_outer_exponent_mod_eight_five
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hOuter : (2 * generator.outerIndex + 1) % 8 = 5) :
    False := by
  let K := data.upperKernel
  let u := generator.real
  let v := generator.ordinate
  let h := 2 * generator.outerIndex + 1
  let s := h / 8
  let T := sm2LucasCoeff u (4 * s + 2)
  let S := sm2LucasCoeff u (4 * s + 3)
  let U := S ^ 2 + T ^ 2
  have hhform : h = 8 * s + 5 := by
    have heq := (Nat.mod_add_div h 8).symm
    rw [hOuter] at heq
    dsimp [s]
    omega
  have hu : u % 4 = 2 := by
    have hmod := Nat.mod_mod_of_dvd u (by decide : 4 ∣ 8)
    rw [generator.real_mod_eight] at hmod
    simpa [u] using hmod.symm
  have hpower :
      sm2UpperNegativeUnit K u v ^ (8 * s + 5) =
        (⟨data.center,
            data.upperKernel * data.upperSquarePart⟩ :
          ℤ√(K : Int)) := by
    have hsource := generator.source_power.symm
    simpa [sm2UpperSourcePoint, sm2UpperNegativeUnit,
      K, u, v, h, hhform] using hsource
  have hshell :=
    sm2UpperNegativeUnit_rank_five_half_shell
      generator.ordinate_pos generator.negative_equation hpower
  have hshell' :
      data.upperKernel * data.upperSquarePart = v * U ∧
        Int.ModEq U
          (((data.center : Int) - 1) * T)
          (-(S + T : Nat)) := by
    simpa [T, S, U, u, v] using hshell
  have hT : T % 8 = 4 := by
    have hmod :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 2) hu
    simpa [T, sm2LucasResidue,
      show (4 * s + 2) % 4 = 2 by omega] using hmod
  have hS : S % 8 = 1 := by
    have hmod :=
      sm2LucasCoeff_mod_eight
        (u := u) (n := 4 * s + 3) hu
    simpa [S, sm2LucasResidue,
      show (4 * s + 3) % 4 = 3 by omega] using hmod
  have hcoprime : Nat.Coprime S T := by
    simpa only [S, T,
      show 4 * s + 3 = 2 * (2 * s + 1) + 1 by omega,
      show 4 * s + 2 = 2 * (2 * s + 1) by omega] using
        sm2LucasCoeff_even_consecutive_coprime u (2 * s + 1)
  have hjac :
      jacobiSym ((data.center : Int) - 1) U = -1 :=
    jacobi_predecessor_eq_neg_one_of_half_shell
      hS hT rfl hcoprime hshell'.2
  have hnonsquare :
      ¬ IsSquare
        ((((data.center : Int) - 1 : Int) : ZMod U)) :=
    ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac
  apply hnonsquare
  refine ⟨(allocation.y : ZMod U), ?_⟩
  have hcenter :=
    congrArg (fun n : Nat => (n : ZMod U)) allocation.center_eq
  push_cast at hcenter
  calc
    ((((data.center : Int) - 1 : Int) : ZMod U)) =
        (data.center : ZMod U) - 1 := by push_cast; ring
    _ = (allocation.y : ZMod U) ^ 2 := by
      rw [hcenter]
      ring
    _ = (allocation.y : ZMod U) * allocation.y := by ring

/-- A prime divisor of the outer source exponent cannot be three or five
modulo eight.  The three-modulo-eight case uses the signed successor because
the complementary exponent is three modulo four. -/
theorem false_of_outer_prime_mod_eight_three_or_five
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {p : Nat}
    (_hp : p.Prime)
    (hpH : p ∣ 2 * generator.outerIndex + 1)
    (hpClass : p % 8 = 3 ∨ p % 8 = 5) :
    False := by
  let K := data.upperKernel
  let u := generator.real
  let v := generator.ordinate
  let h := 2 * generator.outerIndex + 1
  let s := h / p
  let A := sm2LucasReal u p
  let B := sm2LucasCoeff u p
  have hpOdd : Odd p := by
    rw [Nat.odd_iff]
    rcases hpClass with hpThree | hpFive <;> omega
  have hpH' : p ∣ h := by
    simpa only [h] using hpH
  have hhform : h = p * s := by
    simpa only [s, mul_comm] using
      (Nat.div_mul_cancel hpH').symm
  have hu : u % 4 = 2 := by
    have hmod := Nat.mod_mod_of_dvd u (by decide : 4 ∣ 8)
    rw [generator.real_mod_eight] at hmod
    simpa [u] using hmod.symm
  have hsquare :
      (A : ZMod B) ^ 2 = -1 := by
    simpa [A, B] using
      sm2LucasReal_sq_eq_neg_one_mod_coeff
        generator.negative_equation hpOdd
  have hsourcePower :
      sm2UpperNegativeUnit K u v ^ (p * s) =
        sm2UpperSourcePoint K data.center
          (data.upperKernel * data.upperSquarePart) := by
    rw [← hhform]
    simpa [K, u, v, h, sm2UpperNegativeUnit] using
      generator.source_power.symm
  have hre := congrArg Zsqrtd.re hsourcePower
  have hre' :
      (sm2UpperNegativeUnit K u v ^ (p * s)).re =
        (data.center : Int) := by
    simpa [sm2UpperSourcePoint] using hre
  have hpowMod :=
    sm2UpperNegativeUnit_mul_power_real_mod_coeff
      (K := K) (u := u) (v := v) (n := p) (s := s)
      generator.negative_equation
  have hcenterPow :
      (data.center : ZMod B) = (A : ZMod B) ^ s := by
    calc
      (data.center : ZMod B) =
          ((((sm2UpperNegativeUnit K u v ^ (p * s)).re : Int) :
            ZMod B)) := by
              have hcast :=
                congrArg (fun z : Int => (z : ZMod B)) hre'.symm
              push_cast at hcast
              exact hcast
      _ = (A : ZMod B) ^ s := by simpa [A, B] using hpowMod
  have hh4 : h % 4 = 1 := by
    simpa [h] using generator.outer_phase_mod_four
  rcases hpClass with hpThree | hpFive
  · have hp4 : p % 4 = 3 := by
      have hmod := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
      rw [hpThree] at hmod
      omega
    have hs4 : s % 4 = 3 := by
      have hmod := congrArg (fun z : Nat => z % 4) hhform
      rw [hh4, Nat.mul_mod, hp4] at hmod
      have hslt : s % 4 < 4 := Nat.mod_lt _ (by decide)
      omega
    have hcenterMod :
        (data.center : ZMod B) = -(A : ZMod B) := by
      calc
        (data.center : ZMod B) = (A : ZMod B) ^ s := hcenterPow
        _ = -A :=
          zmod_pow_eq_neg_self_of_square_eq_neg_one_local
            hsquare hs4
    have hjac :
        jacobiSym (-((A : Int) + 1)) B = -1 := by
      simpa [A, B] using
        jacobi_sm2LucasReal_signed_successor_of_mod_eight_three
          generator.ordinate_pos generator.negative_equation
          hu hpThree
    have hnonsquare :
        ¬ IsSquare
          ((-((A : Int) + 1) : Int) : ZMod B) :=
      ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac
    apply hnonsquare
    refine ⟨(allocation.y : ZMod B), ?_⟩
    have hcenter :=
      congrArg
        (fun z : Nat => (z : ZMod B)) allocation.center_eq
    push_cast at hcenter
    calc
      ((-((A : Int) + 1) : Int) : ZMod B) =
          -(A : ZMod B) - 1 := by push_cast; ring
      _ = (data.center : ZMod B) - 1 := by rw [hcenterMod]
      _ = (allocation.y : ZMod B) ^ 2 := by
        rw [hcenter]
        ring
      _ = (allocation.y : ZMod B) * allocation.y := by ring
  · have hp4 : p % 4 = 1 := by
      have hmod := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
      rw [hpFive] at hmod
      omega
    have hs4 : s % 4 = 1 := by
      have hmod := congrArg (fun z : Nat => z % 4) hhform
      rw [hh4, Nat.mul_mod, hp4] at hmod
      have hslt : s % 4 < 4 := Nat.mod_lt _ (by decide)
      omega
    have hcenterMod :
        (data.center : ZMod B) = (A : ZMod B) := by
      calc
        (data.center : ZMod B) = (A : ZMod B) ^ s := hcenterPow
        _ = A :=
          zmod_pow_eq_self_of_square_eq_neg_one_local hsquare hs4
    have hjac :
        jacobiSym ((A : Int) - 1) B = -1 := by
      simpa [A, B] using
        jacobi_sm2LucasReal_predecessor_of_mod_eight_five
          generator.ordinate_pos generator.negative_equation
          hu hpFive
    have hnonsquare :
        ¬ IsSquare (((A : Int) - 1 : Int) : ZMod B) :=
      ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac
    apply hnonsquare
    refine ⟨(allocation.y : ZMod B), ?_⟩
    have hcenter :=
      congrArg
        (fun z : Nat => (z : ZMod B)) allocation.center_eq
    push_cast at hcenter
    calc
      (((A : Int) - 1 : Int) : ZMod B) =
          (A : ZMod B) - 1 := by push_cast; ring
      _ = (data.center : ZMod B) - 1 := by rw [hcenterMod]
      _ = (allocation.y : ZMod B) ^ 2 := by
        rw [hcenter]
        ring
      _ = (allocation.y : ZMod B) * allocation.y := by ring

/-- A prime divisor of the outer source exponent cannot be seven modulo
eight.  At that intermediate prime power the real coordinate is six modulo
eight, so its odd half is three modulo four.  But the intermediate real
coordinate divides the retained square predecessor `y² + 1`, which would
make minus one a square modulo that odd half. -/
theorem false_of_outer_prime_mod_eight_seven
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {p : Nat}
    (_hp : p.Prime)
    (hpH : p ∣ 2 * generator.outerIndex + 1)
    (hpSeven : p % 8 = 7) :
    False := by
  let K := data.upperKernel
  let P := generator.real
  let Q := generator.ordinate
  let h := 2 * generator.outerIndex + 1
  let s := h / p
  let A := sm2LucasReal P p
  let B := Q * sm2LucasCoeff P p
  have hpH' : p ∣ h := by
    simpa only [h] using hpH
  have hhform : h = p * s := by
    simpa only [s, mul_comm] using
      (Nat.div_mul_cancel hpH').symm
  have hhOdd : Odd h := by
    exact ⟨generator.outerIndex, by simp [h, two_mul]⟩
  have hsOdd : Odd s := by
    rw [hhform] at hhOdd
    exact (Nat.odd_mul.mp hhOdd).2
  obtain ⟨t, ht⟩ := hsOdd
  have hpFour : p % 4 = 3 := by
    have hmod := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
    rw [hpSeven] at hmod
    omega
  have hA8 : A % 8 = 6 := by
    simpa [A, P] using
      sm2LucasReal_mod_eight_of_index_mod_four_three
        generator.real_mod_eight hpFour
  have hcoords :
      generator.point ^ p =
        (⟨A, B⟩ : ℤ√(K : Int)) := by
    simpa [Sm2LowerSquareUpperSourceGenerator.point,
      sm2UpperNegativeUnit, A, B, K, P, Q] using
      sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel)
        (u := generator.real)
        (v := generator.ordinate)
        (n := p)
        generator.negative_equation
  have hsourceRe :
      (data.center : Int) =
        (generator.point ^ h).re := by
    have hpower := congrArg Zsqrtd.re generator.source_power
    simpa [Sm2LowerSquareUpperSourceGenerator.point,
      sm2UpperSourcePoint, h] using hpower
  have hAdivInt : (A : Int) ∣ (data.center : Int) := by
    have hdiv :=
      zsqrtd_real_dvd_odd_power_local K A B t
    rw [← ht, ← hcoords, ← pow_mul, ← hhform] at hdiv
    simpa [hsourceRe] using hdiv
  have hAdivCenter : A ∣ data.center :=
    Int.natCast_dvd_natCast.mp hAdivInt
  have hAdivPredecessor : A ∣ allocation.y ^ 2 + 1 := by
    rw [← allocation.center_eq]
    exact hAdivCenter
  let m := A / 2
  have hAform : A = 8 * (A / 8) + 6 := by
    have hdecomp := (Nat.mod_add_div A 8).symm
    rw [hA8] at hdecomp
    omega
  have hmFour : m % 4 = 3 := by
    dsimp [m]
    rw [hAform]
    omega
  have hmDvdA : m ∣ A := by
    dsimp [m]
    exact Nat.div_dvd_of_dvd (by
      rw [hAform]
      omega)
  have hmDvd : m ∣ allocation.y ^ 2 + 1 :=
    hmDvdA.trans hAdivPredecessor
  have hzero :
      ((allocation.y ^ 2 + 1 : Nat) : ZMod m) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hmDvd
  have hsquare :
      (allocation.y : ZMod m) ^ 2 = -1 := by
    push_cast at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hjac : jacobiSym (-1 : Int) m = -1 := by
    rw [jacobiSym.at_neg_one
        ((Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hmFour)),
      ZMod.χ₄_nat_three_mod_four hmFour]
  have hnonsquare :
      ¬ IsSquare (-1 : ZMod m) := by
    simpa using
      (ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac)
  apply hnonsquare
  exact
    ⟨(allocation.y : ZMod m),
      by simpa [pow_two] using hsquare.symm⟩

/-- Every prime divisor of the outer source exponent is one or seven modulo
eight. -/
theorem outer_prime_mod_eight_one_or_seven
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {p : Nat}
    (hp : p.Prime)
    (hpH : p ∣ 2 * generator.outerIndex + 1) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  let h := 2 * generator.outerIndex + 1
  have hpNeTwo : p ≠ 2 := by
    intro hpTwo
    subst p
    have hTwoDvd : 2 ∣ h := hpH
    have hmod :=
      Nat.mod_eq_zero_of_dvd hTwoDvd
    dsimp [h] at hmod
    omega
  have hpOdd : Odd p := hp.odd_of_ne_two hpNeTwo
  have hpOddMod : p % 2 = 1 := Nat.odd_iff.mp hpOdd
  have hpLt : p % 8 < 8 := Nat.mod_lt _ (by decide)
  by_contra hnot
  have hpClass : p % 8 = 3 ∨ p % 8 = 5 := by
    have hmod := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 8)
    rw [hpOddMod] at hmod
    omega
  exact generator.false_of_outer_prime_mod_eight_three_or_five
    hp hpH hpClass

/-- Every prime divisor of the outer source exponent is one modulo eight.
The Jacobi obstruction removes the `3` and `5` classes, while the retained
square predecessor removes the remaining `7` class. -/
theorem outer_prime_mod_eight_one
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    {p : Nat}
    (hp : p.Prime)
    (hpH : p ∣ 2 * generator.outerIndex + 1) :
    p % 8 = 1 := by
  rcases generator.outer_prime_mod_eight_one_or_seven hp hpH with
    hpOne | hpSeven
  · exact hpOne
  · exact
      (generator.false_of_outer_prime_mod_eight_seven
        hp hpH hpSeven).elim

/-- Either the source is the first power of its rank-normalized generator,
or its outer exponent has a prime divisor congruent to one modulo eight. -/
theorem outerIndex_eq_zero_or_exists_prime_mod_eight_one
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    generator.outerIndex = 0 ∨
      ∃ p : Nat,
        p.Prime ∧ p % 8 = 1 ∧
          p ∣ 2 * generator.outerIndex + 1 := by
  by_cases ht : generator.outerIndex = 0
  · exact Or.inl ht
  · right
    have hhNeOne : 2 * generator.outerIndex + 1 ≠ 1 := by
      omega
    obtain ⟨p, hp, hpH⟩ :=
      Nat.exists_prime_and_dvd hhNeOne
    exact
      ⟨p, hp, generator.outer_prime_mod_eight_one hp hpH, hpH⟩

/-- The first nontrivial outer source phase begins only at exponent
seventeen: equivalently, either the outer index is zero or it is at least
eight. -/
theorem outerIndex_eq_zero_or_eight_le
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    generator.outerIndex = 0 ∨ 8 ≤ generator.outerIndex := by
  rcases
      generator.outerIndex_eq_zero_or_exists_prime_mod_eight_one with
    ht | ⟨p, hp, hpEight, hpH⟩
  · exact Or.inl ht
  · right
    have hpTwo : 2 ≤ p := hp.two_le
    have hpNeNine : p ≠ 9 := by
      intro hpNine
      subst p
      norm_num at hp
    have hpSeventeen : 17 ≤ p := by
      have hpLt := Nat.mod_lt p (by decide : 0 < 8)
      omega
    have hpLe :
        p ≤ 2 * generator.outerIndex + 1 :=
      Nat.le_of_dvd (by omega) hpH
    omega

/-- In the first outer source phase, the rank-normalized generator is the
retained source point itself.  In particular, its real coordinate has a
literal square predecessor and its successor retains the canonical lower
square-cube allocation.

This is the exact typed shell for the `h = 1` residual.  It is not an
obstruction to that residual. -/
theorem first_outer_source_shell
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hzero : generator.outerIndex = 0) :
    generator.real = data.center ∧
      generator.ordinate =
        data.upperKernel * data.upperSquarePart ∧
      generator.real = allocation.y ^ 2 + 1 ∧
      SquareCubeNormalForm
        (generator.real + 1)
        allocation.linearUpperSquarePart data.pell.D := by
  have hsource := generator.source_power
  rw [hzero] at hsource
  have hrealInt := congrArg Zsqrtd.re hsource
  have hordinateInt := congrArg Zsqrtd.im hsource
  have hreal : generator.real = data.center := by
    exact_mod_cast
      (by
        simpa [sm2UpperSourcePoint] using hrealInt.symm :
          (generator.real : Int) = data.center)
  have hordinate :
      generator.ordinate =
        data.upperKernel * data.upperSquarePart := by
    exact_mod_cast
      (by
        simpa [sm2UpperSourcePoint] using hordinateInt.symm :
          (generator.ordinate : Int) =
            data.upperKernel * data.upperSquarePart)
  have hpredecessor :
      generator.real = allocation.y ^ 2 + 1 :=
    hreal.trans allocation.center_eq
  refine ⟨hreal, hordinate, hpredecessor, ?_⟩
  simpa [hpredecessor] using allocation.linearUpperNormalForm

/-- In the first outer phase, every nontrivial exact Pell rank contains a
source-preserving prime block with exactly one missing kernel prime.

The intermediate point is not itself a divisible negative-Pell source:
its ordinate has GCD `K / p` with the kernel.  Its `p`th power is the
original source point, so the same centre and lower successor allocation
are retained exactly. -/
theorem exists_rank_prime_defect_block
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hzero : generator.outerIndex = 0)
    (hRgt :
      1 <
        pellRank data.upperKernel allocation.upper_pellKernel) :
    ∃ p n A B c : Nat,
      p.Prime ∧
        p % 8 = 1 ∧
        41 ≤ p ∧
        0 < n ∧
        Odd n ∧
        pellRank data.upperKernel allocation.upper_pellKernel =
          n * p ∧
        sm2UpperNegativeUnit data.upperKernel
            generator.upperOrbit.rootX generator.upperOrbit.rootY ^ n =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        B = (data.upperKernel / p) * c ∧
        data.upperKernel.gcd B = data.upperKernel / p ∧
        A ^ 2 + 1 =
          p * (data.upperKernel / p) ^ 3 * c ^ 2 ∧
        ¬ p ∣ c ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p ∧
        sm2LucasReal A p = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A p + 1)
          allocation.linearUpperSquarePart data.pell.D ∧
        c * sm2LucasCoeff A p =
          p * data.upperSquarePart := by
  let K := data.upperKernel
  let u := generator.upperOrbit.rootX
  let v := generator.upperOrbit.rootY
  let R := pellRank K allocation.upper_pellKernel
  have hRgt' : 1 < R := by simpa [R] using hRgt
  have hRNeOne : R ≠ 1 := ne_of_gt hRgt'
  obtain ⟨p, hp, hpR⟩ := Nat.exists_prime_and_dvd hRNeOne
  let n := R / p
  have hRform : R = n * p := by
    simpa [n] using (Nat.div_mul_cancel hpR).symm
  have hpEight : p % 8 = 1 := by
    exact generator.rank_prime_mod_eight_one hp (by simpa [R] using hpR)
  have hpK : p ∣ K := by
    exact hpR.trans (pellRank_dvd_kernel K allocation.upper_pellKernel)
  have hpNeSeventeen : p ≠ 17 := by
    intro hpEq
    subst p
    exact generator.seventeen_not_dvd_upperKernel hpK
  have hpFortyOne : 41 ≤ p := by
    have hpSeventeen : 17 ≤ p := by
      have hpLt := Nat.mod_lt p (by decide : 0 < 8)
      have hpTwo := hp.two_le
      have hpNeNine : p ≠ 9 := by
        intro hpNine
        subst p
        norm_num at hp
      omega
    have hpNeTwentyFive : p ≠ 25 := by
      intro hpTwentyFive
      subst p
      norm_num at hp
    have hpNeThirtyThree : p ≠ 33 := by
      intro hpThirtyThree
      subst p
      norm_num at hp
    omega
  have hRPos : 0 < R := pellRank_pos K allocation.upper_pellKernel
  have hnPos : 0 < n := by
    rw [hRform] at hRPos
    exact Nat.pos_of_mul_pos_right hRPos
  have hROdd : Odd R := by
    rw [Nat.odd_iff]
    have hR8 : R % 8 = 1 := by
      simpa [R] using generator.rank_mod_eight_eq_one
    have hmod : R % 8 % 2 = R % 2 :=
      Nat.mod_mod_of_dvd R (by decide : 2 ∣ 8)
    rw [hR8] at hmod
    exact hmod.symm
  have hnOdd : Odd n := by
    rw [hRform] at hROdd
    exact (Nat.odd_mul.mp hROdd).1
  let A := sm2LucasReal u n
  let B := v * sm2LucasCoeff u n
  have hcoords :
      sm2UpperNegativeUnit K u v ^ n =
        (⟨A, B⟩ : ℤ√(K : Int)) := by
    simpa [A, B] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := K) (u := u) (v := v) (n := n)
        generator.upperOrbit.root_equation)
  obtain
      ⟨d, e, c, hdGcd, hdProfile, _heDef, hBdc,
        hKed, hed, hec, hpartial⟩ :=
    sm2NegativeUnit_odd_partial_depth_normal_form
      allocation.upper_pellKernel.2
      generator.upperOrbit.rootY_pos
      generator.upperOrbit.root_equation hnOdd
  let G := K.gcd v
  have hAdapter : R = K / G := by
    simpa [K, R, G, v] using
      generator.pellRank_eq_kernel_div_gcd_rootY
  have hGdvdK : G ∣ K := Nat.gcd_dvd_left _ _
  have hKsplit : K = R * G := by
    rw [hAdapter]
    exact (Nat.div_mul_cancel hGdvdK).symm
  have hGPos : 0 < G :=
    Nat.gcd_pos_of_pos_left v
      (Nat.zero_lt_of_lt allocation.upper_pellKernel.1)
  have hRGcdN : R.gcd n = n :=
    Nat.gcd_eq_right_iff_dvd.mpr ⟨p, hRform⟩
  have hdGn : d = G * n := by
    calc
      d =
          K.gcd v * (K / K.gcd v).gcd n := hdProfile
      _ = G * R.gcd n := by rw [← hAdapter]
      _ = G * n := by rw [hRGcdN]
  have hKdivP : K / p = G * n := by
    calc
      K / p = (R * G) / p := by rw [hKsplit]
      _ = ((n * p) * G) / p := by rw [hRform]
      _ = ((G * n) * p) / p := by
            congr 1
            ring
      _ = G * n := Nat.mul_div_cancel _ hp.pos
  have hdKdivP : d = K / p := hdGn.trans hKdivP.symm
  have hdPos : 0 < d := by
    rw [hdGn]
    positivity
  have hKpd : K = p * d := by
    calc
      K = (K / p) * p := (Nat.div_mul_cancel hpK).symm
      _ = p * d := by rw [hdKdivP]; ring
  have heP : e = p := by
    apply Nat.eq_of_mul_eq_mul_right hdPos
    calc
      e * d = K := hKed.symm
      _ = p * d := hKpd
  have hBform : B = (K / p) * c := by
    simpa [B, hdKdivP] using hBdc
  have hGcdForm : K.gcd B = K / p := by
    calc
      K.gcd B = d := by simpa [K, B] using hdGcd.symm
      _ = K / p := hdKdivP
  have hdefect :
      A ^ 2 + 1 = p * (K / p) ^ 3 * c ^ 2 := by
    simpa [A, heP, hdKdivP] using hpartial
  have hpNotDvdC : ¬ p ∣ c := by
    intro hpc
    have hpGcd : p ∣ p.gcd c := Nat.dvd_gcd dvd_rfl hpc
    have hpcop : p.Coprime c := by simpa [heP] using hec
    rw [hpcop.gcd_eq_one] at hpGcd
    exact hp.not_dvd_one hpGcd
  have hsource :
      sm2UpperSourcePoint K data.center
          (K * data.upperSquarePart) =
        (⟨A, B⟩ : ℤ√(K : Int)) ^ p := by
    calc
      sm2UpperSourcePoint K data.center
            (K * data.upperSquarePart) =
          generator.point := by
            simpa [K, Sm2LowerSquareUpperSourceGenerator.point,
              hzero] using generator.source_power
      _ =
          sm2UpperNegativeUnit K u v ^ R := by
            simpa [K, u, v, R,
              Sm2LowerSquareUpperSourceGenerator.point] using
              generator.generator_power.symm
      _ =
          sm2UpperNegativeUnit K u v ^ (n * p) := by rw [hRform]
      _ =
          (sm2UpperNegativeUnit K u v ^ n) ^ p := by rw [pow_mul]
      _ = (⟨A, B⟩ : ℤ√(K : Int)) ^ p := by rw [hcoords]
  have hblockNegative :
      A ^ 2 + 1 = K * B ^ 2 := by
    simpa [K, u, v, A, B] using
      (sm2LucasReal_odd_negative_equation
        (K := K) (u := u) (v := v) (n := n)
        generator.upperOrbit.root_equation hnOdd)
  have hpowerCoordinates :
      (⟨A, B⟩ : ℤ√(K : Int)) ^ p =
        (⟨sm2LucasReal A p,
            B * sm2LucasCoeff A p⟩ :
          ℤ√(K : Int)) := by
    simpa [sm2UpperNegativeUnit] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := K) (u := A) (v := B) (n := p)
        hblockNegative)
  have hrealInt := congrArg Zsqrtd.re hsource
  rw [hpowerCoordinates] at hrealInt
  have hrealCenter :
      sm2LucasReal A p = data.center := by
    exact_mod_cast
      (by
        simpa [sm2UpperSourcePoint] using hrealInt.symm :
          (sm2LucasReal A p : Int) = data.center)
  have hreal :
      sm2LucasReal A p = allocation.y ^ 2 + 1 :=
    hrealCenter.trans allocation.center_eq
  have hsuccessor :
      SquareCubeNormalForm
        (sm2LucasReal A p + 1)
        allocation.linearUpperSquarePart data.pell.D := by
    simpa [hreal] using allocation.linearUpperNormalForm
  have himagInt := congrArg Zsqrtd.im hsource
  rw [hpowerCoordinates] at himagInt
  have himag :
      K * data.upperSquarePart =
        B * sm2LucasCoeff A p := by
    exact_mod_cast
      (by
        simpa [sm2UpperSourcePoint] using himagInt :
          (K * data.upperSquarePart : Int) =
            (B * sm2LucasCoeff A p : Nat))
  have hrepair :
      c * sm2LucasCoeff A p =
        p * data.upperSquarePart := by
    apply Nat.eq_of_mul_eq_mul_left hdPos
    calc
      d * (c * sm2LucasCoeff A p) =
          B * sm2LucasCoeff A p := by rw [hBform, hdKdivP]; ring
      _ = K * data.upperSquarePart := himag.symm
      _ = d * (p * data.upperSquarePart) := by rw [hKpd]; ring
  exact
    ⟨p, n, A, B, c, hp, hpEight, hpFortyOne, hnPos, hnOdd,
      by simpa [R] using hRform,
      by simpa [K, u, v] using hcoords,
      by simpa [K] using hBform,
      by simpa [K] using hGcdForm,
      by simpa [K, A] using hdefect,
      hpNotDvdC,
      by simpa [K] using hsource,
      hreal, hsuccessor, hrepair⟩

/-- Every nontrivial outer source phase contains an exact prime block.

Writing the outer exponent as `m * p`, the intermediate point
`A + B * sqrt K` remains a norm-minus-one solution with the full source
depth `K ∣ B`.  Its `p`th power is the retained source point, and its real
coordinate is therefore the exact square-predecessor polynomial source.

This is a source-preserving reduction to a prime shifted-power problem.  It
does not assert that the resulting polynomial equations are impossible. -/
theorem exists_outer_prime_block
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hzero : generator.outerIndex ≠ 0) :
    ∃ p m A B : Nat,
      p.Prime ∧
        p % 8 = 1 ∧
        17 ≤ p ∧
        0 < m ∧
        Odd m ∧
        2 * generator.outerIndex + 1 = m * p ∧
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A ^ 2 + 1 = data.upperKernel * B ^ 2 ∧
        data.upperKernel ∣ B ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p ∧
        sm2LucasReal A p = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A p + 1)
          allocation.linearUpperSquarePart data.pell.D := by
  rcases generator.outerIndex_eq_zero_or_exists_prime_mod_eight_one with
    ht | ⟨p, hp, hpEight, hpH⟩
  · exact (hzero ht).elim
  · obtain ⟨m, hm⟩ := hpH
    have hhOdd : Odd (2 * generator.outerIndex + 1) := by
      exact ⟨generator.outerIndex, by omega⟩
    have hmFactor :
        2 * generator.outerIndex + 1 = m * p := by
      simpa [Nat.mul_comm] using hm
    have hmOdd : Odd m := by
      rw [hmFactor] at hhOdd
      exact (Nat.odd_mul.mp hhOdd).1
    have hmPos : 0 < m := by
      obtain ⟨r, hr⟩ := hmOdd
      omega
    have hpSeventeen : 17 ≤ p := by
      have hpLt := Nat.mod_lt p (by decide : 0 < 8)
      have hpTwo := hp.two_le
      have hpNeNine : p ≠ 9 := by
        intro hpNine
        subst p
        norm_num at hp
      omega
    let A := sm2LucasReal generator.real m
    let B := generator.ordinate * sm2LucasCoeff generator.real m
    have hcoords :
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) := by
      simpa [Sm2LowerSquareUpperSourceGenerator.point,
        sm2UpperNegativeUnit, A, B] using
        (sm2UpperNegativeUnit_pow_coordinates
          (K := data.upperKernel)
          (u := generator.real)
          (v := generator.ordinate)
          (n := m)
          generator.negative_equation)
    have hnegative :
        A ^ 2 + 1 = data.upperKernel * B ^ 2 := by
      simpa [A, B] using
        (sm2LucasReal_odd_negative_equation
          (K := data.upperKernel)
          (u := generator.real)
          (v := generator.ordinate)
          (n := m)
          generator.negative_equation hmOdd)
    have hkernel : data.upperKernel ∣ B := by
      exact generator.kernel_dvd_ordinate.trans
        (by
          simp only [B]
          exact dvd_mul_right generator.ordinate
            (sm2LucasCoeff generator.real m))
    have hsource :
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p := by
      calc
        sm2UpperSourcePoint data.upperKernel data.center
              (data.upperKernel * data.upperSquarePart) =
            generator.point ^ (2 * generator.outerIndex + 1) := by
              simpa [Sm2LowerSquareUpperSourceGenerator.point] using
                generator.source_power
        _ = generator.point ^ (m * p) := by rw [hmFactor]
        _ = (generator.point ^ m) ^ p := by rw [pow_mul]
        _ = (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p := by
              rw [hcoords]
    have hpowerCoordinates :
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p =
          (⟨sm2LucasReal A p,
              B * sm2LucasCoeff A p⟩ :
            ℤ√(data.upperKernel : Int)) := by
      simpa [sm2UpperNegativeUnit] using
        (sm2UpperNegativeUnit_pow_coordinates
          (K := data.upperKernel)
          (u := A)
          (v := B)
          (n := p)
          hnegative)
    have hrealInt := congrArg Zsqrtd.re hsource
    rw [hpowerCoordinates] at hrealInt
    have hrealCenter :
        sm2LucasReal A p = data.center := by
      exact_mod_cast
        (by
          simpa [sm2UpperSourcePoint] using hrealInt.symm :
            (sm2LucasReal A p : Int) = data.center)
    have hreal :
        sm2LucasReal A p = allocation.y ^ 2 + 1 :=
      hrealCenter.trans allocation.center_eq
    have hsuccessor :
        SquareCubeNormalForm
          (sm2LucasReal A p + 1)
          allocation.linearUpperSquarePart data.pell.D := by
      simpa [hreal] using allocation.linearUpperNormalForm
    exact
      ⟨p, m, A, B, hp, hpEight, hpSeventeen, hmPos, hmOdd,
        hmFactor, hcoords, hnegative, hkernel, hsource, hreal,
        hsuccessor⟩

/-- Away from the distinguished outer prime `17`, every nontrivial outer
phase contains a full-depth prime block with prime at least `41`.

This is the exact large-prime refinement of `exists_outer_prime_block`.
All source, reconstruction, and lower-successor fields are retained. -/
theorem exists_outer_large_prime_block
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hzero : generator.outerIndex ≠ 0)
    (h17 : ¬ 17 ∣ 2 * generator.outerIndex + 1) :
    ∃ p m A B : Nat,
      p.Prime ∧
        p % 8 = 1 ∧
        41 ≤ p ∧
        0 < m ∧
        Odd m ∧
        2 * generator.outerIndex + 1 = m * p ∧
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A ^ 2 + 1 = data.upperKernel * B ^ 2 ∧
        data.upperKernel ∣ B ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p ∧
        sm2LucasReal A p = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A p + 1)
          allocation.linearUpperSquarePart data.pell.D := by
  obtain
      ⟨p, m, A, B, hp, hpEight, hpSeventeen, hmPos, hmOdd,
        hmFactor, hcoords, hnegative, hkernel, hsource, hreal,
        hsuccessor⟩ :=
    generator.exists_outer_prime_block hzero
  have hpDvdOuter :
      p ∣ 2 * generator.outerIndex + 1 :=
    ⟨m, by simpa [Nat.mul_comm] using hmFactor⟩
  have hpNeSeventeen : p ≠ 17 := by
    intro hpEq
    subst p
    exact h17 hpDvdOuter
  have hpNeTwentyFive : p ≠ 25 := by
    intro hpEq
    subst p
    norm_num at hp
  have hpNeThirtyThree : p ≠ 33 := by
    intro hpEq
    subst p
    norm_num at hp
  have hpFortyOne : 41 ≤ p := by
    omega
  exact
    ⟨p, m, A, B, hp, hpEight, hpFortyOne, hmPos, hmOdd,
      hmFactor, hcoords, hnegative, hkernel, hsource, hreal,
      hsuccessor⟩

/-- The real-coordinate recurrence evaluated directly in a residue ring.
This is a local implementation detail for the exact `17^2` calculation
below. -/
private def sm2LucasRealMod (q : Nat) (u : ZMod q) :
    Nat → ZMod q
  | 0 => 1
  | 1 => u
  | n + 2 =>
      2 * u * sm2LucasRealMod q u (n + 1) +
        sm2LucasRealMod q u n

@[simp]
private theorem sm2LucasRealMod_zero (q : Nat) (u : ZMod q) :
    sm2LucasRealMod q u 0 = 1 := rfl

@[simp]
private theorem sm2LucasRealMod_one (q : Nat) (u : ZMod q) :
    sm2LucasRealMod q u 1 = u := rfl

@[simp]
private theorem sm2LucasRealMod_succ_succ
    (q : Nat) (u : ZMod q) (n : Nat) :
    sm2LucasRealMod q u (n + 2) =
      2 * u * sm2LucasRealMod q u (n + 1) +
        sm2LucasRealMod q u n := rfl

private theorem sm2LucasReal_cast (q u n : Nat) :
    ((sm2LucasReal u n : Nat) : ZMod q) =
      sm2LucasRealMod q (u : ZMod q) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
      rw [sm2LucasReal_succ_succ,
        sm2LucasRealMod_succ_succ]
      push_cast
      rw [h0, h1]

set_option maxRecDepth 10000 in
private theorem sm2LucasReal_seventeen_minusOne_mod_twoEightyNine :
    ∀ t : ZMod 289,
      sm2LucasRealMod 289 (17 * t + 16) 17 = 186 := by
  decide

set_option maxRecDepth 10000 in
private theorem sm2LucasReal_seventeen_plusOne_mod_twoEightyNine :
    ∀ t : ZMod 289,
      sm2LucasRealMod 289 (17 * t + 1) 17 = 103 := by
  decide

set_option maxRecDepth 10000 in
private theorem sm2LucasReal_seventeen_mod_seventeen :
    ∀ a : ZMod 17,
      sm2LucasRealMod 17 a 17 = a := by
  decide

private theorem sm2LucasReal_seventeen_sq_one_mod_nine :
    ∀ a : ZMod 9,
      sm2LucasRealMod 9 a 17 ^ 2 = 1 →
        a = 4 ∨ a = 5 := by
  decide

private theorem square_eq_neg_one_classes_mod_seventeen :
    ∀ a : ZMod 17, a ^ 2 = -1 → a = 4 ∨ a = 13 := by
  decide

set_option maxRecDepth 10000 in
private theorem oneHundredTwo_not_square_mod_twoEightyNine :
    ∀ y : ZMod 289, y ^ 2 ≠ 102 := by
  decide

/-- Exact `17`-adic localization of a shifted square/powerful pair for the
seventeenth real-coordinate polynomial.  These are local admissible classes,
not a claim that every displayed class reconstructs a source. -/
theorem sm2LucasReal_seventeen_admissible_classes
    {A y z D : Nat}
    (hpredecessor : sm2LucasReal A 17 = y ^ 2 + 1)
    (hsuccessor :
      SquareCubeNormalForm (sm2LucasReal A 17 + 1) z D) :
    A % 17 = 0 ∨ A % 17 = 2 ∨ A % 17 = 3 ∨
      A % 17 = 5 ∨ A % 17 = 9 ∨ A % 17 = 10 ∨
        A % 17 = 14 := by
  have hANeOne : (A : ZMod 17) ≠ 1 := by
    intro hAOne
    have hAmod : A % 17 = 1 := by
      apply (ZMod.natCast_eq_natCast_iff' A 1 17).mp
      simpa using hAOne
    have hAform : A = 17 * (A / 17) + 1 := by
      have hdecomp := (Nat.mod_add_div A 17).symm
      rw [hAmod] at hdecomp
      omega
    have hF :
        ((sm2LucasReal A 17 : Nat) : ZMod 289) = 103 := by
      rw [sm2LucasReal_cast, hAform]
      push_cast
      exact
        sm2LucasReal_seventeen_plusOne_mod_twoEightyNine
          ((A / 17 : Nat) : ZMod 289)
    have hcast :=
      congrArg (fun n : Nat => (n : ZMod 289)) hpredecessor
    push_cast at hcast
    rw [hF] at hcast
    have hySquare : (y : ZMod 289) ^ 2 = 102 := by
      linear_combination -hcast
    exact oneHundredTwo_not_square_mod_twoEightyNine y hySquare
  have hANeMinusOne : (A : ZMod 17) ≠ 16 := by
    intro hAMinusOne
    have hAmod : A % 17 = 16 := by
      apply (ZMod.natCast_eq_natCast_iff' A 16 17).mp
      simpa using hAMinusOne
    have hAform : A = 17 * (A / 17) + 16 := by
      have hdecomp := (Nat.mod_add_div A 17).symm
      rw [hAmod] at hdecomp
      omega
    have hF289 :
        ((sm2LucasReal A 17 : Nat) : ZMod 289) = 186 := by
      rw [sm2LucasReal_cast, hAform]
      push_cast
      exact
        sm2LucasReal_seventeen_minusOne_mod_twoEightyNine
          ((A / 17 : Nat) : ZMod 289)
    have h17Dvd : 17 ∣ sm2LucasReal A 17 + 1 := by
      apply
        (ZMod.natCast_eq_zero_iff
          (sm2LucasReal A 17 + 1) 17).mp
      push_cast
      rw [sm2LucasReal_cast,
        sm2LucasReal_seventeen_mod_seventeen]
      rw [hAMinusOne]
      decide
    have h289NotDvd : ¬ 289 ∣ sm2LucasReal A 17 + 1 := by
      intro h289
      have hzero :=
        (ZMod.natCast_eq_zero_iff
          (sm2LucasReal A 17 + 1) 289).mpr h289
      push_cast at hzero
      rw [hF289] at hzero
      exact (by decide : (187 : ZMod 289) ≠ 0) hzero
    have hpowerful :=
      powerfulPos_of_squareCubeNormalForm hsuccessor
    exact h289NotDvd
      (by
        simpa using hpowerful.2 17 (by norm_num) h17Dvd)
  have hpredecessorCast :=
    congrArg (fun n : Nat => (n : ZMod 17)) hpredecessor
  push_cast at hpredecessorCast
  rw [sm2LucasReal_cast,
    sm2LucasReal_seventeen_mod_seventeen] at hpredecessorCast
  have hAmodEq : A % 17 = (y ^ 2 + 1) % 17 := by
    apply (ZMod.natCast_eq_natCast_iff' A (y ^ 2 + 1) 17).mp
    simpa using hpredecessorCast
  have hAmodNeOne : A % 17 ≠ 1 := by
    intro hA
    apply hANeOne
    exact (ZMod.natCast_eq_natCast_iff' A 1 17).mpr hA
  have hAmodNeMinusOne : A % 17 ≠ 16 := by
    intro hA
    apply hANeMinusOne
    exact (ZMod.natCast_eq_natCast_iff' A 16 17).mpr hA
  have hyLt : y % 17 < 17 := Nat.mod_lt _ (by decide)
  interval_cases hy : y % 17 <;>
    norm_num [Nat.add_mod, Nat.pow_mod, hy] at hAmodEq <;>
    omega

/-- The `17`th real-coordinate polynomial cannot have a powerful successor
whose canonical cube kernel is divisible by `17`.

Modulo `17`, divisibility of the successor forces `A = -1`.  The complete
lift modulo `17^2` is then

```text
sm2LucasReal A 17 + 1 = 187 = 11 * 17 mod 289,
```

so the successor has exact `17`-depth one rather than the depth at least
three forced by `17 ∣ D`. -/
theorem seventeen_not_dvd_sm2LucasReal_seventeen_successor_kernel
    {A z D : Nat}
    (hform :
      SquareCubeNormalForm
        (sm2LucasReal A 17 + 1) z D) :
    ¬ 17 ∣ D := by
  rintro ⟨d, rfl⟩
  have hvalue := hform.2.2.1
  have hcast17 :=
    congrArg (fun n : Nat => (n : ZMod 17)) hvalue
  push_cast at hcast17
  rw [sm2LucasReal_cast,
    sm2LucasReal_seventeen_mod_seventeen] at hcast17
  rw [show (17 : ZMod 17) = 0 by decide] at hcast17
  simp at hcast17
  have hAcast : (A : ZMod 17) = 16 := by
    have hzero : (A : ZMod 17) + 1 = 0 := hcast17
    calc
      (A : ZMod 17) = -1 :=
        eq_neg_of_add_eq_zero_left hzero
      _ = 16 := by decide
  have hAmod : A % 17 = 16 := by
    apply (ZMod.natCast_eq_natCast_iff' A 16 17).mp
    simpa using hAcast
  have hAform : A = 17 * (A / 17) + 16 := by
    have hdecomp := (Nat.mod_add_div A 17).symm
    rw [hAmod] at hdecomp
    omega
  have hF :
      ((sm2LucasReal A 17 : Nat) : ZMod 289) = 186 := by
    rw [sm2LucasReal_cast, hAform]
    push_cast
    exact
      sm2LucasReal_seventeen_minusOne_mod_twoEightyNine
        ((A / 17 : Nat) : ZMod 289)
  have hcast289 :=
    congrArg (fun n : Nat => (n : ZMod 289)) hvalue
  push_cast at hcast289
  rw [hF] at hcast289
  rw [mul_pow, show (17 : ZMod 289) ^ 3 = 0 by decide] at hcast289
  simp at hcast289
  have hzero : (187 : ZMod 289) = 0 := by
    norm_num at hcast289
    exact hcast289
  exact (by decide : (187 : ZMod 289) ≠ 0) hzero

/-- If the exact outer source exponent contains a `17`-block, then the
canonical lower kernel is not divisible by `17`.

This is a coupled leaf theorem: the intermediate upper norm-minus-one point
is converted back to the retained lower successor normal form before the
exact `17^2` obstruction is applied. -/
theorem seventeen_not_dvd_lowerKernel_of_dvd_outer_exponent
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (h17 : 17 ∣ 2 * generator.outerIndex + 1) :
    ¬ 17 ∣ data.pell.D := by
  obtain ⟨m, hm⟩ := h17
  have hmFactor :
      2 * generator.outerIndex + 1 = m * 17 := by
    simpa [Nat.mul_comm] using hm
  have hhOdd : Odd (2 * generator.outerIndex + 1) := by
    exact ⟨generator.outerIndex, by omega⟩
  have hmOdd : Odd m := by
    rw [hmFactor] at hhOdd
    exact (Nat.odd_mul.mp hhOdd).1
  let A := sm2LucasReal generator.real m
  let B := generator.ordinate * sm2LucasCoeff generator.real m
  have hcoords :
      generator.point ^ m =
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) := by
    simpa [Sm2LowerSquareUpperSourceGenerator.point,
      sm2UpperNegativeUnit, A, B] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel)
        (u := generator.real)
        (v := generator.ordinate)
        (n := m)
        generator.negative_equation)
  have hnegative :
      A ^ 2 + 1 = data.upperKernel * B ^ 2 := by
    simpa [A, B] using
      (sm2LucasReal_odd_negative_equation
        (K := data.upperKernel)
        (u := generator.real)
        (v := generator.ordinate)
        (n := m)
        generator.negative_equation hmOdd)
  have hsource :
      sm2UpperSourcePoint data.upperKernel data.center
          (data.upperKernel * data.upperSquarePart) =
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 := by
    calc
      sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          generator.point ^ (2 * generator.outerIndex + 1) := by
            simpa [Sm2LowerSquareUpperSourceGenerator.point] using
              generator.source_power
      _ = generator.point ^ (m * 17) := by rw [hmFactor]
      _ = (generator.point ^ m) ^ 17 := by rw [pow_mul]
      _ = (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 := by
            rw [hcoords]
  have hpowerCoordinates :
      (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 =
        (⟨sm2LucasReal A 17,
            B * sm2LucasCoeff A 17⟩ :
          ℤ√(data.upperKernel : Int)) := by
    simpa [sm2UpperNegativeUnit] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel)
        (u := A)
        (v := B)
        (n := 17)
        hnegative)
  have hrealInt := congrArg Zsqrtd.re hsource
  rw [hpowerCoordinates] at hrealInt
  have hrealCenter :
      sm2LucasReal A 17 = data.center := by
    exact_mod_cast
      (by
        simpa [sm2UpperSourcePoint] using hrealInt.symm :
          (sm2LucasReal A 17 : Int) = data.center)
  have hreal :
      sm2LucasReal A 17 = allocation.y ^ 2 + 1 :=
    hrealCenter.trans allocation.center_eq
  have hsuccessor :
      SquareCubeNormalForm
        (sm2LucasReal A 17 + 1)
        allocation.linearUpperSquarePart data.pell.D := by
    rw [hreal]
    simpa using allocation.linearUpperNormalForm
  exact
    seventeen_not_dvd_sm2LucasReal_seventeen_successor_kernel
      hsuccessor

/-- Every exact source generator has outer exponent one modulo eight. -/
theorem outer_exponent_mod_eight_eq_one
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    (2 * generator.outerIndex + 1) % 8 = 1 := by
  let h := 2 * generator.outerIndex + 1
  have hh4 : h % 4 = 1 := by
    simpa [h] using generator.outer_phase_mod_four
  have hnot : h % 8 ≠ 5 := by
    intro hfive
    exact generator.false_of_outer_exponent_mod_eight_five
      (by simpa [h] using hfive)
  have hlt : h % 8 < 8 := Nat.mod_lt _ (by decide)
  have hmod : h % 8 % 4 = h % 4 :=
    Nat.mod_mod_of_dvd h (by decide : 4 ∣ 8)
  rw [hh4] at hmod
  simpa [h] using (by omega : h % 8 = 1)

/-- Combining the exact modulo-eight obstruction with the two oriented
modulo-twelve phases leaves precisely the classes one and seventeen modulo
twenty-four. -/
theorem outer_exponent_mod_twentyFour
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    (2 * generator.outerIndex + 1) % 24 = 1 ∨
      (2 * generator.outerIndex + 1) % 24 = 17 := by
  let h := 2 * generator.outerIndex + 1
  have h8 : h % 8 = 1 := by
    simpa [h] using generator.outer_exponent_mod_eight_eq_one
  have hmod8 : h % 24 % 8 = h % 8 :=
    Nat.mod_mod_of_dvd h (by decide : 8 ∣ 24)
  have hmod12 : h % 24 % 12 = h % 12 :=
    Nat.mod_mod_of_dvd h (by decide : 12 ∣ 24)
  have hlt : h % 24 < 24 := Nat.mod_lt _ (by decide)
  rcases generator.oriented_phase with hOne | hFive
  · left
    have h12 : h % 12 = 1 := by
      simpa [h] using hOne.2
    rw [h8] at hmod8
    rw [h12] at hmod12
    simpa [h] using (by omega : h % 24 = 1)
  · right
    have h12 : h % 12 = 5 := by
      simpa [h] using hFive.2
    rw [h8] at hmod8
    rw [h12] at hmod12
    simpa [h] using (by omega : h % 24 = 17)

/-- A divisor `17` of the outer exponent produces a specialized complete
prime block.  The complementary exponent and intermediate real coordinate
retain their exact modulo-eight phases. -/
theorem exists_seventeen_outer_block_of_dvd_outer_exponent
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (h17 : 17 ∣ 2 * generator.outerIndex + 1) :
    ∃ m A B : Nat,
      0 < m ∧
        Odd m ∧
        m % 8 = 1 ∧
        A % 8 = 2 ∧
        2 * generator.outerIndex + 1 = m * 17 ∧
        B =
          generator.ordinate *
            sm2LucasCoeff generator.real m ∧
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A ^ 2 + 1 = data.upperKernel * B ^ 2 ∧
        data.upperKernel ∣ B ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 ∧
        sm2LucasReal A 17 = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A 17 + 1)
          allocation.linearUpperSquarePart data.pell.D := by
  obtain ⟨m, hm⟩ := h17
  have hmFactor :
      2 * generator.outerIndex + 1 = m * 17 := by
    simpa [Nat.mul_comm] using hm
  have hhOdd : Odd (2 * generator.outerIndex + 1) := by
    exact ⟨generator.outerIndex, by omega⟩
  have hmOdd : Odd m := by
    rw [hmFactor] at hhOdd
    exact (Nat.odd_mul.mp hhOdd).1
  have hmPos : 0 < m := by
    obtain ⟨r, hr⟩ := hmOdd
    omega
  have hmEight : m % 8 = 1 := by
    have hmod := congrArg (fun n : Nat => n % 8) hmFactor
    rw [generator.outer_exponent_mod_eight_eq_one,
      Nat.mul_mod] at hmod
    norm_num at hmod
    omega
  let A := sm2LucasReal generator.real m
  let B := generator.ordinate * sm2LucasCoeff generator.real m
  have hAEight : A % 8 = 2 := by
    have hmFour : m % 4 = 1 := by
      have hmod : m % 8 % 4 = m % 4 :=
        Nat.mod_mod_of_dvd m (by decide : 4 ∣ 8)
      rw [hmEight] at hmod
      exact hmod.symm
    simpa [A, sm2LucasRealResidue, hmFour] using
      (sm2LucasReal_mod_eight
        (n := m) generator.real_mod_eight)
  have hcoords :
      generator.point ^ m =
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) := by
    simpa [Sm2LowerSquareUpperSourceGenerator.point,
      sm2UpperNegativeUnit, A, B] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel)
        (u := generator.real)
        (v := generator.ordinate)
        (n := m)
        generator.negative_equation)
  have hnegative :
      A ^ 2 + 1 = data.upperKernel * B ^ 2 := by
    simpa [A, B] using
      (sm2LucasReal_odd_negative_equation
        (K := data.upperKernel)
        (u := generator.real)
        (v := generator.ordinate)
        (n := m)
        generator.negative_equation hmOdd)
  have hkernel : data.upperKernel ∣ B := by
    exact generator.kernel_dvd_ordinate.trans
      (by
        simp only [B]
        exact dvd_mul_right generator.ordinate
          (sm2LucasCoeff generator.real m))
  have hsource :
      sm2UpperSourcePoint data.upperKernel data.center
          (data.upperKernel * data.upperSquarePart) =
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 := by
    calc
      sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          generator.point ^ (2 * generator.outerIndex + 1) := by
            simpa [Sm2LowerSquareUpperSourceGenerator.point] using
              generator.source_power
      _ = generator.point ^ (m * 17) := by rw [hmFactor]
      _ = (generator.point ^ m) ^ 17 := by rw [pow_mul]
      _ = (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 := by
            rw [hcoords]
  have hpowerCoordinates :
      (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 =
        (⟨sm2LucasReal A 17,
            B * sm2LucasCoeff A 17⟩ :
          ℤ√(data.upperKernel : Int)) := by
    simpa [sm2UpperNegativeUnit] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel)
        (u := A)
        (v := B)
        (n := 17)
        hnegative)
  have hrealInt := congrArg Zsqrtd.re hsource
  rw [hpowerCoordinates] at hrealInt
  have hrealCenter :
      sm2LucasReal A 17 = data.center := by
    exact_mod_cast
      (by
        simpa [sm2UpperSourcePoint] using hrealInt.symm :
          (sm2LucasReal A 17 : Int) = data.center)
  have hreal :
      sm2LucasReal A 17 = allocation.y ^ 2 + 1 :=
    hrealCenter.trans allocation.center_eq
  have hsuccessor :
      SquareCubeNormalForm
        (sm2LucasReal A 17 + 1)
        allocation.linearUpperSquarePart data.pell.D := by
    rw [hreal]
    simpa using allocation.linearUpperNormalForm
  exact
    ⟨m, A, B, hmPos, hmOdd, hmEight, hAEight, hmFactor,
      rfl, hcoords, hnegative, hkernel, hsource, hreal, hsuccessor⟩

/-- Complete public arithmetic profile of a retained outer `17`-block.
The seven classes and support exclusions are necessary source conditions;
they do not exclude the block. -/
theorem seventeen_outer_block_profile
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (h17 : 17 ∣ 2 * generator.outerIndex + 1) :
    ∃ m A B : Nat,
      0 < m ∧
        Odd m ∧
        m % 8 = 1 ∧
        A % 8 = 2 ∧
        (A % 9 = 4 ∨ A % 9 = 5) ∧
        (2 * A ^ 2 + 1) % 576 = 393 ∧
        (A % 17 = 0 ∨ A % 17 = 2 ∨ A % 17 = 3 ∨
          A % 17 = 5 ∨ A % 17 = 9 ∨ A % 17 = 10 ∨
            A % 17 = 14) ∧
        2 * generator.outerIndex + 1 = m * 17 ∧
        B =
          generator.ordinate *
            sm2LucasCoeff generator.real m ∧
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A ^ 2 + 1 = data.upperKernel * B ^ 2 ∧
        data.upperKernel ∣ B ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 ∧
        sm2LucasReal A 17 = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A 17 + 1)
          allocation.linearUpperSquarePart data.pell.D ∧
        ¬ 17 ∣ data.pell.D ∧
        ¬ 17 ∣ data.upperKernel ∧
        ¬ 17 ∣
          pellRank data.upperKernel allocation.upper_pellKernel ∧
        ¬ 17 ∣ allocation.y ∧
        ¬ 17 ∣ allocation.linearUpperSquarePart ∧
        ¬ 17 ∣ generator.ordinate ∧
        ¬ 17 ∣ B ∧
        ¬ 17 ∣ data.upperSquarePart := by
  obtain
      ⟨m, A, B, hmPos, hmOdd, hmEight, hAEight, hmFactor,
        hBdef, hcoords, hnegative, hkernel, hsource,
        hreal, hsuccessor⟩ :=
    generator.exists_seventeen_outer_block_of_dvd_outer_exponent h17
  have hclasses :=
    sm2LucasReal_seventeen_admissible_classes hreal hsuccessor
  have hrealCenter :
      sm2LucasReal A 17 = data.center :=
    hreal.trans allocation.center_eq.symm
  have hcenterSqModNine : data.center ^ 2 % 9 = 1 := by
    have hThirtySix := allocation.middle_mod_thirtySix
    have hmod :=
      Nat.mod_mod_of_dvd (data.center ^ 2)
        (by decide : 9 ∣ 36)
    rw [hThirtySix] at hmod
    omega
  have hcenterSqCast :
      (data.center : ZMod 9) ^ 2 = 1 := by
    have hcast :=
      (ZMod.natCast_eq_natCast_iff'
        (data.center ^ 2) 1 9).mpr hcenterSqModNine
    simpa using hcast
  have hrealCenterCast :=
    congrArg (fun n : Nat => (n : ZMod 9)) hrealCenter
  rw [sm2LucasReal_cast] at hrealCenterCast
  have hFsq :
      sm2LucasRealMod 9 (A : ZMod 9) 17 ^ 2 = 1 := by
    rw [hrealCenterCast]
    exact hcenterSqCast
  have hAcastNine :=
    sm2LucasReal_seventeen_sq_one_mod_nine
      (A : ZMod 9) hFsq
  have hANine : A % 9 = 4 ∨ A % 9 = 5 := by
    rcases hAcastNine with hA | hA
    · left
      exact (ZMod.natCast_eq_natCast_iff' A 4 9).mp hA
    · right
      exact (ZMod.natCast_eq_natCast_iff' A 5 9).mp hA
  have hphase64 : (2 * A ^ 2 + 1) % 64 = 9 := by
    have hAform : A = 8 * (A / 8) + 2 := by
      have hdecomp := (Nat.mod_add_div A 8).symm
      rw [hAEight] at hdecomp
      omega
    apply
      (ZMod.natCast_eq_natCast_iff'
        (2 * A ^ 2 + 1) 9 64).mp
    rw [hAform]
    push_cast
    ring_nf
    rw [show (64 : ZMod 64) = 0 by decide,
      show (128 : ZMod 64) = 0 by decide]
    ring
  have hphaseNine : (2 * A ^ 2 + 1) % 9 = 6 := by
    rcases hANine with hA | hA
    · have hAform : A = 9 * (A / 9) + 4 := by
        have hdecomp := (Nat.mod_add_div A 9).symm
        rw [hA] at hdecomp
        omega
      apply
        (ZMod.natCast_eq_natCast_iff'
          (2 * A ^ 2 + 1) 6 9).mp
      rw [hAform]
      push_cast
      ring_nf
      rw [show (33 : ZMod 9) = 6 by decide,
        show (144 : ZMod 9) = 0 by decide,
        show (162 : ZMod 9) = 0 by decide]
      ring
    · have hAform : A = 9 * (A / 9) + 5 := by
        have hdecomp := (Nat.mod_add_div A 9).symm
        rw [hA] at hdecomp
        omega
      apply
        (ZMod.natCast_eq_natCast_iff'
          (2 * A ^ 2 + 1) 6 9).mp
      rw [hAform]
      push_cast
      ring_nf
      rw [show (51 : ZMod 9) = 6 by decide,
        show (180 : ZMod 9) = 0 by decide,
        show (162 : ZMod 9) = 0 by decide]
      ring
  have hphase : (2 * A ^ 2 + 1) % 576 = 393 := by
    have hmod64 :
        (2 * A ^ 2 + 1) % 576 % 64 = 9 := by
      rw [Nat.mod_mod_of_dvd
        (2 * A ^ 2 + 1) (by decide : 64 ∣ 576)]
      exact hphase64
    have hmod9 :
        (2 * A ^ 2 + 1) % 576 % 9 = 6 := by
      rw [Nat.mod_mod_of_dvd
        (2 * A ^ 2 + 1) (by decide : 9 ∣ 576)]
      exact hphaseNine
    have hlt :
        (2 * A ^ 2 + 1) % 576 < 576 :=
      Nat.mod_lt _ (by decide)
    omega
  have hAmodNeOne : A % 17 ≠ 1 := by
    rcases hclasses with hA | hA | hA | hA | hA | hA | hA <;>
      omega
  have hAmodNeMinusOne : A % 17 ≠ 16 := by
    rcases hclasses with hA | hA | hA | hA | hA | hA | hA <;>
      omega
  have hAmodNeFour : A % 17 ≠ 4 := by
    rcases hclasses with hA | hA | hA | hA | hA | hA | hA <;>
      omega
  have hAmodNeThirteen : A % 17 ≠ 13 := by
    rcases hclasses with hA | hA | hA | hA | hA | hA | hA <;>
      omega
  have hpredecessorCast :=
    congrArg (fun n : Nat => (n : ZMod 17)) hreal
  push_cast at hpredecessorCast
  rw [sm2LucasReal_cast,
    sm2LucasReal_seventeen_mod_seventeen] at hpredecessorCast
  have hAmodPredecessor :
      A % 17 = (allocation.y ^ 2 + 1) % 17 := by
    apply
      (ZMod.natCast_eq_natCast_iff'
        A (allocation.y ^ 2 + 1) 17).mp
    simpa using hpredecessorCast
  have hD : ¬ 17 ∣ data.pell.D :=
    generator.seventeen_not_dvd_lowerKernel_of_dvd_outer_exponent h17
  have hK : ¬ 17 ∣ data.upperKernel :=
    generator.seventeen_not_dvd_upperKernel
  have hR :
      ¬ 17 ∣
        pellRank data.upperKernel allocation.upper_pellKernel := by
    intro h17R
    exact hK
      (h17R.trans
        (pellRank_dvd_kernel
          data.upperKernel allocation.upper_pellKernel))
  have hy : ¬ 17 ∣ allocation.y := by
    intro h17y
    have hymod : allocation.y % 17 = 0 :=
      Nat.mod_eq_zero_of_dvd h17y
    rw [Nat.add_mod, Nat.pow_mod, hymod] at hAmodPredecessor
    norm_num at hAmodPredecessor
    exact hAmodNeOne hAmodPredecessor
  have hz : ¬ 17 ∣ allocation.linearUpperSquarePart := by
    intro h17z
    have hzCast :
        (allocation.linearUpperSquarePart : ZMod 17) = 0 :=
      (ZMod.natCast_eq_zero_iff
        allocation.linearUpperSquarePart 17).mpr h17z
    have hvalueCast :=
      congrArg (fun n : Nat => (n : ZMod 17))
        hsuccessor.2.2.1
    push_cast at hvalueCast
    rw [sm2LucasReal_cast,
      sm2LucasReal_seventeen_mod_seventeen,
      hzCast] at hvalueCast
    simp at hvalueCast
    have hAcast : (A : ZMod 17) = 16 := by
      calc
        (A : ZMod 17) = -1 :=
          eq_neg_of_add_eq_zero_left hvalueCast
        _ = 16 := by decide
    exact hAmodNeMinusOne
      ((ZMod.natCast_eq_natCast_iff' A 16 17).mp hAcast)
  have hB : ¬ 17 ∣ B := by
    intro h17B
    have hBCast : (B : ZMod 17) = 0 :=
      (ZMod.natCast_eq_zero_iff B 17).mpr h17B
    have hnegativeCast :=
      congrArg (fun n : Nat => (n : ZMod 17)) hnegative
    push_cast at hnegativeCast
    rw [hBCast] at hnegativeCast
    have hASq : (A : ZMod 17) ^ 2 = -1 :=
      eq_neg_of_add_eq_zero_left (by simpa using hnegativeCast)
    rcases square_eq_neg_one_classes_mod_seventeen
        (A : ZMod 17) hASq with hA | hA
    · exact hAmodNeFour
        ((ZMod.natCast_eq_natCast_iff' A 4 17).mp hA)
    · exact hAmodNeThirteen
        ((ZMod.natCast_eq_natCast_iff' A 13 17).mp hA)
  have hQ : ¬ 17 ∣ generator.ordinate := by
    intro h17Q
    apply hB
    rw [hBdef]
    exact dvd_mul_of_dvd_left h17Q
      (sm2LucasCoeff generator.real m)
  have hV : ¬ 17 ∣ data.upperSquarePart := by
    intro h17V
    have hVCast : (data.upperSquarePart : ZMod 17) = 0 :=
      (ZMod.natCast_eq_zero_iff
        data.upperSquarePart 17).mpr h17V
    have hupperCast :=
      congrArg (fun n : Nat => (n : ZMod 17))
        data.upper_negativePell.equation.symm
    push_cast at hupperCast
    rw [hVCast] at hupperCast
    have hcenterSq : (data.center : ZMod 17) ^ 2 = -1 :=
      eq_neg_of_add_eq_zero_left (by simpa using hupperCast)
    have hrealCenterCast17 :=
      congrArg (fun n : Nat => (n : ZMod 17)) hrealCenter
    rw [sm2LucasReal_cast,
      sm2LucasReal_seventeen_mod_seventeen] at hrealCenterCast17
    have hASq : (A : ZMod 17) ^ 2 = -1 := by
      rw [hrealCenterCast17]
      exact hcenterSq
    rcases square_eq_neg_one_classes_mod_seventeen
        (A : ZMod 17) hASq with hA | hA
    · exact hAmodNeFour
        ((ZMod.natCast_eq_natCast_iff' A 4 17).mp hA)
    · exact hAmodNeThirteen
        ((ZMod.natCast_eq_natCast_iff' A 13 17).mp hA)
  exact
    ⟨m, A, B, hmPos, hmOdd, hmEight, hAEight, hANine,
      hphase, hclasses, hmFactor, hBdef, hcoords, hnegative,
      hkernel, hsource, hreal, hsuccessor, hD, hK, hR,
      hy, hz, hQ, hB, hV⟩

/-- The distinguished outer branch: the source has nontrivial outer depth
and its exact outer exponent is divisible by `17`. -/
def OuterSeventeenBranch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.outerIndex ≠ 0 ∧
    17 ∣ 2 * generator.outerIndex + 1

/-- The complementary outer branch.  The negative `17` tag is retained
because a large selected prime does not by itself exclude `17` from the
complementary factor of the outer exponent. -/
def OuterLargeBranch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.outerIndex ≠ 0 ∧
    ¬ 17 ∣ 2 * generator.outerIndex + 1

/-- The first outer phase with nontrivial exact Pell rank. -/
def RankDefectBranch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.outerIndex = 0 ∧
    1 <
      pellRank data.upperKernel allocation.upper_pellKernel

/-- The atomic source phase: the outer exponent and exact Pell rank are
both one. -/
def AtomicBranch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.outerIndex = 0 ∧
    pellRank data.upperKernel allocation.upper_pellKernel = 1

/-- Complete arithmetic packet for the priority outer `17` branch. -/
def OuterSeventeenPacket
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.OuterSeventeenBranch ∧
    ∃ m A B : Nat,
      0 < m ∧
        Odd m ∧
        m % 8 = 1 ∧
        A % 8 = 2 ∧
        (A % 9 = 4 ∨ A % 9 = 5) ∧
        (2 * A ^ 2 + 1) % 576 = 393 ∧
        (A % 17 = 0 ∨ A % 17 = 2 ∨ A % 17 = 3 ∨
          A % 17 = 5 ∨ A % 17 = 9 ∨ A % 17 = 10 ∨
            A % 17 = 14) ∧
        2 * generator.outerIndex + 1 = m * 17 ∧
        B =
          generator.ordinate *
            sm2LucasCoeff generator.real m ∧
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A ^ 2 + 1 = data.upperKernel * B ^ 2 ∧
        data.upperKernel ∣ B ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 ∧
        sm2LucasReal A 17 = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A 17 + 1)
          allocation.linearUpperSquarePart data.pell.D ∧
        ¬ 17 ∣ data.pell.D ∧
        ¬ 17 ∣ data.upperKernel ∧
        ¬ 17 ∣
          pellRank data.upperKernel allocation.upper_pellKernel ∧
        ¬ 17 ∣ allocation.y ∧
        ¬ 17 ∣ allocation.linearUpperSquarePart ∧
        ¬ 17 ∣ generator.ordinate ∧
        ¬ 17 ∣ B ∧
        ¬ 17 ∣ data.upperSquarePart

/-- The outer-`17` packet has an exact scalar/depth reduction.  Writing
`B = K*c`, its source ordinate identity cancels one positive factor of
`K` and gives `V = c*U_17(A)`.  The remaining Lucas factor is coprime to
`K`, so the source square part has exactly the same GCD with `K` as `c`.
This is a reduction of the packet, not an exclusion of the branch. -/
theorem outerSeventeenPacket_scalar_reduction
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (packet : generator.OuterSeventeenPacket) :
    ∃ m A B c : Nat,
      0 < m ∧
        Odd m ∧
        2 * generator.outerIndex + 1 = m * 17 ∧
        B = data.upperKernel * c ∧
        A ^ 2 + 1 =
          data.upperKernel ^ 3 * c ^ 2 ∧
        data.upperSquarePart =
          c * sm2LucasCoeff A 17 ∧
        data.upperKernel.Coprime
          (sm2LucasCoeff A 17) ∧
        data.upperKernel.gcd
          data.upperSquarePart =
            data.upperKernel.gcd c := by
  rcases packet.2 with
    ⟨m, A, B, hmPos, hmOdd, hmEight, hAEight, hANine,
      hphase, hclasses, hmFactor, hBdef, hcoords, hnegative,
      hkernel, hsource, hreal, hsuccessor, hD17, hK17,
      hR17, hy17, hz17, hQ17, hB17, hV17⟩
  obtain ⟨c, hBc⟩ := hkernel
  have hcubic :
      A ^ 2 + 1 =
        data.upperKernel ^ 3 * c ^ 2 := by
    calc
      A ^ 2 + 1 = data.upperKernel * B ^ 2 := hnegative
      _ = data.upperKernel ^ 3 * c ^ 2 := by
        rw [hBc]
        ring
  have hpowerCoordinates :
      (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 17 =
        (⟨sm2LucasReal A 17,
            B * sm2LucasCoeff A 17⟩ :
          ℤ√(data.upperKernel : Int)) := by
    simpa [sm2UpperNegativeUnit] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel) (u := A) (v := B) (n := 17)
        hnegative)
  have himagInt := congrArg Zsqrtd.im hsource
  rw [hpowerCoordinates] at himagInt
  have himag :
      data.upperKernel * data.upperSquarePart =
        B * sm2LucasCoeff A 17 := by
    exact_mod_cast
      (by
        simpa [sm2UpperSourcePoint] using himagInt :
          (data.upperKernel * data.upperSquarePart : Int) =
            (B * sm2LucasCoeff A 17 : Nat))
  have hscalar :
      data.upperSquarePart =
        c * sm2LucasCoeff A 17 := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.zero_lt_of_lt allocation.upper_pellKernel.1)
    calc
      data.upperKernel * data.upperSquarePart =
          B * sm2LucasCoeff A 17 := himag
      _ =
          data.upperKernel *
            (c * sm2LucasCoeff A 17) := by
              rw [hBc]
              ring
  have hcoprime :
      data.upperKernel.Coprime
        (sm2LucasCoeff A 17) := by
    rw [Nat.coprime_iff_gcd_eq_one,
      gcd_sm2LucasCoeff_eq_gcd_index hnegative dvd_rfl]
    exact
      (((by norm_num : Nat.Prime 17).coprime_iff_not_dvd).mpr
        hK17).symm.gcd_eq_one
  have hgcd :
      data.upperKernel.gcd
          data.upperSquarePart =
        data.upperKernel.gcd c := by
    rw [hscalar]
    simpa [mul_comm] using
      hcoprime.symm.gcd_mul_left_cancel_right c
  exact
    ⟨m, A, B, c, hmPos, hmOdd, hmFactor, hBc, hcubic,
      hscalar, hcoprime, hgcd⟩

/-- Complete arithmetic packet for the priority non-`17` outer branch. -/
def OuterLargePacket
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.OuterLargeBranch ∧
    ∃ p m A B : Nat,
      p.Prime ∧
        p % 8 = 1 ∧
        41 ≤ p ∧
        0 < m ∧
        Odd m ∧
        2 * generator.outerIndex + 1 = m * p ∧
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A ^ 2 + 1 = data.upperKernel * B ^ 2 ∧
        data.upperKernel ∣ B ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p ∧
        sm2LucasReal A p = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A p + 1)
          allocation.linearUpperSquarePart data.pell.D

/-- Complete arithmetic packet for a one-prime-defect rank branch. -/
def RankDefectPacket
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.RankDefectBranch ∧
    ∃ p n A B c : Nat,
      p.Prime ∧
        p % 8 = 1 ∧
        41 ≤ p ∧
        0 < n ∧
        Odd n ∧
        pellRank data.upperKernel allocation.upper_pellKernel =
          n * p ∧
        sm2UpperNegativeUnit data.upperKernel
            generator.upperOrbit.rootX generator.upperOrbit.rootY ^ n =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        B = (data.upperKernel / p) * c ∧
        data.upperKernel.gcd B = data.upperKernel / p ∧
        A ^ 2 + 1 =
          p * (data.upperKernel / p) ^ 3 * c ^ 2 ∧
        ¬ p ∣ c ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ p ∧
        sm2LucasReal A p = allocation.y ^ 2 + 1 ∧
        SquareCubeNormalForm
          (sm2LucasReal A p + 1)
          allocation.linearUpperSquarePart data.pell.D ∧
        c * sm2LucasCoeff A p =
          p * data.upperSquarePart

/-- Exact repair of the missing prime depth in a rank-defect packet.
The normalized Lucas ordinate acquires `p` exactly once; after cancelling
that factor in the retained source ordinate identity, the source square
part is prime-to-`p` and retains the scalar residue `c`.  This does not
exclude the rank-defect branch. -/
theorem rankDefectPacket_exact_repair
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (packet : generator.RankDefectPacket) :
    ∃ p n A B c q : Nat,
      p.Prime ∧
        p % 8 = 1 ∧
        41 ≤ p ∧
        0 < n ∧
        Odd n ∧
        pellRank data.upperKernel allocation.upper_pellKernel =
          n * p ∧
        B = (data.upperKernel / p) * c ∧
        A ^ 2 + 1 =
          p * (data.upperKernel / p) ^ 3 * c ^ 2 ∧
        ¬ p ∣ c ∧
        sm2LucasCoeff A p = p * q ∧
        q % p = 1 ∧
        data.upperSquarePart = c * q ∧
        ¬ p ∣ q ∧
        ¬ p ∣ data.upperSquarePart ∧
        data.upperSquarePart % p = c % p := by
  rcases packet.2 with
    ⟨p, n, A, B, c, hp, hpEight, hpFortyOne, hnPos,
      hnOdd, hRank, hcoords, hB, hGcd, hdefect,
      hpNotDvdC, hsource, hreal, hsuccessor, hrepair⟩
  have hpFive : 5 ≤ p := by omega
  have hpDvd :
      p ∣ A ^ 2 + 1 :=
    ⟨(data.upperKernel / p) ^ 3 * c ^ 2,
      by simpa [mul_assoc] using hdefect⟩
  have hmod :
      sm2LucasCoeff A p ≡ p [MOD p ^ 2] :=
    sm2LucasCoeff_mod_prime_sq hp hpFive hpDvd
  have hmodP :
      sm2LucasCoeff A p ≡ p [MOD p] := by
    apply hmod.of_dvd
    exact ⟨p, by simp [pow_two]⟩
  have hpCoeff :
      p ∣ sm2LucasCoeff A p := by
    apply Nat.modEq_zero_iff_dvd.mp
    exact hmodP.trans (by simp)
  obtain ⟨q, hCoeff⟩ := hpCoeff
  have hqCongruence :
      q ≡ 1 [MOD p] := by
    apply Nat.ModEq.mul_left_cancel' hp.ne_zero
    rw [hCoeff] at hmod
    simpa [pow_two] using hmod
  have hqMod : q % p = 1 := by
    change q % p = 1 % p at hqCongruence
    simpa [Nat.mod_eq_of_lt hp.one_lt] using hqCongruence
  have hsourcePart :
      data.upperSquarePart = c * q := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * data.upperSquarePart =
          c * sm2LucasCoeff A p := hrepair.symm
      _ = p * (c * q) := by
        rw [hCoeff]
        ring
  have hpNotDvdQ : ¬ p ∣ q := by
    intro hpq
    have hzero := Nat.mod_eq_zero_of_dvd hpq
    rw [hqMod] at hzero
    omega
  have hpNotDvdSourcePart :
      ¬ p ∣ data.upperSquarePart := by
    intro hpV
    rw [hsourcePart] at hpV
    rcases hp.dvd_mul.mp hpV with hpc | hpq
    · exact hpNotDvdC hpc
    · exact hpNotDvdQ hpq
  have hsourcePartMod :
      data.upperSquarePart % p = c % p := by
    rw [hsourcePart, Nat.mul_mod, hqMod]
    simp
  exact
    ⟨p, n, A, B, c, q, hp, hpEight, hpFortyOne,
      hnPos, hnOdd, hRank, hB, hdefect, hpNotDvdC,
      hCoeff, hqMod, hsourcePart, hpNotDvdQ,
      hpNotDvdSourcePart, hsourcePartMod⟩

/-- Complete arithmetic packet for the atomic branch.  Rank and outer
depth are both one, so the selected fundamental norm-minus-one root is
literally the retained source point. -/
def AtomicPacket
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) : Prop :=
  generator.AtomicBranch ∧
    sm2UpperNegativeUnit data.upperKernel
        generator.upperOrbit.rootX generator.upperOrbit.rootY =
      generator.point ∧
    sm2UpperSourcePoint data.upperKernel data.center
        (data.upperKernel * data.upperSquarePart) =
      generator.point ∧
    generator.real = data.center ∧
    generator.ordinate =
      data.upperKernel * data.upperSquarePart ∧
    generator.real = allocation.y ^ 2 + 1 ∧
    generator.real ^ 2 + 1 =
      data.upperKernel * generator.ordinate ^ 2 ∧
    fundamentalX data.upperKernel allocation.upper_pellKernel =
      2 * generator.real ^ 2 + 1 ∧
    fundamentalY data.upperKernel allocation.upper_pellKernel =
      2 * generator.real * generator.ordinate ∧
    SquareCubeNormalForm
      (generator.real + 1)
      allocation.linearUpperSquarePart data.pell.D

/-- Exhaustive, pairwise-discriminated routing of every exact typed
generator into the four remaining arithmetic worlds. -/
theorem branch_cases
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation) :
    generator.OuterSeventeenBranch ∨
      generator.OuterLargeBranch ∨
      generator.RankDefectBranch ∨
      generator.AtomicBranch := by
  by_cases hzero : generator.outerIndex = 0
  · by_cases hR :
      pellRank data.upperKernel allocation.upper_pellKernel = 1
    · exact Or.inr (Or.inr (Or.inr ⟨hzero, hR⟩))
    · have hRPos :
          0 <
            pellRank data.upperKernel
              allocation.upper_pellKernel :=
        pellRank_pos data.upperKernel allocation.upper_pellKernel
      have hRgt :
          1 <
            pellRank data.upperKernel
              allocation.upper_pellKernel := by
        omega
      exact Or.inr (Or.inr (Or.inl ⟨hzero, hRgt⟩))
  · by_cases h17 :
      17 ∣ 2 * generator.outerIndex + 1
    · exact Or.inl ⟨hzero, h17⟩
    · exact Or.inr (Or.inl ⟨hzero, h17⟩)

/-- Materialize the exact public `17` profile from its priority branch. -/
theorem outerSeventeenPacket_of_branch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hbranch : generator.OuterSeventeenBranch) :
    generator.OuterSeventeenPacket := by
  refine ⟨hbranch, ?_⟩
  exact generator.seventeen_outer_block_profile hbranch.2

/-- Materialize the exact full-depth large-prime block from its priority
branch. -/
theorem outerLargePacket_of_branch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hbranch : generator.OuterLargeBranch) :
    generator.OuterLargePacket := by
  refine ⟨hbranch, ?_⟩
  exact
    generator.exists_outer_large_prime_block
      hbranch.1 hbranch.2

/-- Materialize the exact one-prime-defect block from its rank branch. -/
theorem rankDefectPacket_of_branch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hbranch : generator.RankDefectBranch) :
    generator.RankDefectPacket := by
  refine ⟨hbranch, ?_⟩
  exact
    generator.exists_rank_prime_defect_block
      hbranch.1 hbranch.2

/-- Materialize the exact fundamental-source packet from the atomic
branch. -/
theorem atomicPacket_of_branch
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hbranch : generator.AtomicBranch) :
    generator.AtomicPacket := by
  have hshell :=
    generator.first_outer_source_shell hbranch.1
  have hpower := generator.generator_power
  rw [hbranch.2] at hpower
  simp only [pow_one] at hpower
  have hroot :
      sm2UpperNegativeUnit data.upperKernel
          generator.upperOrbit.rootX generator.upperOrbit.rootY =
        generator.point := by
    simpa [Sm2LowerSquareUpperSourceGenerator.point] using hpower
  have hsource :
      sm2UpperSourcePoint data.upperKernel data.center
          (data.upperKernel * data.upperSquarePart) =
        generator.point := by
    simpa [hbranch.1,
      Sm2LowerSquareUpperSourceGenerator.point] using
      generator.source_power
  have hrootXInt := congrArg Zsqrtd.re hpower
  have hrootYInt := congrArg Zsqrtd.im hpower
  have hrootX :
      generator.upperOrbit.rootX = generator.real := by
    exact_mod_cast
      (by
        simpa [sm2UpperNegativeUnit] using hrootXInt :
          (generator.upperOrbit.rootX : Int) = generator.real)
  have hrootY :
      generator.upperOrbit.rootY = generator.ordinate := by
    exact_mod_cast
      (by
        simpa [sm2UpperNegativeUnit] using hrootYInt :
          (generator.upperOrbit.rootY : Int) = generator.ordinate)
  have hfundX :
      fundamentalX data.upperKernel allocation.upper_pellKernel =
        2 * generator.real ^ 2 + 1 := by
    calc
      fundamentalX data.upperKernel allocation.upper_pellKernel =
          2 * generator.upperOrbit.rootX ^ 2 + 1 :=
        generator.upperOrbit.fundamentalX_eq
      _ = 2 * generator.real ^ 2 + 1 := by rw [hrootX]
  have hfundY :
      fundamentalY data.upperKernel allocation.upper_pellKernel =
        2 * generator.real * generator.ordinate := by
    calc
      fundamentalY data.upperKernel allocation.upper_pellKernel =
          2 * generator.upperOrbit.rootX *
            generator.upperOrbit.rootY :=
        generator.upperOrbit.fundamentalY_eq
      _ = 2 * generator.real * generator.ordinate := by
        rw [hrootX, hrootY]
  refine
    ⟨hbranch, hroot, hsource, hshell.1, hshell.2.1,
      hshell.2.2.1, generator.negative_equation,
      hfundX, hfundY, hshell.2.2.2⟩

end Sm2LowerSquareUpperSourceGenerator

/-- Arithmetic impossibility of every complete priority outer `17`
packet. -/
def NoSm2OuterSeventeenBlocks : Prop :=
  ∀ {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation),
    ¬ generator.OuterSeventeenPacket

/-- Arithmetic impossibility of every complete priority non-`17`
full-depth outer packet. -/
def NoSm2OuterLargeBlocks : Prop :=
  ∀ {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation),
    ¬ generator.OuterLargePacket

/-- Arithmetic impossibility of every complete one-prime-defect packet. -/
def NoSm2RankDefectBlocks : Prop :=
  ∀ {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation),
    ¬ generator.RankDefectPacket

/-- Arithmetic impossibility of every complete rank-one atomic packet. -/
def NoSm2AtomicResiduals : Prop :=
  ∀ {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation),
    ¬ generator.AtomicPacket

/-- Exact conditional assembly theorem for the complete
`sm2LowerSquare` leaf.  Once the four explicitly named arithmetic
obligations are proved, the maintained source compiler has no remaining
case.

Unlike a bare branch-emptiness case split, this bridge materializes and
passes each complete arithmetic packet to the corresponding obstruction
hypothesis.  It does not prove any of those four hypotheses. -/
theorem no_sm2LowerSquareSource_of_terminal_closures
    (hOuter17 : NoSm2OuterSeventeenBlocks)
    (hOuterLarge : NoSm2OuterLargeBlocks)
    (hRankDefect : NoSm2RankDefectBlocks)
    (hAtomic : NoSm2AtomicResiduals)
    (X : Nat) :
    ¬ Sm2LowerSquareSource X := by
  intro hsource
  obtain ⟨data, _hrep, ⟨residual⟩⟩ :=
    (sm2LowerSquareSource_iff_exists_generatorResidual X).mp hsource
  obtain ⟨generator⟩ := residual.upperGenerator
  rcases generator.branch_cases with
    h17 | hlarge | hrank | hatomic
  · exact
      hOuter17 generator
        (generator.outerSeventeenPacket_of_branch h17)
  · exact
      hOuterLarge generator
        (generator.outerLargePacket_of_branch hlarge)
  · exact
      hRankDefect generator
        (generator.rankDefectPacket_of_branch hrank)
  · exact
      hAtomic generator
        (generator.atomicPacket_of_branch hatomic)

namespace Sm2LowerSquareAllocation

/-- The source-equivalent trace-depth triple attached to this leaf has
trivial shared radicand kernel, shared ordinate GCD exactly twice the centre,
and therefore a square one below its recovered half-GCD.

This is the exact `sm2LowerSquare` image inside the global trace-depth
representation.  It is a reconstruction theorem, not a trace-gap
obstruction. -/
theorem exists_traceDepth_square_sharedGCD
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    ∃ trace : TraceDepthTripleData (data.center ^ 2 - 1),
      trace.sharedRadicandGCD = 1 ∧
        trace.sharedOrdinateGCD = 2 * data.center ∧
        trace.sharedOrdinateGCD / 2 - 1 = allocation.y ^ 2 := by
  have hmiddleIndex :
      data.center ^ 2 - 1 + 1 = data.center ^ 2 := by
    exact Nat.sub_add_cancel
      (by nlinarith [data.center_one_lt] :
        1 ≤ data.center ^ 2)
  have hrightIndex :
      data.center ^ 2 - 1 + 2 = data.center ^ 2 + 1 := by
    omega
  have hmiddle :
      SquareCubeNormalForm
        (data.center ^ 2 - 1 + 1) data.center 1 := by
    apply squareCubeNormalForm_of_eq_sq_mul_cube
    · exact Nat.zero_lt_of_lt data.center_one_lt
    · decide
    · rw [hmiddleIndex]
      ring
    · simp
  have hright :
      SquareCubeNormalForm
        (data.center ^ 2 - 1 + 2)
        data.upperSquarePart data.upperKernel := by
    rw [hrightIndex]
    exact data.upperNormalForm
  let state : TripleNormalFormAt (data.center ^ 2 - 1) :=
    { a0 := data.lowerSquarePart
      b0 := data.pell.D
      a1 := data.center
      b1 := 1
      a2 := data.upperSquarePart
      b2 := data.upperKernel
      form0 := data.lowerNormalForm
      form1 := hmiddle
      form2 := hright }
  let trace : TraceDepthTripleData (data.center ^ 2 - 1) :=
    { left :=
        adjacentTraceDepthData_of_normalForms
          state.form0 state.form1
      right :=
        adjacentTraceDepthData_of_normalForms
          state.form1 (by
            simpa [Nat.add_assoc] using state.form2) }
  have hgcds := trace.sharedGCDs_eq_middleComponents state
  have hradicand : trace.sharedRadicandGCD = 1 := by
    simpa [state] using hgcds.1
  have hordinate :
      trace.sharedOrdinateGCD = 2 * data.center := by
    simpa [state] using hgcds.2
  refine ⟨trace, hradicand, hordinate, ?_⟩
  rw [hordinate]
  have hhalf : 2 * data.center / 2 = data.center := by
    omega
  rw [hhalf, allocation.center_eq]
  omega

/-- Under the explicit Cohn quartic-Pell classification, the exact
`sm2LowerSquare` allocation forces its combined discriminant to have a
nested-square fundamental real coordinate, a fundamental ordinate divisible
by the complete discriminant, and therefore Pell divisibility rank one.

This is the exact leaf-specific quartic target.  It is conditional on
`hCohn` and does not prove that the displayed fundamental-unit configuration
is impossible. -/
theorem exists_combined_nested_square_rank_one_of_cohn
    (hCohn : CohnQuarticPellClassification)
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    ∃ hM : PellKernel (data.pell.D * data.upperKernel),
      fundamentalX (data.pell.D * data.upperKernel) hM =
          (allocation.y ^ 2 + 1) ^ 2 ∧
        data.pell.D * data.upperKernel ∣
          fundamentalY (data.pell.D * data.upperKernel) hM ∧
        pellRank (data.pell.D * data.upperKernel) hM = 1 := by
  let M := data.pell.D * data.upperKernel
  let Y :=
    M * (data.lowerSquarePart * data.upperSquarePart)
  have hquartic :
      DivisibleNatQuarticPell M data.center Y := by
    simpa [M, Y] using data.toDivisibleNatQuarticPell
  let hM : PellKernel M :=
    ⟨hquartic.M_one_lt, hquartic.M_squarefree⟩
  have hx :
      data.center ^ 2 = fundamentalX M hM := by
    simpa [hM] using
      even_quarticPell_is_fundamental hCohn hquartic
  have hnested :
      fundamentalX M hM = (allocation.y ^ 2 + 1) ^ 2 := by
    calc
      fundamentalX M hM = data.center ^ 2 := hx.symm
      _ = (allocation.y ^ 2 + 1) ^ 2 := by
        rw [allocation.center_eq]
  have hquarticFund :
      fundamentalX M hM ^ 2 = M * Y ^ 2 + 1 := by
    calc
      fundamentalX M hM ^ 2 = (data.center ^ 2) ^ 2 := by
        rw [hx]
      _ = data.center ^ 4 := by ring
      _ = M * Y ^ 2 + 1 := hquartic.equation
  have hfundSub := fundamental_pell_equation M hM
  have hfund :
      fundamentalX M hM ^ 2 =
        M * fundamentalY M hM ^ 2 + 1 := by
    omega
  have hproducts :
      M * Y ^ 2 = M * fundamentalY M hM ^ 2 := by
    omega
  have hsquares :
      Y ^ 2 = fundamentalY M hM ^ 2 :=
    Nat.eq_of_mul_eq_mul_left
      (Nat.zero_lt_of_lt hquartic.M_one_lt) hproducts
  have hy : Y = fundamentalY M hM :=
    Nat.pow_left_injective (by decide : (2 : Nat) ≠ 0) hsquares
  have hdiv : M ∣ fundamentalY M hM := by
    rw [← hy]
    exact hquartic.M_dvd_Y
  have hrank : pellRank M hM = 1 := by
    rw [pellRank, Nat.gcd_eq_left_iff_dvd.mpr hdiv]
    exact Nat.div_self
      (Nat.zero_lt_of_lt hquartic.M_one_lt)
  exact ⟨hM, hnested, hdiv, hrank⟩

/-- On the atomic branch, the Cohn-conditional combined fundamental unit
retains its exact ordinate as well as its nested-square real coordinate.
The atomic upper fundamental unit is then coupled to the combined unit in
both coordinates.

This is an exact source-facing profile.  It does not assert that such a
profile is impossible. -/
theorem exists_atomic_coupled_fundamental_profile_of_cohn
    (hCohn : CohnQuarticPellClassification)
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data)
    (generator :
      Sm2LowerSquareUpperSourceGenerator allocation)
    (hatomic : generator.AtomicPacket) :
    ∃ hM : PellKernel (data.pell.D * data.upperKernel),
      fundamentalX (data.pell.D * data.upperKernel) hM =
          (allocation.y ^ 2 + 1) ^ 2 ∧
        fundamentalY (data.pell.D * data.upperKernel) hM =
          (data.pell.D * data.upperKernel) *
            ((allocation.y *
                allocation.linearUpperSquarePart) *
              data.upperSquarePart) ∧
        pellRank (data.pell.D * data.upperKernel) hM = 1 ∧
        fundamentalX data.upperKernel
            allocation.upper_pellKernel =
          2 *
              fundamentalX
                (data.pell.D * data.upperKernel) hM +
            1 ∧
        data.pell.D *
              (allocation.y *
                allocation.linearUpperSquarePart) *
              fundamentalY data.upperKernel
                allocation.upper_pellKernel =
          2 * (allocation.y ^ 2 + 1) *
            fundamentalY
              (data.pell.D * data.upperKernel) hM := by
  obtain ⟨hM, hx, _hdiv, hrank⟩ :=
    exists_combined_nested_square_rank_one_of_cohn
      hCohn allocation
  let Y :=
    (data.pell.D * data.upperKernel) *
      ((allocation.y * allocation.linearUpperSquarePart) *
        data.upperSquarePart)
  have hquartic :
      DivisibleNatQuarticPell
        (data.pell.D * data.upperKernel)
        data.center Y := by
    simpa [Y, allocation.lowerSquarePart_eq] using
      data.toDivisibleNatQuarticPell
  have hquarticFund :
      fundamentalX
            (data.pell.D * data.upperKernel) hM ^ 2 =
        (data.pell.D * data.upperKernel) * Y ^ 2 + 1 := by
    calc
      fundamentalX
            (data.pell.D * data.upperKernel) hM ^ 2 =
          ((allocation.y ^ 2 + 1) ^ 2) ^ 2 := by
        rw [hx]
      _ = data.center ^ 4 := by
        rw [allocation.center_eq]
        ring
      _ =
          (data.pell.D * data.upperKernel) * Y ^ 2 + 1 :=
        hquartic.equation
  have hfundSub :=
    fundamental_pell_equation
      (data.pell.D * data.upperKernel) hM
  have hfund :
      fundamentalX
            (data.pell.D * data.upperKernel) hM ^ 2 =
        (data.pell.D * data.upperKernel) *
            fundamentalY
              (data.pell.D * data.upperKernel) hM ^ 2 +
          1 := by
    omega
  have hproducts :
      (data.pell.D * data.upperKernel) * Y ^ 2 =
        (data.pell.D * data.upperKernel) *
          fundamentalY
            (data.pell.D * data.upperKernel) hM ^ 2 := by
    omega
  have hsquares :
      Y ^ 2 =
        fundamentalY
          (data.pell.D * data.upperKernel) hM ^ 2 :=
    Nat.eq_of_mul_eq_mul_left
      (Nat.zero_lt_of_lt hM.1) hproducts
  have hy :
      Y =
        fundamentalY
          (data.pell.D * data.upperKernel) hM :=
    Nat.pow_left_injective
      (by decide : (2 : Nat) ≠ 0) hsquares
  have hyExact :
      fundamentalY
          (data.pell.D * data.upperKernel) hM =
        (data.pell.D * data.upperKernel) *
          ((allocation.y *
              allocation.linearUpperSquarePart) *
            data.upperSquarePart) := by
    simpa [Y] using hy.symm
  rcases hatomic with
    ⟨_hbranch, _hroot, _hsource, _hrealCenter,
      hordinate, hreal, _hnegative,
      hfundXUpper, hfundYUpper, _hform⟩
  have hrealCoupling :
      fundamentalX data.upperKernel
          allocation.upper_pellKernel =
        2 *
            fundamentalX
              (data.pell.D * data.upperKernel) hM +
          1 := by
    calc
      fundamentalX data.upperKernel
          allocation.upper_pellKernel =
          2 * generator.real ^ 2 + 1 :=
        hfundXUpper
      _ = 2 * (allocation.y ^ 2 + 1) ^ 2 + 1 := by
        rw [hreal]
      _ =
          2 *
              fundamentalX
                (data.pell.D * data.upperKernel) hM +
            1 := by
        rw [hx]
  have hordinateCoupling :
      data.pell.D *
            (allocation.y *
              allocation.linearUpperSquarePart) *
            fundamentalY data.upperKernel
              allocation.upper_pellKernel =
        2 * (allocation.y ^ 2 + 1) *
          fundamentalY
            (data.pell.D * data.upperKernel) hM := by
    calc
      data.pell.D *
            (allocation.y *
              allocation.linearUpperSquarePart) *
            fundamentalY data.upperKernel
              allocation.upper_pellKernel =
          data.pell.D *
              (allocation.y *
                allocation.linearUpperSquarePart) *
              (2 * generator.real *
                generator.ordinate) := by
        rw [hfundYUpper]
      _ =
          data.pell.D *
              (allocation.y *
                allocation.linearUpperSquarePart) *
              (2 * (allocation.y ^ 2 + 1) *
                (data.upperKernel *
                  data.upperSquarePart)) := by
        rw [hreal, hordinate]
      _ =
          2 * (allocation.y ^ 2 + 1) *
            ((data.pell.D * data.upperKernel) *
              ((allocation.y *
                  allocation.linearUpperSquarePart) *
                data.upperSquarePart)) := by
        ring
      _ =
          2 * (allocation.y ^ 2 + 1) *
            fundamentalY
              (data.pell.D * data.upperKernel) hM := by
        rw [hyExact]
  exact
    ⟨hM, hx, hyExact, hrank,
      hrealCoupling, hordinateCoupling⟩

end Sm2LowerSquareAllocation

end Erdos364
