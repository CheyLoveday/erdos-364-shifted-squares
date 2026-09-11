import Erdos364.SquareMiddle.FixedPellFlankAllocation
import Erdos364.SquareMiddle.RightFlankNormOneModNine

namespace Erdos364

open Pell

/-!
# Generic norm-one controls for complete upper fibres

An arbitrary positive norm-one control whose real coordinate is neither
`1` nor `-1` modulo its Pell kernel rules out every positive negative-Pell
source at that kernel.  The parametric family below supplies explicit such
controls without requiring that the displayed control be fundamental.
-/

/-- An arbitrary positive norm-one control whose real coordinate is neither
`1` nor `-1` modulo `K` rules out all positive negative-Pell solutions. -/
theorem no_negativePell_of_normOne_control
    {K : Nat} (hPK : PellKernel K) (hK : 2 < K)
    (z : Pell.Solution₁ (K : Int))
    (hzx : 0 < z.x) (hzy : 0 ≤ z.y)
    (hz_ne_one : (z.x : ZMod K) ≠ 1)
    (hz_ne_negOne : (z.x : ZMod K) ≠ -1)
    {X W : Nat} (hX : 0 < X) (hW : 0 < W)
    (hPell : X ^ 2 + 1 = K * W ^ 2) :
    False := by
  let e := fundamentalPell K hPK
  have hfund : Pell.IsFundamental e :=
    fundamentalPell_isFundamental K hPK
  obtain ⟨_m, _hmOdd, _hnegPow, heSign⟩ :=
    negativePell_eq_fundamental_odd_power_and_x_mod_kernel
      hK e hfund hX hW hPell
  obtain ⟨n, hn⟩ := hfund.eq_pow_of_nonneg hzx hzy
  have heSq : (e.x : ZMod K) ^ 2 = 1 := by
    have h := congrArg (fun value : Int => (value : ZMod K)) e.prop
    push_cast at h
    simpa only [ZMod.natCast_self, zero_mul, sub_zero] using h
  have hzPow : (z.x : ZMod K) = (e.x : ZMod K) ^ n := by
    calc
      (z.x : ZMod K) = ((e ^ n).x : ZMod K) := by rw [← hn]
      _ = (e.x : ZMod K) ^ n :=
        (pellSolution_pow_mod_kernel_pair e n).1
  rcases n.even_or_odd with hnEven | hnOdd
  · obtain ⟨r, rfl⟩ := hnEven
    apply hz_ne_one
    rw [hzPow, show r + r = 2 * r by omega, pow_mul, heSq, one_pow]
  · obtain ⟨r, rfl⟩ := hnOdd
    apply hz_ne_negOne
    rw [hzPow, pow_add, pow_mul, heSq, one_pow, one_mul, heSign]
    simp

/-- Source-typed form of `no_negativePell_of_normOne_control`. -/
theorem no_divisibleNatNegativePell_of_normOne_control
    {K : Nat} (hPK : PellKernel K) (hK : 2 < K)
    (z : Pell.Solution₁ (K : Int))
    (hzx : 0 < z.x) (hzy : 0 ≤ z.y)
    (hz_ne_one : (z.x : ZMod K) ≠ 1)
    (hz_ne_negOne : (z.x : ZMod K) ≠ -1)
    {X W : Nat} (h : DivisibleNatNegativePell K X W) :
    False :=
  no_negativePell_of_normOne_control hPK hK z hzx hzy
    hz_ne_one hz_ne_negOne
    (Nat.zero_lt_of_lt h.X_one_lt) h.W_pos h.equation.symm

/-- Complete fixed-upper-fibre form of the generic norm-one control. -/
theorem no_pairPellCounterexample_upperKernel_of_normOne_control
    {K : Nat}
    (z : Pell.Solution₁ (K : Int))
    (hzx : 0 < z.x) (hzy : 0 ≤ z.y)
    (hz_ne_one : (z.x : ZMod K) ≠ 1)
    (hz_ne_negOne : (z.x : ZMod K) ≠ -1)
    (data : PairPellCounterexampleData) (hupper : data.upperKernel = K) :
    False := by
  have hnegative : DivisibleNatNegativePell K data.center
      (data.upperKernel * data.upperSquarePart) := by
    simpa [hupper] using data.upper_negativePell
  have hPK : PellKernel K :=
    ⟨by simpa [hupper] using data.upperKernel_one_lt,
      hnegative.K_squarefree⟩
  have hK : 2 < K := by
    have hKNeTwo : K ≠ 2 := by
      intro hKTwo
      have htwoDvd : 2 ∣ data.upperKernel * data.upperSquarePart := by
        rw [hupper, hKTwo]
        exact dvd_mul_right 2 data.upperSquarePart
      have hmod :=
        data.upperSupport_prime_mod_four_eq_one Nat.prime_two htwoDvd
      norm_num at hmod
    have hKOne : 1 < K := hPK.1
    omega
  exact no_divisibleNatNegativePell_of_normOne_control
    hPK hK z hzx hzy hz_ne_one hz_ne_negOne hnegative

/-- Kernel in the explicit norm-one control family. -/
def normOneControlKernel (h c : Nat) : Nat :=
  c * (4 * h ^ 2 * c + 1)

/-- The explicit positive norm-one control for `normOneControlKernel h c`. -/
def normOneFamilyControl (h c : Nat) :
    Pell.Solution₁ (normOneControlKernel h c : Int) :=
  Pell.Solution₁.mk
    (8 * h ^ 2 * c + 1)
    (4 * h)
    (by
      simp only [normOneControlKernel]
      push_cast
      ring)

private theorem normOneFamilyControl_x_cast (h c : Nat) :
    (((8 * h ^ 2 * c + 1 : Nat) : ZMod (normOneControlKernel h c))) =
      ((normOneFamilyControl h c).x : ZMod (normOneControlKernel h c)) := by
  simp only [normOneFamilyControl, Pell.Solution₁.x_mk]
  push_cast
  ring

private theorem normOneFamilyControl_x_lt_kernel
    {h c : Nat} (hh : 0 < h) (hc : 3 ≤ c) :
    8 * h ^ 2 * c + 1 < normOneControlKernel h c := by
  simp only [normOneControlKernel]
  have hcc : 3 * c ≤ c * c := by nlinarith
  have hscaled :
      4 * h ^ 2 * (3 * c) ≤ 4 * h ^ 2 * (c * c) :=
    Nat.mul_le_mul_left (4 * h ^ 2) hcc
  have hhcpos : 0 < h ^ 2 * c := Nat.mul_pos (pow_pos hh 2) (by omega)
  nlinarith

private theorem normOneFamilyControl_x_add_one_lt_kernel
    {h c : Nat} (hh : 0 < h) (hc : 3 ≤ c) :
    8 * h ^ 2 * c + 1 + 1 < normOneControlKernel h c := by
  simp only [normOneControlKernel]
  have hcc : 3 * c ≤ c * c := by nlinarith
  have hscaled :
      4 * h ^ 2 * (3 * c) ≤ 4 * h ^ 2 * (c * c) :=
    Nat.mul_le_mul_left (4 * h ^ 2) hcc
  have hhcpos : 0 < h ^ 2 * c := Nat.mul_pos (pow_pos hh 2) (by omega)
  nlinarith

private theorem normOneFamilyControl_x_ne_one_mod
    {h c : Nat} (hh : 0 < h) (hc : 3 ≤ c) :
    ((normOneFamilyControl h c).x : ZMod (normOneControlKernel h c)) ≠ 1 := by
  intro heq
  have heqNat :
      (((8 * h ^ 2 * c + 1 : Nat) : ZMod
        (normOneControlKernel h c))) = 1 := by
    rw [normOneFamilyControl_x_cast]
    exact heq
  have hmod :
      8 * h ^ 2 * c + 1 ≡ 1 [MOD normOneControlKernel h c] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa using heqNat
  have hxlt :=
    normOneFamilyControl_x_lt_kernel hh hc
  have hOneLt : 1 < normOneControlKernel h c := by omega
  have hxmod : (8 * h ^ 2 * c + 1) % normOneControlKernel h c = 1 := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hOneLt] using hmod
  have hxgt : 1 < 8 * h ^ 2 * c + 1 := by
    have : 0 < h ^ 2 * c := Nat.mul_pos (pow_pos hh 2) (by omega)
    nlinarith
  rw [Nat.mod_eq_of_lt hxlt] at hxmod
  omega

private theorem normOneFamilyControl_x_ne_negOne_mod
    {h c : Nat} (hh : 0 < h) (hc : 3 ≤ c) :
    ((normOneFamilyControl h c).x : ZMod (normOneControlKernel h c)) ≠ -1 := by
  intro heq
  have hzX :
      (((8 * h ^ 2 * c + 1 : Nat) : ZMod
        (normOneControlKernel h c))) = -1 := by
    rw [normOneFamilyControl_x_cast]
    exact heq
  have hzero :
      (((8 * h ^ 2 * c + 1 + 1 : Nat) : ZMod
        (normOneControlKernel h c))) = 0 := by
    calc
      (((8 * h ^ 2 * c + 1 + 1 : Nat) : ZMod
          (normOneControlKernel h c))) =
          ((8 * h ^ 2 * c + 1 : Nat) : ZMod
            (normOneControlKernel h c)) + 1 := by
              push_cast
              ring
      _ = -1 + 1 := by rw [hzX]
      _ = 0 := by ring
  have hdvd :
      normOneControlKernel h c ∣ 8 * h ^ 2 * c + 1 + 1 :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hle : normOneControlKernel h c ≤ 8 * h ^ 2 * c + 1 + 1 :=
    Nat.le_of_dvd (by positivity) hdvd
  exact (Nat.not_le_of_lt
    (normOneFamilyControl_x_add_one_lt_kernel hh hc)) hle

/-- Every member of `c * (4 h² c + 1)`, for `h > 0` and `c ≥ 3`, has an
empty complete upper-kernel fibre.  No squarefreeness hypothesis on the
parameters is needed: an actual counterexample supplies it through its
upper-kernel equality. -/
theorem no_pairPellCounterexample_upperKernel_normOneControlFamily
    {h c : Nat} (hh : 0 < h) (hc : 3 ≤ c)
    (data : PairPellCounterexampleData)
    (hupper : data.upperKernel = normOneControlKernel h c) :
    False := by
  have hzx : 0 < (normOneFamilyControl h c).x := by
    simp only [normOneFamilyControl, Pell.Solution₁.x_mk]
    positivity
  have hzy : 0 ≤ (normOneFamilyControl h c).y := by
    simp only [normOneFamilyControl, Pell.Solution₁.y_mk]
    positivity
  exact no_pairPellCounterexample_upperKernel_of_normOne_control
    (normOneFamilyControl h c) hzx hzy
    (normOneFamilyControl_x_ne_one_mod hh hc)
    (normOneFamilyControl_x_ne_negOne_mod hh hc)
    data hupper

private theorem four_mul_sq_mod_twentyFour_of_mod_six
    {h r : Nat} (hmod : h % 6 = r) :
    4 * h ^ 2 ≡ 4 * r ^ 2 [MOD 24] := by
  have hrepr : h = r + 6 * (h / 6) := by
    have hdiv := Nat.mod_add_div h 6
    rw [hmod] at hdiv
    omega
  rw [hrepr]
  rw [Nat.modEq_iff_dvd]
  refine ⟨-(2 * (r : Int) * (h / 6) + 6 * (h / 6 : Int) ^ 2), ?_⟩
  push_cast
  ring

private theorem normOneControlKernel_mod_twentyFour
    {h c r s : Nat} (hh : h % 6 = r) (hc : c % 24 = s) :
    normOneControlKernel h c % 24 =
      (s * (4 * r ^ 2 * s + 1)) % 24 := by
  have hslt : s < 24 := by
    rw [← hc]
    exact Nat.mod_lt _ (by decide)
  have hcmod : c ≡ s [MOD 24] := by
    change c % 24 = s % 24
    rw [hc, Nat.mod_eq_of_lt hslt]
  have hfour := four_mul_sq_mod_twentyFour_of_mod_six hh
  have hinner : 4 * h ^ 2 * c + 1 ≡ 4 * r ^ 2 * s + 1 [MOD 24] := by
    exact (hfour.mul hcmod).add (Nat.ModEq.refl 1)
  have hkernel :
      normOneControlKernel h c ≡
        s * (4 * r ^ 2 * s + 1) [MOD 24] := by
    simpa [normOneControlKernel] using hcmod.mul hinner
  exact hkernel

/-- Exact leaf-compatible parameter sectors for the norm-one control family.
This records only the kernel residue `5 mod 24`; it does not assert
squarefreeness or source realizability for arbitrary parameters. -/
theorem normOneControlKernel_mod_twentyFour_eq_five_of_compatible_residues
    {h c : Nat}
    (hparams :
      (h % 6 = 0 ∧ c % 24 = 5) ∨
        ((h % 6 = 1 ∨ h % 6 = 5) ∧ c % 24 = 1) ∨
          ((h % 6 = 2 ∨ h % 6 = 4) ∧ c % 24 = 13) ∨
            (h % 6 = 3 ∧ c % 24 = 17)) :
    normOneControlKernel h c % 24 = 5 := by
  rcases hparams with ⟨hh, hc⟩ | ⟨hcases, hc⟩ | ⟨hcases, hc⟩ | ⟨hh, hc⟩
  · have hmod := normOneControlKernel_mod_twentyFour hh hc
    norm_num at hmod ⊢
    exact hmod
  · rcases hcases with hh | hh
    · have hmod := normOneControlKernel_mod_twentyFour hh hc
      norm_num at hmod ⊢
      exact hmod
    · have hmod := normOneControlKernel_mod_twentyFour hh hc
      norm_num at hmod ⊢
      exact hmod
  · rcases hcases with hh | hh
    · have hmod := normOneControlKernel_mod_twentyFour hh hc
      norm_num at hmod ⊢
      exact hmod
    · have hmod := normOneControlKernel_mod_twentyFour hh hc
      norm_num at hmod ⊢
      exact hmod
  · have hmod := normOneControlKernel_mod_twentyFour hh hc
    norm_num at hmod ⊢
    exact hmod

/-- Exact squarefree control at parameters `(h,c) = (1,73)`. -/
theorem normOneControlFamily_control_one_seventyThree :
    normOneControlKernel 1 73 = 21389 ∧
      21389 = 73 * 293 ∧
        Nat.Prime 73 ∧
          Nat.Prime 293 ∧
            Squarefree 21389 ∧
              21389 % 24 = 5 ∧
                ∀ p : Nat, p.Prime → p ∣ 21389 → p % 4 = 1 := by
  refine ⟨by norm_num [normOneControlKernel], by norm_num,
    by norm_num, by norm_num, ?_, by norm_num, ?_⟩
  · rw [show 21389 = 73 * 293 by norm_num]
    apply (Nat.squarefree_mul (by norm_num : Nat.Coprime 73 293)).mpr
    constructor
    · exact (Nat.prime_iff.mp (by norm_num : Nat.Prime 73)).squarefree
    · exact (Nat.prime_iff.mp (by norm_num : Nat.Prime 293)).squarefree
  · intro p hp hpdiv
    rw [show 21389 = 73 * 293 by norm_num] at hpdiv
    rcases hp.dvd_mul.mp hpdiv with hp73 | hp293
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 73)).mp hp73 with
        hpone | hpeq
      · exact False.elim (hp.ne_one hpone)
      · subst p
        norm_num
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 293)).mp hp293 with
        hpone | hpeq
      · exact False.elim (hp.ne_one hpone)
      · subst p
        norm_num

/-- Exact squarefree control at parameters `(h,c) = (3,17)`. -/
theorem normOneControlFamily_control_three_seventeen :
    normOneControlKernel 3 17 = 10421 ∧
      10421 = 17 * 613 ∧
        Nat.Prime 17 ∧
          Nat.Prime 613 ∧
            Squarefree 10421 ∧
              10421 % 24 = 5 ∧
                ∀ p : Nat, p.Prime → p ∣ 10421 → p % 4 = 1 := by
  refine ⟨by norm_num [normOneControlKernel], by norm_num,
    by norm_num, by norm_num, ?_, by norm_num, ?_⟩
  · rw [show 10421 = 17 * 613 by norm_num]
    apply (Nat.squarefree_mul (by norm_num : Nat.Coprime 17 613)).mpr
    constructor
    · exact (Nat.prime_iff.mp (by norm_num : Nat.Prime 17)).squarefree
    · exact (Nat.prime_iff.mp (by norm_num : Nat.Prime 613)).squarefree
  · intro p hp hpdiv
    rw [show 10421 = 17 * 613 by norm_num] at hpdiv
    rcases hp.dvd_mul.mp hpdiv with hp17 | hp613
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hp17 with
        hpone | hpeq
      · exact False.elim (hp.ne_one hpone)
      · subst p
        norm_num
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 613)).mp hp613 with
        hpone | hpeq
      · exact False.elim (hp.ne_one hpone)
      · subst p
        norm_num

end Erdos364
