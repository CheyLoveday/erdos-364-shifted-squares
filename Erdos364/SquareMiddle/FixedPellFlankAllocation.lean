import Erdos364.SquareMiddle.PellDivisibilityRank
import Erdos364.SquareMiddle.FlankKernelAllocation
import Erdos364.SquareMiddle.Normalization

namespace Erdos364

/-!
# Fixed fundamental-unit allocation of Pell flank kernels

For an admissible Pell kernel whose fundamental `x` coordinate is even, each
prime factor of the squarefree kernel is permanently assigned to one of the
two flanks by the sign of the fundamental coordinate modulo that prime.  This
file proves that assignment and identifies it with the two actual flank
normal-form kernels of every odd-index source centre.

The evenness of the fundamental coordinate is explicit: it is a genuine
admissibility condition, not a consequence of arbitrary odd squarefree `D`
(for example, the fundamental solution for `D = 5` has odd `x`).
-/

/-- The portion of the Pell kernel permanently assigned to the lower flank. -/
noncomputable def fundamentalLowerKernel (D : Nat) (hD : PellKernel D) : Nat :=
  D.gcd (fundamentalX D hD - 1)

/-- The portion of the Pell kernel permanently assigned to the upper flank. -/
noncomputable def fundamentalUpperKernel (D : Nat) (hD : PellKernel D) : Nat :=
  D.gcd (fundamentalX D hD + 1)

theorem fundamentalLowerKernel_dvd_kernel (D : Nat) (hD : PellKernel D) :
    fundamentalLowerKernel D hD ∣ D := by
  exact Nat.gcd_dvd_left _ _

theorem fundamentalUpperKernel_dvd_kernel (D : Nat) (hD : PellKernel D) :
    fundamentalUpperKernel D hD ∣ D := by
  exact Nat.gcd_dvd_left _ _

theorem fundamentalLowerKernel_dvd_lowerFlank (D : Nat) (hD : PellKernel D) :
    fundamentalLowerKernel D hD ∣ fundamentalX D hD - 1 := by
  exact Nat.gcd_dvd_right _ _

theorem fundamentalUpperKernel_dvd_upperFlank (D : Nat) (hD : PellKernel D) :
    fundamentalUpperKernel D hD ∣ fundamentalX D hD + 1 := by
  exact Nat.gcd_dvd_right _ _

/-- The Pell equation places the kernel inside the product of the two
fundamental flanks. -/
theorem kernel_dvd_fundamentalFlank_product (D : Nat) (hD : PellKernel D) :
    D ∣ (fundamentalX D hD - 1) * (fundamentalX D hD + 1) := by
  have hEq := fundamental_pell_equation D hD
  have hEq' : fundamentalX D hD ^ 2 =
      D * fundamentalY D hD ^ 2 + 1 := by
    omega
  have hsub : fundamentalX D hD ^ 2 - 1 = D * fundamentalY D hD ^ 2 := by
    rw [hEq']
    omega
  rw [← square_sub_one_eq_flank_mul (Nat.zero_lt_of_lt (fundamentalX_one_lt D hD))]
  rw [hsub]
  exact dvd_mul_right D _

/-- If the fundamental `x` coordinate is even, its two integer flanks are
coprime. -/
theorem fundamentalFlanks_coprime_of_even (D : Nat) (hD : PellKernel D)
    (heven : Even (fundamentalX D hD)) :
    Nat.Coprime (fundamentalX D hD - 1) (fundamentalX D hD + 1) := by
  have hXone : 1 ≤ fundamentalX D hD := (fundamentalX_one_lt D hD).le
  have hminusOdd : Odd (fundamentalX D hD - 1) :=
    Nat.Even.sub_odd hXone heven odd_one
  have hcopTwo : Nat.Coprime (fundamentalX D hD - 1) 2 :=
    Nat.coprime_two_right.mpr hminusOdd
  rw [show fundamentalX D hD + 1 = 2 + (fundamentalX D hD - 1) by omega,
    Nat.coprime_add_self_right]
  exact hcopTwo

/-- Under the explicit even-fundamental admissibility condition, the two
fixed kernels are coprime and multiply back to `D`. -/
theorem fundamentalFlankKernels_coprime_and_product (D : Nat) (hD : PellKernel D)
    (heven : Even (fundamentalX D hD)) :
    Nat.Coprime (fundamentalLowerKernel D hD) (fundamentalUpperKernel D hD) ∧
      fundamentalLowerKernel D hD * fundamentalUpperKernel D hD = D := by
  have hcop := fundamentalFlanks_coprime_of_even D hD heven
  have hprod := kernel_dvd_fundamentalFlank_product D hD
  constructor
  · exact hcop.of_dvd
      (fundamentalLowerKernel_dvd_lowerFlank D hD)
      (fundamentalUpperKernel_dvd_upperFlank D hD)
  · simpa [fundamentalLowerKernel, fundamentalUpperKernel] using
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (x := D) hcop).mpr hprod

/-- The fundamental `x` coordinate squares to one modulo its Pell kernel. -/
theorem fundamentalX_sq_eq_one_mod_kernel (D : Nat) (hD : PellKernel D) :
    (fundamentalX D hD : ZMod D) ^ 2 = 1 := by
  have h := congrArg (fun z : Int => (z : ZMod D))
    (fundamentalPell D hD).prop
  rw [← fundamentalX_intCast D hD] at h
  push_cast at h
  simp only [ZMod.natCast_self, zero_mul, sub_zero] at h
  simpa [pow_two] using h

/-- An odd power of the fundamental `x` coordinate agrees with that
coordinate modulo the Pell kernel. -/
theorem fundamentalX_pow_eq_fundamentalX_mod_kernel_of_odd
    (D : Nat) (hD : PellKernel D) {n : Nat} (hn : Odd n) :
    (fundamentalX D hD : ZMod D) ^ n = (fundamentalX D hD : ZMod D) := by
  rcases hn with ⟨k, hk⟩
  rw [hk, pow_add, pow_mul, fundamentalX_sq_eq_one_mod_kernel]
  simp

/-- At every odd index, the canonical Pell `x` coordinate is congruent to the
fundamental `x` coordinate modulo the kernel. -/
theorem pellX_mod_kernel_eq_fundamentalX_of_odd
    (D : Nat) (hD : PellKernel D) {n : Nat} (hn : Odd n) :
    (pellX D hD n : ZMod D) = (fundamentalX D hD : ZMod D) := by
  have hpow := (pellSolution_pow_mod_kernel_pair (fundamentalPell D hD) n).1
  have hx : (pellX D hD n : ZMod D) =
      ((pellSolution D hD n).x : ZMod D) := by
    have h := congrArg (fun z : Int => (z : ZMod D))
      (pellX_intCast D hD n)
    simpa using h
  have hfund : (fundamentalX D hD : ZMod D) =
      ((fundamentalPell D hD).x : ZMod D) := by
    have h := congrArg (fun z : Int => (z : ZMod D))
      (fundamentalX_intCast D hD)
    simpa using h
  calc
    (pellX D hD n : ZMod D) = ((pellSolution D hD n).x : ZMod D) := hx
    _ = ((fundamentalPell D hD).x : ZMod D) ^ n := hpow
    _ = (fundamentalX D hD : ZMod D) ^ n := by rw [hfund]
    _ = (fundamentalX D hD : ZMod D) :=
      fundamentalX_pow_eq_fundamentalX_mod_kernel_of_odd D hD hn

/-- Natural-number formulation of the odd-index congruence. -/
theorem pellX_modEq_fundamentalX_of_odd
    (D : Nat) (hD : PellKernel D) {n : Nat} (hn : Odd n) :
    pellX D hD n ≡ fundamentalX D hD [MOD D] := by
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (pellX_mod_kernel_eq_fundamentalX_of_odd D hD hn)

private theorem SquareCubeNormalForm.kernel_dvd_value
    {N A E : Nat} (hform : SquareCubeNormalForm N A E) :
    E ∣ N := by
  rw [hform.2.2.1]
  exact ⟨A ^ 2 * E ^ 2, by ring⟩

/-- A divisor of the Pell kernel which lies in the lower flank of an
odd-index centre also lies in the corresponding fundamental lower flank. -/
private theorem divisor_dvd_fundamental_lowerFlank
    {D X d : Nat} (hD : PellKernel D) (hXd : 1 ≤ X)
    (hmod : X ≡ fundamentalX D hD [MOD D]) (hdD : d ∣ D)
    (hdminus : d ∣ X - 1) :
    d ∣ fundamentalX D hD - 1 := by
  have hmod_d : X ≡ fundamentalX D hD [MOD d] := hmod.of_dvd hdD
  have hminus_zero : X - 1 ≡ 0 [MOD d] := hdminus.modEq_zero_nat
  have hX_one : X ≡ 1 [MOD d] := by
    have h := hminus_zero.add_right 1
    rw [Nat.sub_add_cancel hXd] at h
    simpa using h
  have hfund_one : fundamentalX D hD ≡ 1 [MOD d] :=
    hmod_d.symm.trans hX_one
  exact (Nat.modEq_iff_dvd' (fundamentalX_one_lt D hD).le).mp hfund_one.symm

/-- A divisor of the Pell kernel which lies in the upper flank of an
odd-index centre also lies in the corresponding fundamental upper flank. -/
private theorem divisor_dvd_fundamental_upperFlank
    {D X d : Nat} (hD : PellKernel D)
    (hmod : X ≡ fundamentalX D hD [MOD D]) (hdD : d ∣ D)
    (hdplus : d ∣ X + 1) :
    d ∣ fundamentalX D hD + 1 := by
  have hmod_d : X ≡ fundamentalX D hD [MOD d] := hmod.of_dvd hdD
  have hplus_zero : X + 1 ≡ 0 [MOD d] := hdplus.modEq_zero_nat
  have hfund_plus_zero : fundamentalX D hD + 1 ≡ 0 [MOD d] :=
    (hmod_d.add_right 1).symm.trans hplus_zero
  exact Nat.modEq_zero_iff_dvd.mp hfund_plus_zero

/-- The fundamental-unit allocation is exactly the allocation of the two
actual powerful flank kernels at every odd-index source centre.  The source
normal form supplies the product kernel `D`; the proof then uses the odd-index
congruence and coprimality of the fundamental flanks to identify each factor.
-/
theorem SquareMiddleFlankNormalForms.fixed_fundamental_allocation
    {X A D n : Nat} (h : SquareMiddle X) (w : SquareMiddleFlankNormalForms X)
    (hsource : SquareCubeNormalForm (X ^ 2 - 1) A D)
    (hD : PellKernel D) (heven : Even (fundamentalX D hD))
    (hcenter : X = pellX D hD n) (hn : Odd n) :
    w.lowerKernel = fundamentalLowerKernel D hD ∧
      w.upperKernel = fundamentalUpperKernel D hD := by
  have hprod : w.lowerKernel * w.upperKernel = D :=
    w.kernel_product_eq h hsource
  have hlD : w.lowerKernel ∣ D := by
    rw [← hprod]
    exact dvd_mul_right _ _
  have huD : w.upperKernel ∣ D := by
    rw [← hprod]
    exact dvd_mul_left _ _
  have hlminus : w.lowerKernel ∣ X - 1 := w.lowerForm.kernel_dvd_value
  have huplus : w.upperKernel ∣ X + 1 := w.upperForm.kernel_dvd_value
  have hmod : X ≡ fundamentalX D hD [MOD D] := by
    rw [hcenter]
    exact pellX_modEq_fundamentalX_of_odd D hD hn
  have hlFundMinus : w.lowerKernel ∣ fundamentalX D hD - 1 :=
    divisor_dvd_fundamental_lowerFlank hD h.1.le hmod hlD hlminus
  have huFundPlus : w.upperKernel ∣ fundamentalX D hD + 1 :=
    divisor_dvd_fundamental_upperFlank hD hmod huD huplus
  have hlFixed : w.lowerKernel ∣ fundamentalLowerKernel D hD :=
    Nat.dvd_gcd hlD hlFundMinus
  have huFixed : w.upperKernel ∣ fundamentalUpperKernel D hD :=
    Nat.dvd_gcd huD huFundPlus
  have hfundCop := fundamentalFlanks_coprime_of_even D hD heven
  have hLowerFixed_coprime_upper :
      Nat.Coprime (fundamentalLowerKernel D hD) w.upperKernel :=
    hfundCop.of_dvd (fundamentalLowerKernel_dvd_lowerFlank D hD) huFundPlus
  have hUpperFixed_coprime_lower :
      Nat.Coprime (fundamentalUpperKernel D hD) w.lowerKernel :=
    hfundCop.symm.of_dvd
      (fundamentalUpperKernel_dvd_upperFlank D hD) hlFundMinus
  have hFixedLower_dvd : fundamentalLowerKernel D hD ∣ w.lowerKernel := by
    apply hLowerFixed_coprime_upper.dvd_of_dvd_mul_right
    rw [hprod]
    exact fundamentalLowerKernel_dvd_kernel D hD
  have hFixedUpper_dvd : fundamentalUpperKernel D hD ∣ w.upperKernel := by
    apply hUpperFixed_coprime_lower.dvd_of_dvd_mul_right
    rw [mul_comm, hprod]
    exact fundamentalUpperKernel_dvd_kernel D hD
  exact ⟨Nat.dvd_antisymm hlFixed hFixedLower_dvd,
    Nat.dvd_antisymm huFixed hFixedUpper_dvd⟩

/-- Source-facing specialization of the fixed allocation.  A fully normalized
square-middle witness therefore carries no free flank-kernel choices: both
are recovered from its fundamental Pell unit. -/
theorem ValidNormalizedWitness.fixed_fundamental_allocation
    {X : Nat} (w : ValidNormalizedWitness X) :
    w.flanks.lowerKernel = fundamentalLowerKernel w.D w.pellKernel ∧
      w.flanks.upperKernel = fundamentalUpperKernel w.D w.pellKernel := by
  obtain ⟨A, hsource⟩ :=
    w.pell_represents_source.exists_squareSubOne_normalForm
  have hn : Odd (canonicalPellIndex w.D w.pellKernel w.k) := by
    unfold canonicalPellIndex
    exact (pellRank_odd_of_kernel_odd w.D w.pellKernel w.kernel_odd).mul
      (odd_two_mul_add_one w.k)
  apply w.flanks.fixed_fundamental_allocation w.source hsource
    w.pellKernel w.fundamentalX_even
  · simpa [canonicalPellCenter] using w.center_eq
  · exact hn

end Erdos364
