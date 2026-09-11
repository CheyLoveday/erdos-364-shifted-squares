import Erdos364.SquareMiddle.PellCoordinates

namespace Erdos364

/-- Powers of an arbitrary norm-one Pell solution, reduced modulo its
discriminant.  The first component is `x^n`; the second is the linear term
`(n + 1) * x^n * y`. -/
theorem pellSolution_pow_mod_kernel_pair {D : Nat}
    (e : Pell.Solution₁ (D : Int)) :
    ∀ n : Nat,
      (((e ^ n).x : ZMod D) = (e.x : ZMod D) ^ n) ∧
      (((e ^ (n + 1)).y : ZMod D) =
        (n + 1 : ZMod D) * (e.x : ZMod D) ^ n * (e.y : ZMod D)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rcases ih with ⟨hx, hy⟩
      have hx' :
          ((e ^ (n + 1)).x : ZMod D) = (e.x : ZMod D) ^ (n + 1) := by
        rw [pow_succ, Pell.Solution₁.x_mul]
        push_cast
        rw [hx, ZMod.natCast_self]
        simp [pow_succ]
      refine ⟨by simpa [Nat.succ_eq_add_one] using hx', ?_⟩
      rw [show n.succ + 1 = (n + 1) + 1 by omega,
        pow_succ, Pell.Solution₁.y_mul]
      push_cast
      rw [hx', hy]
      ring

/-- The x-coordinate of a norm-one Pell solution is a unit modulo the
discriminant: its square is one there. -/
theorem pellSolution_x_isUnit_mod_kernel {D : Nat}
    (e : Pell.Solution₁ (D : Int)) :
    IsUnit (e.x : ZMod D) := by
  have h := congrArg (fun z : Int => (z : ZMod D)) e.prop
  push_cast at h
  simp only [ZMod.natCast_self, zero_mul, sub_zero] at h
  rw [show (e.x : ZMod D) ^ 2 =
      (e.x : ZMod D) * (e.x : ZMod D) by ring] at h
  exact isUnit_iff_exists_inv.mpr ⟨(e.x : ZMod D), h⟩

/-- Successor-index divisibility for an arbitrary norm-one Pell solution.
No primality or squarefreeness hypothesis is needed. -/
theorem kernel_dvd_pellSolutionY_succ_iff {D n : Nat}
    (e : Pell.Solution₁ (D : Int)) :
    (D : Int) ∣ (e ^ (n + 1)).y ↔
      (D : Int) ∣ (n + 1 : Nat) * e.y := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [(pellSolution_pow_mod_kernel_pair e n).2]
  push_cast
  have hu := (pellSolution_x_isUnit_mod_kernel e).pow n
  have hcancel :
      ((e.x : ZMod D) ^ n *
          ((n + 1 : ZMod D) * (e.y : ZMod D)) = 0 ↔
        ((n + 1 : ZMod D) * (e.y : ZMod D)) = 0) := by
    simpa using
      (hu.mul_right_inj :
        (e.x : ZMod D) ^ n *
            ((n + 1 : ZMod D) * (e.y : ZMod D)) =
          (e.x : ZMod D) ^ n * 0 ↔ _)
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcancel

/-- Exact divisibility rank before the gcd is cancelled: for every natural
index `n`, the discriminant divides `Y_n` exactly when it divides `n * Y_1`.
This is the generic theorem used by the later composite-rank layer. -/
theorem kernel_dvd_pellSolutionY_iff {D n : Nat}
    (e : Pell.Solution₁ (D : Int)) :
    (D : Int) ∣ (e ^ n).y ↔ (D : Int) ∣ (n : Int) * e.y := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        (kernel_dvd_pellSolutionY_succ_iff (D := D) (n := n) e)

/-- Natural-coordinate specialization of the generic divisibility theorem to
the selected fundamental Pell solution. -/
theorem kernel_dvd_pellY_iff_index_mul_fundamentalY
    (D : Nat) (hD : PellKernel D) (n : Nat) :
    D ∣ pellY D hD n ↔ D ∣ n * fundamentalY D hD := by
  have h := kernel_dvd_pellSolutionY_iff
    (D := D) (n := n) (fundamentalPell D hD)
  change (D : Int) ∣ (pellSolution D hD n).y ↔
    (D : Int) ∣ (n : Int) * (fundamentalPell D hD).y at h
  rw [← pellY_intCast D hD n, ← fundamentalY_intCast D hD] at h
  exact_mod_cast h

end Erdos364
