import Erdos364.SquareMiddle.PellDivisibilityPrime

namespace Erdos364

/-- The exact index rank for divisibility of the canonical Pell y-coordinate
by its squarefree kernel. -/
noncomputable def pellRank (D : Nat) (hD : PellKernel D) : Nat :=
  D / D.gcd (fundamentalY D hD)

/-- The rank is positive.  This records the nonzero denominator needed by
the later index arithmetic. -/
theorem pellRank_pos (D : Nat) (hD : PellKernel D) :
    0 < pellRank D hD := by
  have hD_pos : 0 < D := Nat.zero_lt_of_lt hD.1
  have hg_dvd : D.gcd (fundamentalY D hD) ∣ D := Nat.gcd_dvd_left _ _
  have hg_pos : 0 < D.gcd (fundamentalY D hD) :=
    Nat.gcd_pos_of_pos_left _ hD_pos
  exact Nat.div_pos (Nat.le_of_dvd hD_pos hg_dvd) hg_pos

/-- The rank divides its kernel. -/
theorem pellRank_dvd_kernel (D : Nat) (hD : PellKernel D) :
    pellRank D hD ∣ D := by
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left D (fundamentalY D hD))

/-- Cancelling the fundamental y-coordinate from `D ∣ n * Y₁` is exact.
Squarefreeness is used precisely to make the residual quotient coprime to
`Y₁`; positivity of `Y₁` supplies the required nonzero hypothesis. -/
theorem kernel_dvd_index_mul_fundamentalY_iff_rank_dvd
    (D : Nat) (hD : PellKernel D) (n : Nat) :
    D ∣ n * fundamentalY D hD ↔ pellRank D hD ∣ n := by
  constructor
  · intro hdiv
    have hRank_div_product : pellRank D hD ∣ n * fundamentalY D hD :=
      (pellRank_dvd_kernel D hD).trans hdiv
    have hY_ne : fundamentalY D hD ≠ 0 :=
      Nat.ne_of_gt (fundamentalY_pos D hD)
    have hcoprime : (pellRank D hD).Coprime (fundamentalY D hD) := by
      simpa [pellRank] using
        Nat.coprime_div_gcd_of_squarefree hD.2 hY_ne
    exact hcoprime.dvd_of_dvd_mul_right hRank_div_product
  · intro hRank
    let g := D.gcd (fundamentalY D hD)
    have hg_dvd_D : g ∣ D := Nat.gcd_dvd_left _ _
    have hg_dvd_Y : g ∣ fundamentalY D hD := Nat.gcd_dvd_right _ _
    have hg_pos : 0 < g :=
      Nat.gcd_pos_of_pos_left _ (Nat.zero_lt_of_lt hD.1)
    have hD_dvd_gn : D ∣ g * n := by
      exact (Nat.div_dvd_iff_dvd_mul hg_dvd_D hg_pos).mp
        (by simpa [pellRank, g] using hRank)
    have hgn_dvd_Yn : g * n ∣ fundamentalY D hD * n :=
      Nat.mul_dvd_mul_right hg_dvd_Y n
    exact hD_dvd_gn.trans (by simpa [mul_comm] using hgn_dvd_Yn)

/-- Exact composite divisibility rank for the canonical Pell sequence. -/
theorem D_dvd_pellY_iff_rank_dvd_index
    (D : Nat) (hD : PellKernel D) (n : Nat) :
    D ∣ pellY D hD n ↔ pellRank D hD ∣ n := by
  exact (kernel_dvd_pellY_iff_index_mul_fundamentalY D hD n).trans
    (kernel_dvd_index_mul_fundamentalY_iff_rank_dvd D hD n)

end Erdos364
