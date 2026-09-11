import Erdos364.SquareMiddle.PellIndex
import Erdos364.SquareMiddle.Sm2LowerSquareResidual

namespace Erdos364

/-!
# Exact lower norm-minus-two orbit for `sm2LowerSquare`

The lower fundamental-unit classifier writes the selected positive
fundamental norm-one unit as half the square of
`r + s * sqrt D`, a positive norm-minus-two point.  This file keeps the
result in natural coordinates and identifies the exact source-depth term
carried by every `sm2LowerSquare` allocation.
-/

/-- Real coordinate of
`(r + s * sqrt D) * (fundamentalPell D hD) ^ m`. -/
noncomputable def lowerNormTwoX
    (D : Nat) (hD : PellKernel D) (r s m : Nat) : Nat :=
  r * pellX D hD m + D * s * pellY D hD m

/-- Radical coordinate of
`(r + s * sqrt D) * (fundamentalPell D hD) ^ m`. -/
noncomputable def lowerNormTwoY
    (D : Nat) (hD : PellKernel D) (r s m : Nat) : Nat :=
  s * pellX D hD m + r * pellY D hD m

private theorem pellCoordinates_two_mul_add_one
    (D : Nat) (hD : PellKernel D) (m : Nat) :
    pellX D hD (2 * m + 1) =
        fundamentalX D hD *
            (pellX D hD m ^ 2 + D * pellY D hD m ^ 2) +
          2 * D * fundamentalY D hD *
            pellX D hD m * pellY D hD m ∧
      pellY D hD (2 * m + 1) =
        fundamentalY D hD *
            (pellX D hD m ^ 2 + D * pellY D hD m ^ 2) +
          2 * fundamentalX D hD *
            pellX D hD m * pellY D hD m := by
  constructor
  · have hInt :
        (pellSolution D hD (2 * m + 1)).x =
          (fundamentalX D hD : Int) *
              ((pellX D hD m : Int) ^ 2 +
                (D : Int) * (pellY D hD m : Int) ^ 2) +
            2 * (D : Int) * (fundamentalY D hD : Int) *
              (pellX D hD m : Int) * (pellY D hD m : Int) := by
      simp only [pellSolution]
      rw [show 2 * m + 1 = m + (m + 1) by omega,
        pow_add, pow_succ]
      simp only [Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
      rw [fundamentalX_intCast D hD, fundamentalY_intCast D hD,
        pellX_intCast D hD m, pellY_intCast D hD m]
      simp only [pellSolution]
      ring
    rw [← pellX_intCast D hD (2 * m + 1)] at hInt
    exact_mod_cast hInt
  · have hInt :
        (pellSolution D hD (2 * m + 1)).y =
          (fundamentalY D hD : Int) *
              ((pellX D hD m : Int) ^ 2 +
                (D : Int) * (pellY D hD m : Int) ^ 2) +
            2 * (fundamentalX D hD : Int) *
              (pellX D hD m : Int) * (pellY D hD m : Int) := by
      simp only [pellSolution]
      rw [show 2 * m + 1 = m + (m + 1) by omega,
        pow_add, pow_succ]
      simp only [Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
      rw [fundamentalX_intCast D hD, fundamentalY_intCast D hD,
        pellX_intCast D hD m, pellY_intCast D hD m]
      simp only [pellSolution]
      ring
    rw [← pellY_intCast D hD (2 * m + 1)] at hInt
    exact_mod_cast hInt

/-- The distinguished half-square orbit remains on the norm-minus-two
equation. -/
theorem lowerNormTwo_equation
    (D : Nat) (hD : PellKernel D) (r s m : Nat)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    lowerNormTwoX D hD r s m ^ 2 + 2 =
      D * lowerNormTwoY D hD r s m ^ 2 := by
  have hpell :=
    pellX_square_eq_one_add_mul_pellY_sq D hD m
  simp only [lowerNormTwoX, lowerNormTwoY]
  nlinarith

/-- Squaring a distinguished norm-minus-two orbit point and dividing by two
recovers the canonical odd Pell power at index `2m+1`. -/
theorem lowerNormTwo_square_coordinates
    (D : Nat) (hD : PellKernel D) (r s m : Nat)
    (hfundX : fundamentalX D hD = r ^ 2 + 1)
    (hfundY : fundamentalY D hD = r * s)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    pellX D hD (2 * m + 1) =
        lowerNormTwoX D hD r s m ^ 2 + 1 ∧
      pellY D hD (2 * m + 1) =
        lowerNormTwoX D hD r s m *
          lowerNormTwoY D hD r s m := by
  have hcoords := pellCoordinates_two_mul_add_one D hD m
  have hpell :=
    pellX_square_eq_one_add_mul_pellY_sq D hD m
  rw [hfundX, hfundY] at hcoords
  simp only [lowerNormTwoX, lowerNormTwoY]
  constructor
  · rw [hcoords.1]
    nlinarith
  · rw [hcoords.2]
    have hcoefficient :
        2 * (r ^ 2 + 1) = r ^ 2 + D * s ^ 2 := by
      nlinarith
    rw [hcoefficient]
    ring

private theorem normTwoSeed_r_odd
    {D : Nat} {hD : PellKernel D} {r : Nat}
    (hfundEven : Even (fundamentalX D hD))
    (hfundX : fundamentalX D hD = r ^ 2 + 1) :
    Odd r := by
  rw [← Nat.not_even_iff_odd]
  intro hrEven
  have hrSqEven : Even (r ^ 2) :=
    Nat.even_pow.mpr ⟨hrEven, by decide⟩
  have hfundOdd : Odd (fundamentalX D hD) := by
    rw [hfundX]
    exact hrSqEven.add_one
  exact hfundOdd.not_two_dvd_nat hfundEven.two_dvd

private theorem normTwoSeed_s_odd
    {D r s : Nat} (hrOdd : Odd r)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    Odd s := by
  rw [← Nat.not_even_iff_odd]
  intro hsEven
  have hsSqEven : Even (s ^ 2) :=
    Nat.even_pow.mpr ⟨hsEven, by decide⟩
  have hrightEven : Even (D * s ^ 2) :=
    hsSqEven.mul_left D
  have hleftOdd : Odd (r ^ 2 + 2) :=
    hrOdd.pow.add_even even_two
  rw [hseed] at hleftOdd
  exact hleftOdd.not_two_dvd_nat hrightEven.two_dvd

private theorem normTwoSeed_kernel_coprime_real
    {D r s : Nat} (hDOdd : Odd D)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    Nat.Coprime D r := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := D.gcd r
  have hgD : g ∣ D := Nat.gcd_dvd_left D r
  have hgr : g ∣ r := Nat.gcd_dvd_right D r
  have hgrSq : g ∣ r ^ 2 := dvd_pow hgr (by norm_num)
  have hgSum : g ∣ r ^ 2 + 2 := by
    rw [hseed]
    exact dvd_mul_of_dvd_left hgD (s ^ 2)
  have hgTwo : g ∣ 2 :=
    (Nat.dvd_add_iff_right hgrSq).mpr hgSum
  have hgOdd : Odd g := hDOdd.of_dvd_nat hgD
  have hgLe : g ≤ 2 := Nat.le_of_dvd (by decide) hgTwo
  rcases hgOdd with ⟨j, hj⟩
  omega

private theorem normTwoSeed_coordinates_coprime
    {D r s : Nat} (hrOdd : Odd r)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    Nat.Coprime r s := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := r.gcd s
  have hgr : g ∣ r := Nat.gcd_dvd_left r s
  have hgs : g ∣ s := Nat.gcd_dvd_right r s
  have hgrSq : g ∣ r ^ 2 := dvd_pow hgr (by norm_num)
  have hgsSq : g ∣ s ^ 2 := dvd_pow hgs (by norm_num)
  have hgSum : g ∣ r ^ 2 + 2 := by
    rw [hseed]
    exact dvd_mul_of_dvd_right hgsSq D
  have hgTwo : g ∣ 2 :=
    (Nat.dvd_add_iff_right hgrSq).mpr hgSum
  have hgOdd : Odd g := hrOdd.of_dvd_nat hgr
  have hgLe : g ≤ 2 := Nat.le_of_dvd (by decide) hgTwo
  rcases hgOdd with ⟨j, hj⟩
  omega

/-- The ramified source-depth rank can be read directly from the
norm-minus-two seed ordinate. -/
theorem pellRank_eq_kernel_div_gcd_normTwoSeed
    (D : Nat) (hD : PellKernel D) (r s : Nat)
    (hDOdd : Odd D)
    (hfundY : fundamentalY D hD = r * s)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    pellRank D hD = D / D.gcd s := by
  have hDr : Nat.Coprime D r :=
    normTwoSeed_kernel_coprime_real hDOdd hseed
  unfold pellRank
  rw [hfundY]
  rw [hDr.symm.gcd_mul_left_cancel_right s]

/-- Kernel divisibility on the norm-minus-two orbit is exactly divisibility
of the associated odd Pell index by the canonical Pell rank. -/
theorem lowerNormTwoY_dvd_iff_rank_dvd_oddIndex
    (D : Nat) (hD : PellKernel D) (r s m : Nat)
    (hDOdd : Odd D)
    (hfundX : fundamentalX D hD = r ^ 2 + 1)
    (hfundY : fundamentalY D hD = r * s)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    D ∣ lowerNormTwoY D hD r s m ↔
      pellRank D hD ∣ 2 * m + 1 := by
  have hcoords :=
    lowerNormTwo_square_coordinates
      D hD r s m hfundX hfundY hseed
  have hcop :
      Nat.Coprime D (lowerNormTwoX D hD r s m) :=
    normTwoSeed_kernel_coprime_real hDOdd
      (lowerNormTwo_equation D hD r s m hseed)
  rw [← D_dvd_pellY_iff_rank_dvd_index
    D hD (2 * m + 1), hcoords.2]
  constructor
  · intro hdiv
    exact dvd_mul_of_dvd_right hdiv _
  · intro hdiv
    exact hcop.dvd_of_dvd_mul_left hdiv

/-- Exact and unique natural parametrisation of the lower source-depth
subsequence.  The use of `R / 2` is boundary-safe at `R = 1`; for odd `R`
it is equal to `(R - 1) / 2`. -/
theorem lowerNormTwoY_dvd_iff_existsUnique_depth
    (D : Nat) (hD : PellKernel D) (r s m : Nat)
    (hDOdd : Odd D)
    (hfundX : fundamentalX D hD = r ^ 2 + 1)
    (hfundY : fundamentalY D hD = r * s)
    (hseed : r ^ 2 + 2 = D * s ^ 2) :
    D ∣ lowerNormTwoY D hD r s m ↔
      ∃! k : Nat,
        m = pellRank D hD * k + pellRank D hD / 2 := by
  let R := pellRank D hD
  have hRPos : 0 < R := by
    simpa [R] using pellRank_pos D hD
  have hROdd : Odd R := by
    simpa [R] using pellRank_odd_of_kernel_odd D hD hDOdd
  have hhalf : 2 * (R / 2) + 1 = R :=
    Nat.two_mul_div_two_add_one_of_odd hROdd
  have hformula :
      ∀ k : Nat, 2 * (R * k + R / 2) + 1 =
        R * (2 * k + 1) := by
    intro k
    calc
      2 * (R * k + R / 2) + 1 =
          2 * R * k + (2 * (R / 2) + 1) := by ring
      _ = 2 * R * k + R := by rw [hhalf]
      _ = R * (2 * k + 1) := by ring
  have hdepth :
      D ∣ lowerNormTwoY D hD r s m ↔ R ∣ 2 * m + 1 := by
    simpa [R] using
      lowerNormTwoY_dvd_iff_rank_dvd_oddIndex
        D hD r s m hDOdd hfundX hfundY hseed
  constructor
  · intro hdiv
    obtain ⟨k, hk, hunique⟩ :=
      (odd_dvd_iff_existsUnique_twice_mul_add_one
        hRPos hROdd).mp
        ⟨hdepth.mp hdiv, odd_two_mul_add_one m⟩
    refine ⟨k, ?_, ?_⟩
    · change m = R * k + R / 2
      have htwice :
          2 * m + 1 =
            2 * (R * k + R / 2) + 1 :=
        hk.trans (hformula k).symm
      omega
    · intro l hl
      change m = R * l + R / 2 at hl
      apply hunique l
      rw [hl]
      exact hformula l
  · rintro ⟨k, hk, _hunique⟩
    change m = R * k + R / 2 at hk
    apply hdepth.mpr
    refine ⟨2 * k + 1, ?_⟩
    rw [hk]
    exact hformula k

/-- The exact distinguished norm-minus-two term carried by an allocation.
Its doubled index is the canonical lower Pell index, and its two coordinates
are literally the allocated `y` and `D*z`. -/
theorem Sm2LowerSquareAllocation.lowerNormTwo_at_sourceDepth
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data)
    {r s : Nat}
    (hfundX :
      fundamentalX data.pell.D data.pell.kernel = r ^ 2 + 1)
    (hfundY :
      fundamentalY data.pell.D data.pell.kernel = r * s)
    (hseed : r ^ 2 + 2 = data.pell.D * s ^ 2) :
    let R := pellRank data.pell.D data.pell.kernel
    let m := R * data.pell.k + R / 2
    2 * m + 1 =
        canonicalPellIndex
          data.pell.D data.pell.kernel data.pell.k ∧
      lowerNormTwoX
          data.pell.D data.pell.kernel r s m =
        allocation.y ∧
      lowerNormTwoY
          data.pell.D data.pell.kernel r s m =
        data.pell.D * allocation.linearUpperSquarePart := by
  let R := pellRank data.pell.D data.pell.kernel
  let m := R * data.pell.k + R / 2
  have hROdd : Odd R := by
    simpa [R] using
      pellRank_odd_of_kernel_odd
        data.pell.D data.pell.kernel data.admissible.1
  have hhalf : 2 * (R / 2) + 1 = R :=
    Nat.two_mul_div_two_add_one_of_odd hROdd
  have hindex :
      2 * m + 1 =
        canonicalPellIndex
          data.pell.D data.pell.kernel data.pell.k := by
    change
      2 * (R * data.pell.k + R / 2) + 1 =
        R * (2 * data.pell.k + 1)
    calc
      2 * (R * data.pell.k + R / 2) + 1 =
          2 * R * data.pell.k + (2 * (R / 2) + 1) := by
        ring
      _ = 2 * R * data.pell.k + R := by rw [hhalf]
      _ = R * (2 * data.pell.k + 1) := by ring
  have hcenter := data.represents_center.2
  dsimp [canonicalPellCenter] at hcenter
  have hcoords :=
    lowerNormTwo_square_coordinates
      data.pell.D data.pell.kernel r s m
        hfundX hfundY hseed
  have hxAdd :
      lowerNormTwoX
            data.pell.D data.pell.kernel r s m ^ 2 + 1 =
        allocation.y ^ 2 + 1 := by
    calc
      lowerNormTwoX
            data.pell.D data.pell.kernel r s m ^ 2 + 1 =
          pellX data.pell.D data.pell.kernel (2 * m + 1) :=
        hcoords.1.symm
      _ =
          pellX data.pell.D data.pell.kernel
            (canonicalPellIndex
              data.pell.D data.pell.kernel data.pell.k) := by
        rw [hindex]
      _ = data.center := hcenter.symm
      _ = allocation.y ^ 2 + 1 := allocation.center_eq
  have hxSq :
      lowerNormTwoX
            data.pell.D data.pell.kernel r s m ^ 2 =
        allocation.y ^ 2 := by
    omega
  have hx :
      lowerNormTwoX
          data.pell.D data.pell.kernel r s m =
        allocation.y :=
    Nat.pow_left_injective (by decide : (2 : Nat) ≠ 0) hxSq
  have hnormOrbit :=
    lowerNormTwo_equation
      data.pell.D data.pell.kernel r s m hseed
  have hscaled :
      data.pell.D *
          lowerNormTwoY
            data.pell.D data.pell.kernel r s m ^ 2 =
        data.pell.D *
          (data.pell.D * allocation.linearUpperSquarePart) ^ 2 := by
    calc
      data.pell.D *
            lowerNormTwoY
              data.pell.D data.pell.kernel r s m ^ 2 =
          lowerNormTwoX
              data.pell.D data.pell.kernel r s m ^ 2 + 2 :=
        hnormOrbit.symm
      _ = allocation.y ^ 2 + 2 := by rw [hx]
      _ =
          allocation.linearUpperSquarePart ^ 2 *
            data.pell.D ^ 3 :=
        allocation.linearUpperNormalForm.2.2.1
      _ =
          data.pell.D *
            (data.pell.D * allocation.linearUpperSquarePart) ^ 2 := by
        ring
  have hySq :
      lowerNormTwoY
            data.pell.D data.pell.kernel r s m ^ 2 =
        (data.pell.D * allocation.linearUpperSquarePart) ^ 2 :=
    Nat.eq_of_mul_eq_mul_left
      (Nat.zero_lt_of_lt data.pell.kernel.1) hscaled
  have hy :
      lowerNormTwoY
          data.pell.D data.pell.kernel r s m =
        data.pell.D * allocation.linearUpperSquarePart :=
    Nat.pow_left_injective (by decide : (2 : Nat) ≠ 0) hySq
  exact ⟨hindex, hx, hy⟩

/-- Complete lower-orbit compiler for a hypothetical `sm2LowerSquare`
allocation.  Besides the literal source point, it records the exact seed
parity, coprimality, and ramified rank formula. -/
theorem Sm2LowerSquareAllocation.exists_exact_lowerNormTwoOrbit
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    ∃ r s : Nat,
      0 < r ∧
        0 < s ∧
          Odd r ∧
            Odd s ∧
              Nat.Coprime data.pell.D r ∧
                Nat.Coprime r s ∧
                  fundamentalX data.pell.D data.pell.kernel =
                    r ^ 2 + 1 ∧
                  fundamentalY data.pell.D data.pell.kernel =
                    r * s ∧
                  r ^ 2 + 2 = data.pell.D * s ^ 2 ∧
                  pellRank data.pell.D data.pell.kernel =
                    data.pell.D / data.pell.D.gcd s ∧
                  let R := pellRank data.pell.D data.pell.kernel
                  let m := R * data.pell.k + R / 2
                  2 * m + 1 =
                      canonicalPellIndex
                        data.pell.D data.pell.kernel data.pell.k ∧
                    lowerNormTwoX
                        data.pell.D data.pell.kernel r s m =
                      allocation.y ∧
                    lowerNormTwoY
                        data.pell.D data.pell.kernel r s m =
                      data.pell.D *
                        allocation.linearUpperSquarePart := by
  obtain ⟨r, s, hrPos, hsPos, hfundX, hseed, hfundY⟩ :=
    allocation.exists_lower_fundamental_normTwo
  have hrOdd : Odd r :=
    normTwoSeed_r_odd data.admissible.2 hfundX
  have hsOdd : Odd s :=
    normTwoSeed_s_odd hrOdd hseed
  have hDr : Nat.Coprime data.pell.D r :=
    normTwoSeed_kernel_coprime_real data.admissible.1 hseed
  have hrs : Nat.Coprime r s :=
    normTwoSeed_coordinates_coprime hrOdd hseed
  have hRank :
      pellRank data.pell.D data.pell.kernel =
        data.pell.D / data.pell.D.gcd s :=
    pellRank_eq_kernel_div_gcd_normTwoSeed
      data.pell.D data.pell.kernel r s
        data.admissible.1 hfundY hseed
  have hpoint :=
    allocation.lowerNormTwo_at_sourceDepth
      hfundX hfundY hseed
  exact
    ⟨r, s, hrPos, hsPos, hrOdd, hsOdd, hDr, hrs,
      hfundX, hfundY, hseed, hRank, hpoint⟩

/-- Selected exact lower norm-minus-two orbit attached to a complete
allocation. -/
structure Sm2LowerSquareLowerNormTwoOrbit
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) where
  r : Nat
  s : Nat
  r_pos : 0 < r
  s_pos : 0 < s
  r_odd : Odd r
  s_odd : Odd s
  kernel_coprime_r : Nat.Coprime data.pell.D r
  r_coprime_s : Nat.Coprime r s
  fundamentalX_eq :
    fundamentalX data.pell.D data.pell.kernel = r ^ 2 + 1
  fundamentalY_eq :
    fundamentalY data.pell.D data.pell.kernel = r * s
  normTwo_eq :
    r ^ 2 + 2 = data.pell.D * s ^ 2
  rank_eq :
    pellRank data.pell.D data.pell.kernel =
      data.pell.D / data.pell.D.gcd s
  sourcePoint :
    let R := pellRank data.pell.D data.pell.kernel
    let m := R * data.pell.k + R / 2
    2 * m + 1 =
        canonicalPellIndex
          data.pell.D data.pell.kernel data.pell.k ∧
      lowerNormTwoX
          data.pell.D data.pell.kernel r s m =
        allocation.y ∧
      lowerNormTwoY
          data.pell.D data.pell.kernel r s m =
        data.pell.D * allocation.linearUpperSquarePart

namespace Sm2LowerSquareAllocation

/-- Every allocation carries a complete exact lower norm-minus-two orbit. -/
theorem lowerNormTwoOrbit_nonempty
    {data : PairPellCounterexampleData}
    (allocation : Sm2LowerSquareAllocation data) :
    Nonempty (Sm2LowerSquareLowerNormTwoOrbit allocation) := by
  obtain
    ⟨r, s, hrPos, hsPos, hrOdd, hsOdd, hDr, hrs,
      hfundX, hfundY, hseed, hRank, hpoint⟩ :=
    allocation.exists_exact_lowerNormTwoOrbit
  exact
    ⟨{ r := r
       s := s
       r_pos := hrPos
       s_pos := hsPos
       r_odd := hrOdd
       s_odd := hsOdd
       kernel_coprime_r := hDr
       r_coprime_s := hrs
       fundamentalX_eq := hfundX
       fundamentalY_eq := hfundY
       normTwo_eq := hseed
       rank_eq := hRank
       sourcePoint := hpoint }⟩

end Sm2LowerSquareAllocation

/-- Exact L5 residual enriched with its selected lower source-depth orbit.
The complete previous residual is retained, so no upper-axis certificate or
same-centre information is forgotten. -/
structure Sm2LowerSquareLowerOrbitResidual
    (data : PairPellCounterexampleData) where
  residual : Sm2LowerSquareResidual data
  lowerOrbit :
    Nonempty
      (Sm2LowerSquareLowerNormTwoOrbit residual.allocation)

namespace Sm2LowerSquareResidual

/-- Every exact residual refines to the lower-orbit residual. -/
def toLowerOrbitResidual
    {data : PairPellCounterexampleData}
    (residual : Sm2LowerSquareResidual data) :
    Sm2LowerSquareLowerOrbitResidual data :=
  { residual := residual
    lowerOrbit := residual.allocation.lowerNormTwoOrbit_nonempty }

end Sm2LowerSquareResidual

/-- Exact source compiler after the complete lower norm-minus-two orbit has
been exposed.  Both directions retain the original canonical package and
represented centre. -/
theorem sm2LowerSquareSource_iff_exists_lowerOrbitResidual
    (X : Nat) :
    Sm2LowerSquareSource X ↔
      ∃ data : PairPellCounterexampleData,
        data.pell.Represents X ∧
          Nonempty (Sm2LowerSquareLowerOrbitResidual data) := by
  constructor
  · intro hsource
    obtain ⟨data, hrep, ⟨residual⟩⟩ :=
      (sm2LowerSquareSource_iff_exists_residual X).mp hsource
    exact
      ⟨data, hrep, ⟨residual.toLowerOrbitResidual⟩⟩
  · rintro ⟨data, hrep, ⟨orbitResidual⟩⟩
    apply (sm2LowerSquareSource_iff_exists_residual X).mpr
    exact ⟨data, hrep, ⟨orbitResidual.residual⟩⟩

end Erdos364
