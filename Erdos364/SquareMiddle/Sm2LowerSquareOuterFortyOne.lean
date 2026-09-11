import Erdos364.SquareMiddle.Sm2LowerSquareGeneratorRank

namespace Erdos364

open scoped jacobiSym

/-!
# The fixed-`41` factor-safe Jacobi transfer

This module formalizes the problem-private square-determinant transfer used
by the first fixed-`41` pseudo-remainder block.  It deliberately does not
introduce a public polynomial-Jacobi framework.
-/

private theorem outer41_qrSign_left_one
    {m n : Nat} (hm : m % 4 = 1) :
    qrSign m n = 1 := by
  rw [qrSign, ZMod.χ₄_nat_one_mod_four hm, jacobiSym.one_left]

private theorem outer41_qrSign_right_one
    {m n : Nat} (hm : Odd m) (hn : Odd n) (hn4 : n % 4 = 1) :
    qrSign m n = 1 := by
  rw [qrSign.symm hm hn, outer41_qrSign_left_one hn4]

private theorem outer41_qrSign_both_three
    {m n : Nat} (hm : m % 4 = 3) (hn : n % 4 = 3) :
    qrSign m n = -1 := by
  have hnOdd : Odd n :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hn)
  rw [qrSign, ZMod.χ₄_nat_three_mod_four hm,
    jacobiSym.at_neg_one hnOdd, ZMod.χ₄_nat_three_mod_four hn]

private theorem outer41_qrSign_restore
    {b X x g h b0 X0 x0 : Nat}
    (hb4 : b % 4 = 3) (hX4 : X % 4 = 1) (hx4 : x % 4 = 1)
    (hgOdd : Odd g) (hhOdd : Odd h)
    (hbfac : b = h * b0) (hXfac : X = h * X0)
    (hxfac : x = g * (h * x0)) :
    (qrSign X0 b0 * qrSign X0 x0 * qrSign x0 b0 *
        qrSign X0 g * qrSign x0 g * qrSign b0 g) *
      jacobiSym (g : Int) h =
      jacobiSym (-1 : Int) g * jacobiSym (-1 : Int) h *
        jacobiSym (h : Int) g := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hhOdd) with hh1 | hh3
  · rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hgOdd) with hg1 | hg3
    · have hb04 : b0 % 4 = 3 := by
        rw [hbfac, Nat.mul_mod, hh1] at hb4
        omega
      have hX04 : X0 % 4 = 1 := by
        rw [hXfac, Nat.mul_mod, hh1] at hX4
        omega
      have hx04 : x0 % 4 = 1 := by
        rw [hxfac] at hx4
        norm_num [Nat.mul_mod, hg1, hh1] at hx4
        omega
      have hb0Odd : Odd b0 :=
        Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hb04)
      have hx0Odd : Odd x0 :=
        Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hx04)
      rw [outer41_qrSign_left_one hX04,
        outer41_qrSign_left_one hX04,
        outer41_qrSign_left_one hx04,
        outer41_qrSign_left_one hX04,
        outer41_qrSign_left_one hx04,
        outer41_qrSign_right_one hb0Odd hgOdd hg1,
        jacobiSym.quadratic_reciprocity_one_mod_four hg1 hhOdd,
        jacobiSym.at_neg_one hgOdd,
        jacobiSym.at_neg_one hhOdd,
        ZMod.χ₄_nat_one_mod_four hg1,
        ZMod.χ₄_nat_one_mod_four hh1]
      ring
    · have hb04 : b0 % 4 = 3 := by
        rw [hbfac, Nat.mul_mod, hh1] at hb4
        omega
      have hX04 : X0 % 4 = 1 := by
        rw [hXfac, Nat.mul_mod, hh1] at hX4
        omega
      have hx04 : x0 % 4 = 3 := by
        rw [hxfac] at hx4
        norm_num [Nat.mul_mod, hg3, hh1] at hx4
        omega
      have hb0Odd : Odd b0 :=
        Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hb04)
      have hx0Odd : Odd x0 :=
        Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hx04)
      rw [outer41_qrSign_left_one hX04,
        outer41_qrSign_left_one hX04,
        outer41_qrSign_both_three hx04 hb04,
        outer41_qrSign_left_one hX04,
        outer41_qrSign_both_three hx04 hg3,
        outer41_qrSign_both_three hb04 hg3,
        jacobiSym.quadratic_reciprocity_one_mod_four hh1 hgOdd,
        jacobiSym.at_neg_one hgOdd,
        jacobiSym.at_neg_one hhOdd,
        ZMod.χ₄_nat_three_mod_four hg3,
        ZMod.χ₄_nat_one_mod_four hh1]
      ring
  · rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hgOdd) with hg1 | hg3
    · have hb04 : b0 % 4 = 1 := by
        rw [hbfac, Nat.mul_mod, hh3] at hb4
        omega
      have hX04 : X0 % 4 = 3 := by
        rw [hXfac, Nat.mul_mod, hh3] at hX4
        omega
      have hx04 : x0 % 4 = 3 := by
        rw [hxfac] at hx4
        norm_num [Nat.mul_mod, hg1, hh3] at hx4
        omega
      have hX0Odd : Odd X0 :=
        Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hX04)
      have hx0Odd : Odd x0 :=
        Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hx04)
      rw [outer41_qrSign_right_one hX0Odd
          (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hb04)) hb04,
        outer41_qrSign_both_three hX04 hx04,
        outer41_qrSign_right_one hx0Odd
          (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hb04)) hb04,
        outer41_qrSign_right_one hX0Odd hgOdd hg1,
        outer41_qrSign_right_one hx0Odd hgOdd hg1,
        outer41_qrSign_left_one hb04,
        jacobiSym.quadratic_reciprocity_one_mod_four hg1 hhOdd,
        jacobiSym.at_neg_one hgOdd,
        jacobiSym.at_neg_one hhOdd,
        ZMod.χ₄_nat_one_mod_four hg1,
        ZMod.χ₄_nat_three_mod_four hh3]
      ring
    · have hb04 : b0 % 4 = 1 := by
        rw [hbfac, Nat.mul_mod, hh3] at hb4
        omega
      have hX04 : X0 % 4 = 3 := by
        rw [hXfac, Nat.mul_mod, hh3] at hX4
        omega
      have hx04 : x0 % 4 = 1 := by
        rw [hxfac] at hx4
        norm_num [Nat.mul_mod, hg3, hh3] at hx4
        omega
      have hX0Odd : Odd X0 :=
        Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hX04)
      have hgSwap :=
        jacobiSym.quadratic_reciprocity_three_mod_four hg3 hh3
      rw [outer41_qrSign_right_one hX0Odd
          (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hb04)) hb04,
        outer41_qrSign_right_one hX0Odd
          (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hx04)) hx04,
        outer41_qrSign_left_one hx04,
        outer41_qrSign_both_three hX04 hg3,
        outer41_qrSign_left_one hx04,
        outer41_qrSign_left_one hb04,
        hgSwap,
        jacobiSym.at_neg_one hgOdd,
        jacobiSym.at_neg_one hhOdd,
        ZMod.χ₄_nat_three_mod_four hg3,
        ZMod.χ₄_nat_three_mod_four hh3]
      ring

private theorem outer41_reduced_jacobi_transfer
    {A b X Y x y g s : Nat}
    (hbOdd : Odd b) (hXOdd : Odd X) (hxOdd : Odd x) (hgOdd : Odd g)
    (hAb : Nat.Coprime A b) (hbX : Nat.Coprime b X)
    (hbx : Nat.Coprime b x) (hgX : Nat.Coprime g X)
    (hgb : Nat.Coprime g b) (hgXsmall : Nat.Coprime g x)
    (hsx : Nat.Coprime s x)
    (hrowX : Int.ModEq X
      ((4 : Int) * (g : Int) * x) ((b : Int) * Y))
    (hrowB : Int.ModEq b
      ((4 : Int) * (g : Int) * x) (-(A : Int) * X))
    (hcross : Int.ModEq x
      ((b : Int) * y) ((g : Int) * (s : Int) ^ 2 * X)) :
    jacobiSym (Y : Int) X =
      (qrSign X b * qrSign X x * qrSign x b *
        qrSign X g * qrSign x g * qrSign b g) *
      jacobiSym (-(A : Int)) b *
      jacobiSym (b * X * x : Int) g *
      jacobiSym (y : Int) x := by
  have hAbInt : Int.gcd (-(A : Int)) b = 1 := by
    rw [Int.gcd_def, Int.natAbs_neg, Int.natAbs_natCast]
    exact hAb.gcd_eq_one
  have hbXInt : Int.gcd (b : Int) X = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hbX.gcd_eq_one
  have hbxInt : Int.gcd (b : Int) x = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hbx.gcd_eq_one
  have hgXInt : Int.gcd (g : Int) X = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hgX.gcd_eq_one
  have hgbInt : Int.gcd (g : Int) b = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hgb.gcd_eq_one
  have hgXsmallInt : Int.gcd (g : Int) x = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hgXsmall.gcd_eq_one
  have hsxInt : Int.gcd (s : Int) x = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hsx.gcd_eq_one
  have hE1 :
      jacobiSym (g : Int) X * jacobiSym (x : Int) X =
        jacobiSym (b : Int) X * jacobiSym (Y : Int) X := by
    calc
      jacobiSym (g : Int) X * jacobiSym (x : Int) X =
          jacobiSym ((g : Int) * x) X := by
            rw [jacobiSym.mul_left]
      _ = jacobiSym ((4 : Int) * ((g : Int) * x)) X := by
        symm
        rw [jacobiSym.mul_left, jacobiSym.at_four hXOdd, one_mul]
      _ = jacobiSym ((4 : Int) * (g : Int) * x) X := by rw [mul_assoc]
      _ = jacobiSym ((b : Int) * Y) X :=
        jacobiSym.mod_left' hrowX.eq
      _ = jacobiSym (b : Int) X * jacobiSym (Y : Int) X := by
        rw [jacobiSym.mul_left]
  have hE2 :
      jacobiSym (b : Int) x * jacobiSym (y : Int) x =
        jacobiSym (g : Int) x * jacobiSym (X : Int) x := by
    calc
      jacobiSym (b : Int) x * jacobiSym (y : Int) x =
          jacobiSym ((b : Int) * y) x := by
            rw [jacobiSym.mul_left]
      _ = jacobiSym ((g : Int) * (s : Int) ^ 2 * X) x :=
        jacobiSym.mod_left' hcross.eq
      _ = jacobiSym (g : Int) x *
          (jacobiSym ((s : Int) ^ 2) x * jacobiSym (X : Int) x) := by
            rw [jacobiSym.mul_left, jacobiSym.mul_left]
            ring
      _ = jacobiSym (g : Int) x * jacobiSym (X : Int) x := by
        rw [jacobiSym.sq_one' hsxInt, one_mul]
  have hE3 :
      jacobiSym (g : Int) b * jacobiSym (x : Int) b =
        jacobiSym (-(A : Int)) b * jacobiSym (X : Int) b := by
    calc
      jacobiSym (g : Int) b * jacobiSym (x : Int) b =
          jacobiSym ((g : Int) * x) b := by
            rw [jacobiSym.mul_left]
      _ = jacobiSym ((4 : Int) * ((g : Int) * x)) b := by
        symm
        rw [jacobiSym.mul_left, jacobiSym.at_four hbOdd, one_mul]
      _ = jacobiSym ((4 : Int) * (g : Int) * x) b := by rw [mul_assoc]
      _ = jacobiSym (-(A : Int) * X) b :=
        jacobiSym.mod_left' hrowB.eq
      _ = jacobiSym (-(A : Int)) b * jacobiSym (X : Int) b := by
        rw [jacobiSym.mul_left]
  have hYX :
      jacobiSym (Y : Int) X =
        jacobiSym (b : Int) X * jacobiSym (g : Int) X *
          jacobiSym (x : Int) X := by
    have hsquare := jacobiSym.sq_one hbXInt
    calc
      jacobiSym (Y : Int) X =
          jacobiSym (b : Int) X ^ 2 * jacobiSym (Y : Int) X := by
            rw [hsquare, one_mul]
      _ = jacobiSym (b : Int) X *
          (jacobiSym (b : Int) X * jacobiSym (Y : Int) X) := by ring
      _ = jacobiSym (b : Int) X *
          (jacobiSym (g : Int) X * jacobiSym (x : Int) X) := by
            rw [← hE1]
      _ = _ := by ring
  have hXx :
      jacobiSym (X : Int) x =
        jacobiSym (g : Int) x * jacobiSym (b : Int) x *
          jacobiSym (y : Int) x := by
    have hsquare := jacobiSym.sq_one hgXsmallInt
    calc
      jacobiSym (X : Int) x =
          jacobiSym (g : Int) x ^ 2 * jacobiSym (X : Int) x := by
            rw [hsquare, one_mul]
      _ = jacobiSym (g : Int) x *
          (jacobiSym (g : Int) x * jacobiSym (X : Int) x) := by ring
      _ = jacobiSym (g : Int) x *
          (jacobiSym (b : Int) x * jacobiSym (y : Int) x) := by
            rw [← hE2]
      _ = _ := by ring
  have hXb :
      jacobiSym (X : Int) b =
        jacobiSym (-(A : Int)) b * jacobiSym (g : Int) b *
          jacobiSym (x : Int) b := by
    have hsquare := jacobiSym.sq_one hAbInt
    calc
      jacobiSym (X : Int) b =
          jacobiSym (-(A : Int)) b ^ 2 * jacobiSym (X : Int) b := by
            rw [hsquare, one_mul]
      _ = jacobiSym (-(A : Int)) b *
          (jacobiSym (-(A : Int)) b * jacobiSym (X : Int) b) := by ring
      _ = jacobiSym (-(A : Int)) b *
          (jacobiSym (g : Int) b * jacobiSym (x : Int) b) := by
            rw [← hE3]
      _ = _ := by ring
  have hxbInt : Int.gcd (x : Int) b = 1 := by
    rw [Int.gcd_comm]
    exact hbxInt
  have hxbSquare := jacobiSym.sq_one hxbInt
  have hproduct :
      jacobiSym (b : Int) g * jacobiSym (X : Int) g *
          jacobiSym (x : Int) g =
        jacobiSym (b * X * x : Int) g := by
    calc
      jacobiSym (b : Int) g * jacobiSym (X : Int) g *
          jacobiSym (x : Int) g =
          jacobiSym ((b : Int) * X) g * jacobiSym (x : Int) g := by
            exact congrArg (fun z : Int => z * jacobiSym (x : Int) g)
              (jacobiSym.mul_left (b : Int) (X : Int) g).symm
      _ = jacobiSym (((b : Int) * X) * x) g := by
        exact (jacobiSym.mul_left ((b : Int) * X) (x : Int) g).symm
      _ = jacobiSym (b * X * x : Int) g := by norm_num
  rw [hYX,
    jacobiSym.quadratic_reciprocity' hbOdd hXOdd,
    jacobiSym.quadratic_reciprocity' hxOdd hXOdd,
    hXb, hXx,
    jacobiSym.quadratic_reciprocity' hbOdd hxOdd,
    jacobiSym.quadratic_reciprocity' hgOdd hXOdd,
    jacobiSym.quadratic_reciprocity' hgOdd hxOdd,
    jacobiSym.quadratic_reciprocity' hgOdd hbOdd]
  calc
    _ =
        (qrSign X b * qrSign X x * qrSign x b *
          qrSign X g * qrSign x g * qrSign b g) *
        jacobiSym (-(A : Int)) b *
        (jacobiSym (b : Int) g * jacobiSym (X : Int) g *
          jacobiSym (x : Int) g) *
        jacobiSym (y : Int) x * jacobiSym (x : Int) b ^ 2 := by ring
    _ =
        (qrSign X b * qrSign X x * qrSign x b *
          qrSign X g * qrSign x g * qrSign b g) *
        jacobiSym (-(A : Int)) b *
        (jacobiSym (b : Int) g * jacobiSym (X : Int) g *
          jacobiSym (x : Int) g) *
        jacobiSym (y : Int) x := by rw [hxbSquare, mul_one]
    _ = _ := by rw [hproduct]

/-- A factor-safe cross transfer for one fixed-`41` coefficient-descent link.

The common factor `h` is kept in the formula instead of being cancelled
inside a Jacobi symbol.  This is the reusable kernel needed before any
link-specific squareclass simplification.  In particular, `r` may be even.
-/
theorem ss41_crossJacobiTransfer
    {P Q p q h Q0 q0 : Nat} (r : Int)
    (hhpos : 0 < h) (hQ0pos : 0 < Q0) (hq0pos : 0 < q0)
    (hQ0Odd : Odd Q0) (hq0Odd : Odd q0)
    (hQfac : Q = h * Q0) (hqfac : q = h * q0)
    (hph : Nat.Coprime p h)
    (hQ0q0 : Nat.Coprime Q0 q0)
    (hrq0 : Int.gcd r q0 = 1)
    (hcross : (h : Int) * r =
      (p : Int) * Q - (q : Int) * P) :
    jacobiSym (P : Int) Q =
      qrSign Q0 q0 *
        jacobiSym (P : Int) h * jacobiSym (p : Int) h *
        jacobiSym (-r) Q0 * jacobiSym r q0 *
        jacobiSym (p : Int) q := by
  have hhne : h ≠ 0 := hhpos.ne'
  have hQ0ne : Q0 ≠ 0 := hQ0pos.ne'
  have hq0ne : q0 ≠ 0 := hq0pos.ne'
  have hhInt : (h : Int) ≠ 0 := by exact_mod_cast hhne
  have hQfacInt : (Q : Int) = (h : Int) * Q0 := by
    exact_mod_cast hQfac
  have hqfacInt : (q : Int) = (h : Int) * q0 := by
    exact_mod_cast hqfac
  have hcrossRed : r = (p : Int) * Q0 - (q0 : Int) * P := by
    apply mul_left_cancel₀ hhInt
    calc
      (h : Int) * r = (p : Int) * Q - (q : Int) * P := hcross
      _ = (h : Int) * ((p : Int) * Q0 - (q0 : Int) * P) := by
        rw [hQfacInt, hqfacInt]
        ring
  have hminusMod : Int.ModEq Q0 (-r) ((q0 : Int) * P) := by
    rw [Int.modEq_iff_dvd]
    use (p : Int)
    rw [hcrossRed]
    ring
  have hplusMod : Int.ModEq q0 r ((p : Int) * Q0) := by
    rw [Int.modEq_iff_dvd]
    use (P : Int)
    rw [hcrossRed]
    ring
  have hq0Q0Int : Int.gcd (q0 : Int) Q0 = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hQ0q0.symm.gcd_eq_one
  have hQ0q0Int : Int.gcd (Q0 : Int) q0 = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hQ0q0.gcd_eq_one
  have hphInt : Int.gcd (p : Int) h = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hph.gcd_eq_one
  have hminus :
      jacobiSym (P : Int) Q0 =
        jacobiSym (-r) Q0 * jacobiSym (q0 : Int) Q0 := by
    have hsquare := jacobiSym.sq_one hq0Q0Int
    have hmod := jacobiSym.mod_left' hminusMod
    calc
      jacobiSym (P : Int) Q0 =
          jacobiSym (q0 : Int) Q0 ^ 2 * jacobiSym (P : Int) Q0 := by
            rw [hsquare, one_mul]
      _ = jacobiSym (q0 : Int) Q0 *
          jacobiSym ((q0 : Int) * P) Q0 := by
            rw [jacobiSym.mul_left]
            ring
      _ = jacobiSym (q0 : Int) Q0 * jacobiSym (-r) Q0 := by
            rw [hmod]
      _ = _ := by ring
  have hplus :
      jacobiSym (p : Int) q0 =
        jacobiSym r q0 * jacobiSym (Q0 : Int) q0 := by
    have hsquare := jacobiSym.sq_one hQ0q0Int
    have hmod := jacobiSym.mod_left' hplusMod
    calc
      jacobiSym (p : Int) q0 =
          jacobiSym (Q0 : Int) q0 ^ 2 * jacobiSym (p : Int) q0 := by
            rw [hsquare, one_mul]
      _ = jacobiSym (Q0 : Int) q0 *
          jacobiSym ((p : Int) * Q0) q0 := by
            rw [jacobiSym.mul_left]
            ring
      _ = jacobiSym (Q0 : Int) q0 * jacobiSym r q0 := by
            rw [hmod]
      _ = _ := by ring
  have hPsplit :
      jacobiSym (P : Int) Q =
        jacobiSym (P : Int) h * jacobiSym (P : Int) Q0 := by
    rw [hQfac, jacobiSym.mul_right' (P : Int) hhne hQ0ne]
  have hpsplit :
      jacobiSym (p : Int) q =
        jacobiSym (p : Int) h * jacobiSym (p : Int) q0 := by
    rw [hqfac, jacobiSym.mul_right' (p : Int) hhne hq0ne]
  have hpRecover :
      jacobiSym (p : Int) q0 =
        jacobiSym (p : Int) h * jacobiSym (p : Int) q := by
    have hsquare := jacobiSym.sq_one hphInt
    calc
      jacobiSym (p : Int) q0 =
          jacobiSym (p : Int) h ^ 2 * jacobiSym (p : Int) q0 := by
            rw [hsquare, one_mul]
      _ = jacobiSym (p : Int) h *
          (jacobiSym (p : Int) h * jacobiSym (p : Int) q0) := by ring
      _ = _ := by rw [← hpsplit]
  have hQRecover :
      jacobiSym (Q0 : Int) q0 =
        jacobiSym r q0 * jacobiSym (p : Int) q0 := by
    have hsquare := jacobiSym.sq_one hrq0
    calc
      jacobiSym (Q0 : Int) q0 =
          jacobiSym r q0 ^ 2 * jacobiSym (Q0 : Int) q0 := by
            rw [hsquare, one_mul]
      _ = jacobiSym r q0 *
          (jacobiSym r q0 * jacobiSym (Q0 : Int) q0) := by ring
      _ = _ := by rw [← hplus]
  rw [hPsplit, hminus,
    jacobiSym.quadratic_reciprocity' hq0Odd hQ0Odd,
    hQRecover, hpRecover]
  ring

/-- The correction layer for a factored endpoint row.

After writing the common denominator factor as `h = e * h0`, the concrete
endpoint identity is used only through
`p * t0 = Delta0 * P (mod h0)`.  The two explicit gcd hypotheses are exactly
the square cancellations performed by the proof. -/
theorem ss41_endpointFactorCorrection
    {P p e h0 h : Nat} (t0 Delta0 : Int)
    (hepos : 0 < e) (hh0pos : 0 < h0)
    (hhfac : h = e * h0)
    (hph0 : Int.gcd (p : Int) h0 = 1)
    (hDeltah0 : Int.gcd Delta0 h0 = 1)
    (hendpoint : Int.ModEq h0
      ((p : Int) * t0) (Delta0 * P)) :
    jacobiSym (P : Int) h * jacobiSym (p : Int) h =
      jacobiSym (P : Int) e * jacobiSym (p : Int) e *
      jacobiSym t0 h0 * jacobiSym Delta0 h0 := by
  have hene : e ≠ 0 := hepos.ne'
  have hh0ne : h0 ≠ 0 := hh0pos.ne'
  have hmod :
      jacobiSym (p : Int) h0 * jacobiSym t0 h0 =
        jacobiSym Delta0 h0 * jacobiSym (P : Int) h0 := by
    have h := jacobiSym.mod_left' hendpoint
    simpa [jacobiSym.mul_left] using h
  have hpSquare := jacobiSym.sq_one hph0
  have hDeltaSquare := jacobiSym.sq_one hDeltah0
  have hcorrection :
      jacobiSym (P : Int) h0 * jacobiSym (p : Int) h0 =
        jacobiSym t0 h0 * jacobiSym Delta0 h0 := by
    calc
      jacobiSym (P : Int) h0 * jacobiSym (p : Int) h0 =
          jacobiSym Delta0 h0 ^ 2 *
            (jacobiSym (P : Int) h0 * jacobiSym (p : Int) h0) := by
              rw [hDeltaSquare, one_mul]
      _ = (jacobiSym Delta0 h0 * jacobiSym (P : Int) h0) *
          (jacobiSym (p : Int) h0 * jacobiSym Delta0 h0) := by ring
      _ = (jacobiSym (p : Int) h0 * jacobiSym t0 h0) *
          (jacobiSym (p : Int) h0 * jacobiSym Delta0 h0) := by
            rw [← hmod]
      _ = jacobiSym (p : Int) h0 ^ 2 *
          (jacobiSym t0 h0 * jacobiSym Delta0 h0) := by ring
      _ = _ := by rw [hpSquare, one_mul]
  rw [hhfac,
    jacobiSym.mul_right' (P : Int) hene hh0ne,
    jacobiSym.mul_right' (p : Int) hene hh0ne]
  calc
    jacobiSym (P : Int) e * jacobiSym (P : Int) h0 *
        (jacobiSym (p : Int) e * jacobiSym (p : Int) h0) =
        jacobiSym (P : Int) e * jacobiSym (p : Int) e *
          (jacobiSym (P : Int) h0 * jacobiSym (p : Int) h0) := by ring
    _ = _ := by rw [hcorrection]; ring

/-- The factor-safe square-determinant transfer for the first fixed-`41`
pseudo-remainder block.  The name and interface are problem-specific; the
lower-level Jacobi machinery remains file-private. -/
theorem ss41_squareDetJacobiTransfer
    {A b c D S g s X Y x y xp yp : Nat}
    (_hA4 : A % 4 = 1) (hb4 : b % 4 = 3)
    (hX4 : X % 4 = 1) (_hY4 : Y % 4 = 3)
    (hx4 : x % 4 = 1) (_hy4 : y % 4 = 3)
    (hgpos : 0 < g)
    (hxfac : x = g * xp) (hyfac : y = g * yp)
    (hSfac : S = g * s)
    (hAb : Nat.Coprime A b) (_hXY : Nat.Coprime X Y)
    (hxpyp : Nat.Coprime xp yp)
    (hgprod : Nat.Coprime g (A * b * X * Y))
    (hsxp : Nat.Coprime s xp)
    (hrow0 : 4 * x + A * X = b * Y)
    (hrow1 : y + D * Y = c * X)
    (hdet : b * c = A * D + S ^ 2) :
    jacobiSym (Y : Int) X =
      jacobiSym (-1 : Int) g *
      jacobiSym (-(A : Int)) b *
      jacobiSym (b * X * xp : Int) g *
      jacobiSym (yp : Int) xp := by
  have hbOdd : Odd b :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hb4)
  have hXOdd : Odd X :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hX4)
  have hxOdd : Odd x :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hx4)
  have hgb : Nat.Coprime g b := by
    apply hgprod.of_dvd_right
    use A * X * Y
    ring
  have hgX : Nat.Coprime g X := by
    apply hgprod.of_dvd_right
    use A * b * Y
    ring
  have hgOdd : Odd g := by
    rw [hxfac] at hxOdd
    exact (Nat.odd_mul.mp hxOdd).1
  have hxpOdd : Odd xp := by
    rw [hxfac] at hxOdd
    exact (Nat.odd_mul.mp hxOdd).2
  have hcrossNat : b * y + 4 * D * x = S ^ 2 * X := by
    have hr0 :
        (4 : Int) * x + A * X = b * Y := by exact_mod_cast hrow0
    have hr1 :
        (y : Int) + D * Y = c * X := by exact_mod_cast hrow1
    have hd :
        (b : Int) * c = A * D + S ^ 2 := by exact_mod_cast hdet
    have hc :
        (b : Int) * y + 4 * D * x = S ^ 2 * X := by
      linear_combination (b : Int) * hr1 + (D : Int) * hr0 + (X : Int) * hd
    exact_mod_cast hc
  have hcrossDiv : b * yp + 4 * D * xp = g * s ^ 2 * X := by
    apply Nat.mul_left_cancel hgpos
    calc
      g * (b * yp + 4 * D * xp) = b * y + 4 * D * x := by
        rw [hxfac, hyfac]
        ring
      _ = S ^ 2 * X := hcrossNat
      _ = g * (g * s ^ 2 * X) := by
        rw [hSfac]
        ring
  have hgxp : Nat.Coprime g xp := by
    apply Nat.coprime_of_dvd'
    intro p _ hpg hpxp
    have hpRhs : p ∣ g * s ^ 2 * X :=
      by simpa [mul_assoc] using dvd_mul_of_dvd_left hpg (s ^ 2 * X)
    have hpSecond : p ∣ 4 * D * xp :=
      dvd_mul_of_dvd_right hpxp _
    have hpSum : p ∣ b * yp + 4 * D * xp := by
      rw [hcrossDiv]
      exact hpRhs
    have hpByp : p ∣ b * yp :=
      (Nat.dvd_add_iff_left hpSecond).mpr hpSum
    have hpb : Nat.Coprime p b := hgb.of_dvd_left hpg
    have hpyp : p ∣ yp := hpb.dvd_of_dvd_mul_left hpByp
    rw [← hxpyp.gcd_eq_one]
    exact Nat.dvd_gcd hpxp hpyp
  let h := Nat.gcd b X
  let b0 := b / h
  let X0 := X / h
  let x0 := xp / h
  have hhpos : 0 < h := Nat.gcd_pos_of_pos_left X hbOdd.pos
  have hhOdd : Odd h :=
    Odd.of_dvd_nat hbOdd (Nat.gcd_dvd_left b X)
  have hhb : h ∣ b := Nat.gcd_dvd_left b X
  have hhX : h ∣ X := Nat.gcd_dvd_right b X
  have hbfac : b = h * b0 := by
    dsimp [b0]
    exact (Nat.mul_div_cancel' hhb).symm
  have hXfac : X = h * X0 := by
    dsimp [X0]
    exact (Nat.mul_div_cancel' hhX).symm
  have hhg : Nat.Coprime h g :=
    (hgb.of_dvd_right hhb).symm
  have hhAX : h ∣ A * X := dvd_mul_of_dvd_right hhX A
  have hhBY : h ∣ b * Y := dvd_mul_of_dvd_left hhb Y
  have hhSum : h ∣ 4 * x + A * X := by
    rw [hrow0]
    exact hhBY
  have hh4x : h ∣ 4 * x :=
    (Nat.dvd_add_iff_left hhAX).mpr hhSum
  have hh4 : Nat.Coprime h 4 := by
    simpa [show (4 : Nat) = 2 ^ 2 by decide] using
      hhOdd.coprime_two_right.pow_right 2
  have hh4g : Nat.Coprime h (4 * g) := hh4.mul_right hhg
  have hhxp : h ∣ xp := by
    apply hh4g.dvd_of_dvd_mul_left
    rw [hxfac] at hh4x
    simpa [mul_assoc] using hh4x
  have hxpfac : xp = h * x0 := by
    dsimp [x0]
    exact (Nat.mul_div_cancel' hhxp).symm
  have hx0Odd : Odd x0 := by
    rw [hxpfac] at hxpOdd
    exact (Nat.odd_mul.mp hxpOdd).2
  have hb0Odd : Odd b0 := by
    rw [hbfac] at hbOdd
    exact (Nat.odd_mul.mp hbOdd).2
  have hX0Odd : Odd X0 := by
    rw [hXfac] at hXOdd
    exact (Nat.odd_mul.mp hXOdd).2
  have hb0X0 : Nat.Coprime b0 X0 := by
    dsimp [b0, X0, h]
    exact Nat.coprime_div_gcd_div_gcd hhpos
  have hAb0 : Nat.Coprime A b0 := by
    apply hAb.of_dvd_right
    use h
    rw [hbfac]
    ring
  have hgb0 : Nat.Coprime g b0 := by
    apply hgb.of_dvd_right
    use h
    rw [hbfac]
    ring
  have hgX0 : Nat.Coprime g X0 := by
    apply hgX.of_dvd_right
    use h
    rw [hXfac]
    ring
  have hgx0 : Nat.Coprime g x0 := by
    apply hgxp.of_dvd_right
    use h
    rw [hxpfac]
    ring
  have hsx0 : Nat.Coprime s x0 := by
    apply hsxp.of_dvd_right
    use h
    rw [hxpfac]
    ring
  have hrow0Red : 4 * g * x0 + A * X0 = b0 * Y := by
    apply Nat.mul_left_cancel hhpos
    calc
      h * (4 * g * x0 + A * X0) = 4 * x + A * X := by
        rw [hxfac, hxpfac, hXfac]
        ring
      _ = b * Y := hrow0
      _ = h * (b0 * Y) := by rw [hbfac]; ring
  have hcrossRed : b0 * yp + 4 * D * x0 = g * s ^ 2 * X0 := by
    apply Nat.mul_left_cancel hhpos
    calc
      h * (b0 * yp + 4 * D * x0) =
          b * yp + 4 * D * xp := by
            rw [hbfac, hxpfac]
            ring
      _ = g * s ^ 2 * X := hcrossDiv
      _ = h * (g * s ^ 2 * X0) := by rw [hXfac]; ring
  have hb0x0 : Nat.Coprime b0 x0 := by
    apply Nat.coprime_of_dvd'
    intro p _ hpb0 hpx0
    have hpB0Y : p ∣ b0 * Y := dvd_mul_of_dvd_left hpb0 Y
    have hpFirst : p ∣ 4 * g * x0 :=
      dvd_mul_of_dvd_right hpx0 _
    have hpSum : p ∣ 4 * g * x0 + A * X0 := by
      rw [hrow0Red]
      exact hpB0Y
    have hpAX0 : p ∣ A * X0 :=
      (Nat.dvd_add_iff_right hpFirst).mpr hpSum
    have hpb : p ∣ b := by
      exact hpb0.trans (by use h; rw [hbfac]; ring)
    have hpA : Nat.Coprime p A := hAb.symm.of_dvd_left hpb
    have hpX0 : p ∣ X0 := hpA.dvd_of_dvd_mul_left hpAX0
    rw [← hb0X0.gcd_eq_one]
    exact Nat.dvd_gcd hpb0 hpX0
  have hrowXMod : Int.ModEq X0
      ((4 : Int) * (g : Int) * x0) ((b0 : Int) * Y) := by
    rw [Int.modEq_iff_dvd]
    use (A : Int)
    have hr :
        (4 : Int) * g * x0 + A * X0 = b0 * Y := by
      exact_mod_cast hrow0Red
    calc
      (b0 : Int) * Y - 4 * g * x0 = A * X0 := by
        rw [← hr]
        ring
      _ = (X0 : Int) * A := by ring
  have hrowBMod : Int.ModEq b0
      ((4 : Int) * (g : Int) * x0) (-(A : Int) * X0) := by
    rw [Int.modEq_iff_dvd]
    use -(Y : Int)
    have hr :
        (4 : Int) * g * x0 + A * X0 = b0 * Y := by
      exact_mod_cast hrow0Red
    calc
      -(A : Int) * X0 - 4 * g * x0 =
          -((4 : Int) * g * x0 + A * X0) := by ring
      _ = -(b0 * Y) := by rw [hr]
      _ = (b0 : Int) * (-(Y : Int)) := by ring
  have hcrossMod : Int.ModEq x0
      ((b0 : Int) * yp) ((g : Int) * (s : Int) ^ 2 * X0) := by
    rw [Int.modEq_iff_dvd]
    use (4 : Int) * D
    have hr :
        (b0 : Int) * yp + 4 * D * x0 = g * s ^ 2 * X0 := by
      exact_mod_cast hcrossRed
    calc
      (g : Int) * s ^ 2 * X0 - b0 * yp = 4 * D * x0 := by
        rw [← hr]
        ring
      _ = (x0 : Int) * ((4 : Int) * D) := by ring
  have hred := outer41_reduced_jacobi_transfer
    hb0Odd hX0Odd hx0Odd hgOdd hAb0 hb0X0 hb0x0 hgX0 hgb0 hgx0 hsx0
    hrowXMod hrowBMod hcrossMod
  have hhyp : Nat.Coprime h yp :=
    hxpyp.of_dvd_left hhxp
  have hhA : Nat.Coprime h A :=
    hAb.symm.of_dvd_left hhb
  have hhs : Nat.Coprime h s :=
    (hsxp.of_dvd_right hhxp).symm
  have hhS : Nat.Coprime h S := by
    rw [hSfac]
    exact hhg.mul_right hhs
  have hrowHMod : Int.ModEq h
      ((g : Int) * yp) (-(D : Int) * Y) := by
    rw [Int.modEq_iff_dvd]
    use -((c : Int) * X0)
    have hr : (yp : Int) * g + D * Y = c * (h * X0) := by
      have hr0 : (y : Int) + D * Y = c * X := by
        exact_mod_cast hrow1
      rw [hyfac, hXfac] at hr0
      simpa [mul_comm, mul_left_comm, mul_assoc] using hr0
    calc
      -(D : Int) * Y - g * yp = -((yp : Int) * g + D * Y) := by
        ring
      _ = -(c * (h * X0)) := by rw [hr]
      _ = (h : Int) * (-((c : Int) * X0)) := by ring
  have hdetHMod : Int.ModEq h
      ((A : Int) * D) (-(S : Int) ^ 2) := by
    rw [Int.modEq_iff_dvd]
    use -((b0 : Int) * c)
    have hd : (h : Int) * b0 * c = A * D + S ^ 2 := by
      have hd0 : (b : Int) * c = A * D + S ^ 2 := by
        exact_mod_cast hdet
      rw [hbfac] at hd0
      simpa [mul_assoc] using hd0
    calc
      -(S : Int) ^ 2 - A * D = -(A * D + S ^ 2) := by ring
      _ = -((h : Int) * b0 * c) := by rw [hd]
      _ = (h : Int) * (-((b0 : Int) * c)) := by ring
  have hhAInt : Int.gcd (A : Int) h = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hhA.symm.gcd_eq_one
  have hhSInt : Int.gcd (S : Int) h = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hhS.symm.gcd_eq_one
  have hGY :
      jacobiSym (g : Int) h * jacobiSym (yp : Int) h =
        jacobiSym (-1 : Int) h * jacobiSym (D : Int) h *
          jacobiSym (Y : Int) h := by
    calc
      jacobiSym (g : Int) h * jacobiSym (yp : Int) h =
          jacobiSym ((g : Int) * yp) h := by
            rw [jacobiSym.mul_left]
      _ = jacobiSym (-(D : Int) * Y) h :=
        jacobiSym.mod_left' hrowHMod.eq
      _ = jacobiSym (((-1 : Int) * D) * Y) h := by
        congr 1
        ring
      _ = jacobiSym (-1 : Int) h * jacobiSym (D : Int) h *
          jacobiSym (Y : Int) h := by
            rw [jacobiSym.mul_left, jacobiSym.mul_left]
  have hAD :
      jacobiSym (A : Int) h * jacobiSym (D : Int) h =
        jacobiSym (-1 : Int) h := by
    calc
      jacobiSym (A : Int) h * jacobiSym (D : Int) h =
          jacobiSym ((A : Int) * D) h := by rw [jacobiSym.mul_left]
      _ = jacobiSym (-(S : Int) ^ 2) h :=
        jacobiSym.mod_left' hdetHMod.eq
      _ = jacobiSym ((-1 : Int) * (S : Int) ^ 2) h := by
        congr 1
        ring
      _ = jacobiSym (-1 : Int) h * jacobiSym ((S : Int) ^ 2) h := by
        rw [jacobiSym.mul_left]
      _ = jacobiSym (-1 : Int) h := by
        rw [jacobiSym.sq_one' hhSInt, mul_one]
  have hASquare := jacobiSym.sq_one hhAInt
  have hminusInt : Int.gcd (-1 : Int) h = 1 := by simp [Int.gcd_def]
  have hminusSquare := jacobiSym.sq_one hminusInt
  have hDsolve :
      jacobiSym (D : Int) h =
        jacobiSym (A : Int) h * jacobiSym (-1 : Int) h := by
    calc
      jacobiSym (D : Int) h =
          jacobiSym (A : Int) h ^ 2 * jacobiSym (D : Int) h := by
            rw [hASquare, one_mul]
      _ = jacobiSym (A : Int) h *
          (jacobiSym (A : Int) h * jacobiSym (D : Int) h) := by ring
      _ = _ := by rw [hAD]
  have hMD :
      jacobiSym (-1 : Int) h * jacobiSym (D : Int) h =
        jacobiSym (A : Int) h := by
    rw [hDsolve]
    calc
      jacobiSym (-1 : Int) h *
          (jacobiSym (A : Int) h * jacobiSym (-1 : Int) h) =
          jacobiSym (A : Int) h * jacobiSym (-1 : Int) h ^ 2 := by ring
      _ = _ := by rw [hminusSquare, mul_one]
  have hGY' :
      jacobiSym (g : Int) h * jacobiSym (yp : Int) h =
        jacobiSym (A : Int) h * jacobiSym (Y : Int) h := by
    calc
      _ = (jacobiSym (-1 : Int) h * jacobiSym (D : Int) h) *
          jacobiSym (Y : Int) h := hGY
      _ = _ := by rw [hMD]
  have hcorr :
      jacobiSym (Y : Int) h =
        jacobiSym (A : Int) h * jacobiSym (g : Int) h *
          jacobiSym (yp : Int) h := by
    calc
      jacobiSym (Y : Int) h =
          jacobiSym (A : Int) h ^ 2 * jacobiSym (Y : Int) h := by
            rw [hASquare, one_mul]
      _ = jacobiSym (A : Int) h *
          (jacobiSym (A : Int) h * jacobiSym (Y : Int) h) := by ring
      _ = _ := by rw [← hGY']; ring
  have hhne : h ≠ 0 := hhpos.ne'
  have hb0ne : b0 ≠ 0 := hb0Odd.pos.ne'
  have hX0ne : X0 ≠ 0 := hX0Odd.pos.ne'
  have hx0ne : x0 ≠ 0 := hx0Odd.pos.ne'
  have hYXfac :
      jacobiSym (Y : Int) X =
        jacobiSym (Y : Int) h * jacobiSym (Y : Int) X0 := by
    rw [hXfac, jacobiSym.mul_right' (Y : Int) hhne hX0ne]
  have hAbfac :
      jacobiSym (-(A : Int)) b =
        jacobiSym (-(A : Int)) h * jacobiSym (-(A : Int)) b0 := by
    rw [hbfac, jacobiSym.mul_right' (-(A : Int)) hhne hb0ne]
  have hypfac :
      jacobiSym (yp : Int) xp =
        jacobiSym (yp : Int) h * jacobiSym (yp : Int) x0 := by
    rw [hxpfac, jacobiSym.mul_right' (yp : Int) hhne hx0ne]
  have hhgInt : Int.gcd (h : Int) g = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hhg.gcd_eq_one
  have hhgSquare := jacobiSym.sq_one hhgInt
  have hproductFac :
      jacobiSym (b * X * xp : Int) g =
        jacobiSym (h : Int) g * jacobiSym (b0 * X0 * x0 : Int) g := by
    calc
      jacobiSym (b * X * xp : Int) g =
          jacobiSym ((h : Int) * h * h *
            ((b0 : Int) * X0 * x0)) g := by
            congr 1
            rw [hbfac, hXfac, hxpfac]
            push_cast
            ring
      _ = jacobiSym (h : Int) g * jacobiSym (h : Int) g *
          jacobiSym (h : Int) g *
          jacobiSym (b0 * X0 * x0 : Int) g := by
            rw [jacobiSym.mul_left, jacobiSym.mul_left,
              jacobiSym.mul_left]
      _ = _ := by rw [← pow_two, hhgSquare, one_mul]
  have hnegA :
      jacobiSym (-(A : Int)) h =
        jacobiSym (-1 : Int) h * jacobiSym (A : Int) h := by
    calc
      jacobiSym (-(A : Int)) h =
          jacobiSym ((-1 : Int) * A) h := by
            congr 1
            ring
      _ = _ := by rw [jacobiSym.mul_left]
  have hsign := outer41_qrSign_restore hb4 hX4 hx4 hgOdd hhOdd
    hbfac hXfac (by rw [hxfac, hxpfac])
  rw [hYXfac, hred, hcorr, hAbfac, hproductFac, hypfac, hnegA]
  calc
    _ =
        (qrSign X0 b0 * qrSign X0 x0 * qrSign x0 b0 *
          qrSign X0 g * qrSign x0 g * qrSign b0 g *
          jacobiSym (g : Int) h) *
        jacobiSym (A : Int) h * jacobiSym (yp : Int) h *
        jacobiSym (-(A : Int)) b0 *
        jacobiSym (b0 * X0 * x0 : Int) g *
        jacobiSym (yp : Int) x0 := by ring
    _ =
        (jacobiSym (-1 : Int) g * jacobiSym (-1 : Int) h *
          jacobiSym (h : Int) g) *
        jacobiSym (A : Int) h * jacobiSym (yp : Int) h *
        jacobiSym (-(A : Int)) b0 *
        jacobiSym (b0 * X0 * x0 : Int) g *
        jacobiSym (yp : Int) x0 := by rw [hsign]
    _ = _ := by ring

/-- Route-neutral Jacobi transfer for the determinant-`-16` endpoint of the
fixed-`41` pseudo-remainder chain.  The two congruences are exactly the
specialization-safe information used by the reciprocity calculation.

No coprimality hypotheses are needed: the first congruence forces the relevant
Jacobi symbols to be nonzero.  This theorem deliberately stops at the
coefficient symbol on the right, so it does not prove `SS41`. -/
theorem ss41_globalJacobiTransfer
    (X Y alpha gamma : Nat)
    (hX4 : X % 4 = 1) (hY8 : Y % 8 = 3)
    (hgamma8 : gamma % 8 = 7)
    (hinv : Int.ModEq Y ((2 : Int) * gamma * X) 1)
    (helim : Int.ModEq gamma ((8 : Int) * Y) (-(alpha : Int))) :
    jacobiSym (Y : Int) X = -jacobiSym (alpha : Int) gamma := by
  have hY4 : Y % 4 = 3 := by omega
  have hgamma4 : gamma % 4 = 3 := by omega
  have hYodd : Odd Y := Nat.odd_iff.mpr (by omega)
  have hgammaOdd : Odd gamma := Nat.odd_iff.mpr (by omega)
  have htwoY : jacobiSym (2 : Int) Y = -1 := by
    rw [jacobiSym.at_two hYodd, ZMod.χ₈_nat_eq_if_mod_eight]
    omega
  have htwoGamma : jacobiSym (2 : Int) gamma = 1 := by
    rw [jacobiSym.at_two hgammaOdd, ZMod.χ₈_nat_eq_if_mod_eight]
    omega
  have heightGamma : jacobiSym (8 : Int) gamma = 1 := by
    calc
      jacobiSym (8 : Int) gamma =
          jacobiSym ((2 : Int) * 2 * 2) gamma := by norm_num
      _ = jacobiSym (2 : Int) gamma * jacobiSym (2 : Int) gamma *
          jacobiSym (2 : Int) gamma := by
            rw [jacobiSym.mul_left, jacobiSym.mul_left]
      _ = 1 := by rw [htwoGamma]; norm_num
  have hnegOneGamma : jacobiSym (-1 : Int) gamma = -1 := by
    rw [jacobiSym.at_neg_one hgammaOdd,
      ZMod.χ₄_nat_three_mod_four hgamma4]
  have hprodY :
      jacobiSym (2 : Int) Y * jacobiSym (gamma : Int) Y *
          jacobiSym (X : Int) Y = 1 := by
    have h := jacobiSym.mod_left' hinv
    simpa [jacobiSym.mul_left] using h
  have hXY :
      jacobiSym (X : Int) Y = -jacobiSym (gamma : Int) Y := by
    rw [htwoY] at hprodY
    rcases jacobiSym.trichotomy (gamma : Int) Y with hg | hg | hg
    all_goals (rw [hg] at hprodY ⊢; omega)
  have hYAlpha :
      jacobiSym (Y : Int) gamma = -jacobiSym (alpha : Int) gamma := by
    have h := jacobiSym.mod_left' helim
    rw [jacobiSym.mul_left] at h
    rw [show -(alpha : Int) = (-1 : Int) * alpha by ring,
      jacobiSym.mul_left] at h
    rw [heightGamma, hnegOneGamma] at h
    simpa using h
  calc
    jacobiSym (Y : Int) X = jacobiSym (X : Int) Y :=
      (jacobiSym.quadratic_reciprocity_one_mod_four hX4 hYodd).symm
    _ = -jacobiSym (gamma : Int) Y := hXY
    _ = jacobiSym (Y : Int) gamma := by
      rw [jacobiSym.quadratic_reciprocity_three_mod_four hgamma4 hY4]
      ring
    _ = -jacobiSym (alpha : Int) gamma := hYAlpha

/-- Source-facing wrapper for `ss41_globalJacobiTransfer`. -/
theorem ss41_globalJacobiTransfer_of_identities
    (X Y alpha gamma delta Q39 : Nat)
    (hX8 : X % 8 = 1) (hY8 : Y % 8 = 3)
    (hgamma8 : gamma % 8 = 7)
    (hbez : (1 : Int) = 2 * gamma * X - delta * Y)
    (helimEq : (8 : Int) * Y = gamma * Q39 - alpha) :
    jacobiSym (Y : Int) X = -jacobiSym (alpha : Int) gamma := by
  apply ss41_globalJacobiTransfer X Y alpha gamma (by omega) hY8 hgamma8
  · rw [Int.modEq_iff_add_fac]
    refine ⟨-(delta : Int), ?_⟩
    calc
      (1 : Int) = 2 * gamma * X - delta * Y := hbez
      _ = 2 * gamma * X + Y * -delta := by ring
  · rw [Int.modEq_iff_add_fac]
    refine ⟨-(Q39 : Int), ?_⟩
    calc
      -(alpha : Int) = 8 * Y - gamma * Q39 := by omega
      _ = 8 * Y + gamma * -Q39 := by ring

/-- The source-facing wrapper with all three determinant-`-16` endpoint
identities exposed. -/
theorem ss41_globalJacobiTransfer_of_endpoint
    (X Y alpha beta gamma delta Q39 : Nat)
    (hX8 : X % 8 = 1) (hY8 : Y % 8 = 3)
    (hgamma8 : gamma % 8 = 7)
    (hrow : (Q39 : Int) = 2 * alpha * X - beta * Y)
    (hbez : (1 : Int) = 2 * gamma * X - delta * Y)
    (hdet : (beta : Int) * gamma - alpha * delta = -8) :
    jacobiSym (Y : Int) X = -jacobiSym (alpha : Int) gamma := by
  apply ss41_globalJacobiTransfer_of_identities
    X Y alpha gamma delta Q39 hX8 hY8 hgamma8 hbez
  linear_combination
    -(gamma : Int) * hrow + (alpha : Int) * hbez + (Y : Int) * hdet

/-! ## Private fixed-41 local-certificate prototype -/

private def outer41HornerNat (j : Nat) : List Nat -> Nat
  | [] => 0
  | a :: rest => a + j * outer41HornerNat j rest

private def outer41HornerInt (j : Int) : List Int -> Int
  | [] => 0
  | a :: rest => a + j * outer41HornerInt j rest

private def outer41CoeffAdd : List Int → List Int → List Int
  | [], right => right
  | left, [] => left
  | a :: left, b :: right => (a + b) :: outer41CoeffAdd left right

private def outer41CoeffScale (a : Int) : List Int → List Int :=
  List.map (a * ·)

private def outer41CoeffMul : List Int → List Int → List Int
  | [], _ => []
  | _, [] => []
  | a :: left, right =>
      outer41CoeffAdd (outer41CoeffScale a right)
        (0 :: outer41CoeffMul left right)

private def outer41CoeffSub (left right : List Int) : List Int :=
  outer41CoeffAdd left (outer41CoeffScale (-1) right)

private def outer41NatCoeffs (coefficients : List Nat) : List Int :=
  coefficients.map (Int.ofNat ·)

private theorem outer41HornerInt_add (j : Int) (left right : List Int) :
    outer41HornerInt j (outer41CoeffAdd left right) =
      outer41HornerInt j left + outer41HornerInt j right := by
  induction left generalizing right with
  | nil => simp [outer41CoeffAdd, outer41HornerInt]
  | cons a left ih =>
      cases right with
      | nil => simp [outer41CoeffAdd, outer41HornerInt]
      | cons b right =>
          simp only [outer41CoeffAdd, outer41HornerInt, ih]
          ring

private theorem outer41HornerInt_scale
    (j a : Int) (coefficients : List Int) :
    outer41HornerInt j (outer41CoeffScale a coefficients) =
      a * outer41HornerInt j coefficients := by
  induction coefficients with
  | nil => simp [outer41CoeffScale, outer41HornerInt]
  | cons b coefficients ih =>
      simp only [outer41CoeffScale, List.map_cons, outer41HornerInt]
      rw [show outer41HornerInt j (List.map (fun x => a * x) coefficients) =
        a * outer41HornerInt j coefficients by
          simpa [outer41CoeffScale] using ih]
      ring

private theorem outer41HornerInt_mul
    (j : Int) (left right : List Int) :
    outer41HornerInt j (outer41CoeffMul left right) =
      outer41HornerInt j left * outer41HornerInt j right := by
  induction left with
  | nil => simp [outer41CoeffMul, outer41HornerInt]
  | cons a left ih =>
      cases right with
      | nil => simp [outer41CoeffMul, outer41HornerInt]
      | cons b right =>
          simp only [outer41CoeffMul, outer41HornerInt_add,
            outer41HornerInt_scale, outer41HornerInt, ih]
          ring

private theorem outer41HornerInt_sub
    (j : Int) (left right : List Int) :
    outer41HornerInt j (outer41CoeffSub left right) =
      outer41HornerInt j left - outer41HornerInt j right := by
  simp [outer41CoeffSub, outer41HornerInt_add, outer41HornerInt_scale,
    sub_eq_add_neg]

private theorem outer41HornerNat_cast
    (j : Nat) (coefficients : List Nat) :
    (outer41HornerNat j coefficients : Int) =
      outer41HornerInt j (outer41NatCoeffs coefficients) := by
  induction coefficients with
  | nil => simp [outer41HornerNat, outer41HornerInt, outer41NatCoeffs]
  | cons a coefficients ih =>
      simp only [outer41HornerNat, outer41NatCoeffs, List.map_cons,
        outer41HornerInt, Nat.cast_add, Nat.cast_mul, ih]
      rfl

private def outer41P35Coeffs : List Nat := [37114507521077322748199865448013086411175693996767, 973668832123250869486273381804376797472826371769056, 12386533563815280752002946805098734358484101470472704, 101782626964201459017595712513961871456707410635509760, 607132169600948260714365191543749659028970933808594944, 2801073162793407900177193874099289238578690192620650496, 10399425083720156507896804968806169306988725781504458752, 31916703671104248065576352328152715386987724956405596160, 82548511337576964145871755863962897246788933124767088640, 182506977511055412649493229615570883796413079361280802816, 348681026573164425070647010511945680942559722095647916032, 580451504856934564988697900020953257721388542668495126528, 847373200756409695226377053478149241489539968706694610944, 1090141545703557436927877102991049261032376591553056997376, 1240457681104303179003196626460730035177574052295067303936, 1251717364652627165864518801590802934653011057051722317824, 1121981425255523184878375376357996926623741406215831289856, 894082150425835055335646967778432354817138947949171048448, 633405099584648057655135783231642482566799722274418065408, 398603189605129206449167041082576379539906856880386867200, 222446345669494018516606686851858231792992765669944590336, 109799589811026231714280764003010128725196713769740271616, 47761240179924833704100637899686124789374079710890295296, 18218880815330787461375237831136868378857270585143066624, 6055592640406432966705731423140206854285380512068403200, 1739283246484606369416817082455364970298159161514393600, 427034621819446714682316960958970493412883347747635200, 88356495964201906070416340429725928657399938428174336, 15112552650990963117991862686934794410680195383033856, 2080084483058620864754721343420087633482474357522432, 221439904487999491680864191556467708263969983561728, 17112626506310728754524430117922574524480462258176, 854206719154027822946732201031205254639220948992, 20676661851243980248163970188279174911217369088]
private def outer41Q35Coeffs : List Nat := [13575035032899773789280580782481393970125623418743, 366268570366642270079544749007778815769444160059968, 4796496882336001046498082106048227803428705810155008, 40611985930969683036405024678295573430870462063939584, 249872240671630097821295649925703119416117865683025920, 1190397662864420506517698221855598243123864780564070400, 4569012195670096452810679913713651114810029108025622528, 14515315900020688482287241011411825704677359228505030656, 38913931571707068435418647235162757225998199684205641728, 89310275638122073737019515676445191188076992192495747072, 177405687110856737535699975906990671728041900807724990464, 307590412532837874095924323280161921797594527013332320256, 468561570947634112085010608298729601824914324818625560576, 630309486033935884814470096937192380677284471102796464128, 751646255359788066335478733413166910898379934883762929664, 796858414224697596613336522840493981904779365504245563392, 752496052012938657885416820995106282087326065084491366400, 633691316123357690814595077582054209772627268659828490240, 476063193613061992531883872105038223575338125410846113792, 318934789479283893273742007212153427464098001589555429376, 190324424900280974163416765047393079536674568378785988608, 100970634019586706331849234212202979024077698691170828288, 47486264514371149620115665011400190922480798791622459392, 19721234402051958448695472492002800291688678540640780288, 7195958178853828252263281905816943479315394992644554752, 2291828515113001455980174987686250004486699846723436544, 631749885443670795890732622404599283601690323417300992, 149082158687920671995082374223774786592887835191148544, 29687958710530360850569507935056099656668316602204160, 4893376322708213381074135572209961917933962414522368, 649819523992475451274433398102651471648515394895872, 66816973463978995220429187276538316408298571563008, 4992455175896648482203529681429884377201733795840, 241182989439020477341926610824195823442197479424, 5655155378118011691805530307905415360332955648]
private def outer41P35 (j : Nat) := outer41HornerNat j outer41P35Coeffs
private def outer41Q35 (j : Nat) := outer41HornerNat j outer41Q35Coeffs
private def outer41P35Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41P35Coeffs)
private def outer41Q35Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41Q35Coeffs)

private def outer41P33Coeffs : List Nat := [356339931386431843564601306280292201074799166973, 8781456415895854055904346851765885143577228971792, 104728911802328833963249664870928322251177604665088, 805045677611184040887486067557347674022748907950080, 4481920491534265612172529344101805626301135365603328, 19251823942602678521496196182448033628029980278521856, 66370690079782717857849521992006387610279983315943424, 188611873892185692353759652571300550936876838425722880, 450307707903458493743588172170267343563806605018398720, 915971934744380607893365842111303009480416081582489600, 1604207962167446163218769835359927031175499071757484032, 2438436518904276375693546512488307945469128212664549376, 3236329527942173183004030185301735752297509380933287936, 3767245054368065803572083761948403217070521821280862208, 3858314126447661120498219673762391324437371574636511232, 3483797025512802662986461477052206601601979904564396032, 2775995779204712660380476845469161191555898219973050368, 1952070321414158452049418580387856643911767009343307776, 1210190320836790102935309522840190273442686473965928448, 660107221621497951377762988015111995443985031094075392, 315794942060517601876614431892478328727063843974414336, 131912630535854436627909248223929343249219405490421760, 47823341105587392285533923540957013632259309283835904, 14927916746604783008883437137226207577957939984465920, 3970004319111522904677253772722055794553982306746368, 887013979219636199076473081333512630267574455631872, 163364713971838672076813461321223010631600249503744, 24148092809257351318450814176066894406248592048128, 2754048596653032589391758273628327064717347520512, 227483623810186828310509475217525083107907076096, 12111073938310477793824841092511787656002142208, 312042141881338387352663450612789087217647616]
private def outer41Q33Coeffs : List Nat := [130335207854901393876609772891581612178578423085, 3309254906124007380115001699420232566714291271344, 40704668293514583200035407184178498769011123196160, 323065287244601445123696628362730051897946947923968, 1859251437367047177675812690810257950949012972109824, 8266081703601630699214731747271164552084540034646016, 29535847558927934897974775259285119882107773723344896, 87121559089212439075322399269144456506367074052866048, 216242069633269822608957657435496076835845718954475520, 458075495997450810183751100866607041332436388544512000, 837060060420125326826034518780591280615594774090481664, 1330276443180122517677757208120171223457319889645076480, 1850115197325556636681485072959918681460371113923051520, 2262391440885481338222314694876016995957757641463169024, 2440839040407489415230002331122023696642038420561985536, 2328786548143245237925783140574012304904869865343418368, 1967575328305644416428262375984846429888788002081079296, 1472782462467377851696070052842260012886785530657767424, 976240772267248514865348631601202666176173807698444288, 572261265297461721068961464061167221303843708213395456, 295960705479706144835873709484060575360506453781643264, 134581605943373993046180538077925757653322398798184448, 53556076072080059447877619727610102030335742268407808, 18535199912937044709187798495760809590890136694947840, 5533605689202804964087649308172895292620891872034816, 1409941669063935157209944090163728532724021783953408, 302295772087617751424230077766374538589068370903040, 53504345804627424643823422828177536684996696211456, 7610860834650204603809771666749304592312991481856, 836357127370720466000061247226475362533156847616, 66642453402860458722272231412175190422559129600, 3426428780523267012581698806843355337077030912, 85344859317972892267395131791532058042433536]
private def outer41P33 (j : Nat) := outer41HornerNat j outer41P33Coeffs
private def outer41Q33 (j : Nat) := outer41HornerNat j outer41Q33Coeffs
private def outer41P33Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41P33Coeffs)
private def outer41Q33Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41Q33Coeffs)

private def outer41P25Coeffs : List Nat := [2027634547908940871852281267934205595347393, 37054013345651939211907004200517848705527280, 323919434338066769119876098461726338826364288, 1802334675720977599956867155389442628071782400, 7164685960028491336543213321386273559212818432, 21650293886787272591721556714153145378267463680, 51660596459669654047932700126317140631607050240, 99810445191115836356954203694082138405664194560, 158841149062667262914238593026392084406866018304, 210697870878991082896908560586034328755733790720, 234816125072584427501317934973191614946841985024, 220957979196068604320903356339310105726268997632, 175967385510964424582422636098661056575652757504, 118602928275575120611240659751698949659925938176, 67495170678108804654768679976940435916086837248, 32271616770548249394790720313507471251220725760, 12861125506630645578339571703117190555682996224, 4221899067790017301773772434396936327800029184, 1122167991169544532049580942315861935415885824, 235525064346214887704882959317678522344931328, 37576954513154603207553687925960605318512640, 4283212586886548010743487751781098356473856, 310752559652180496797253136373257900916736, 10784906123191466246533598669648707977216]
private def outer41Q25Coeffs : List Nat := [741629402091626969168858619349980841667189, 14106799134145288377388519111629148051020496, 128599654176348514997503033950720776335946624, 747717988045879084113883118936684051882223616, 3112983417858608724053937586569920666306117632, 9876418807983928329608793594363131434376888320, 24811185962557708537147350883787594895762391040, 50623316546229732038484345197982511958977413120, 85373093589293879281551590010627115602805784576, 120473859556257046877307465925072920961653669888, 143470038251986937253907421656100286494217863168, 144996144614283670453882758635276965337876135936, 124755922134865834851048787585570593582945927168, 91479620843040097569466852318824584638671880192, 57107998879291292572378311024543667069611147264, 30254935441491113643944750272865669192450310144, 13526700720849075293346310989848054052320968704, 5060443908026293521975801230672356988713697280, 1564776560664621262944872556293863233307017216, 392980179869462311416872630637764979929907200, 78147263873882059106173260382215848046100480, 11842408101324281549827111881394377866608640, 1285010125453426790586182397073408353370112, 88932200954039323742262420156942857011200, 2949717914035272819564744935288535515136]
private def outer41P25 (j : Nat) := outer41HornerNat j outer41P25Coeffs
private def outer41Q25 (j : Nat) := outer41HornerNat j outer41Q25Coeffs
private def outer41P25Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41P25Coeffs)
private def outer41Q25Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41Q25Coeffs)

private def outer41P23Coeffs : List Nat := [1756181067308519595954749458874420371119, 29237780651317466924832116429261714696672, 231842253628048290263938985445144651217920, 1164569480721901045942804684870377852166144, 4157292539710919326513385853299881143107584, 11215387618845481073805133341612358748864512, 23735579701491404225479094946202406564659200, 40374006188241444916890753738064907733041152, 56097119526322522600843513964122076195323904, 64347826652928988981908056615452219602370560, 61333725749558773397326475557038541707935744, 48727623814287500641597325271351418045857792, 32267214435910279925306746398446972309602304, 17754958212606804083729880780303586589409280, 8065514899811726370589340110565931898372096, 2992821243047310323254863868250973446078464, 892576175331369315458322643498117562892288, 208829046112119221472708224330912562675712, 36922759443822132890537875255799670898688, 4639473910164700334314717866305081311232, 369289353164224994752200694596705976320, 14000276305858894752496423838460936192]
private def outer41Q23Coeffs : List Nat := [642342337407807779757329406829563081679, 11173773806138653908942997952982462988736, 92786186996340679280686066499395812339712, 489293672779849199917217234538752081223680, 1838755523449154367155761036355754612948992, 5238059118430491222990831070075867014103040, 11746134512222283053051393280156396729401344, 21253315554519890542028396274313008582230016, 31551534945364555156011876401044253027860480, 38867014093405336139277216624171244937281536, 40020471316446678524213876176403470137425920, 34586834699576346800697266421739890896011264, 25121443269857798189088181584209873266016256, 15314602078753064306036254211452535381688320, 7803810406007563726037526373114908631891968, 3299695595117576235836130811557434961690624, 1144727666637926694711382011325553955569664, 320432416197976034168211475041575573127168, 70606951022401992675289327569902543831040, 11793666101321424522552108750179563208704, 1403836145249449778801459166498516893696, 106116934768972073417303967871006670848, 3829135399893031043417825323339743232]
private def outer41P23 (j : Nat) := outer41HornerNat j outer41P23Coeffs
private def outer41Q23 (j : Nat) := outer41HornerNat j outer41Q23Coeffs
private def outer41P23Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41P23Coeffs)
private def outer41Q23Int (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41Q23Coeffs)

private def outer41A34Coeffs : List Int := [-1659986084617607093367347469044707580851593679843, -42116410086997682104981064145379253082936259298384, -517657101865380150490706542764072948116780359617280, -4105475521094732172994259904111794943756681426718720, -23609395490385112829683007356270158519712385838743552, -104886196609730448051412431396423443910841544127545344, -374488331051703597730868664926887441344064859284701184, -1103781164942440158584620857778736229259023731317014528, -2737563940150934499512785988398280517303446614306717696, -5794635360127614222982186931608023494175968380923674624, -10580564572996144887082590813217204145469040884468154368, -16801786631127999950796705767778296391222103656470937600, -23349190256506894499648527203307631869308793937645797376, -28529779094324087471235758423504687851623916336912007168, -30755691560078730047945974841285252827761592256182616064, -29320393616288208187585799058876568513755610093329580032, -24752739377486713480559509930447283860584056687081553920, -18513148968106342299011537236318985246904749865140486144, -12261578892618235532548335943624553841647520111801663488, -7181737237501839038334565657089303957446330652569894912, -3711186943152987935462693894564994325957711246428995584, -1686187951528924676491402257253107807884420437644410880, -670453051752113207814023594112367589954211635248758784, -231843038799937999625795303447651321916376681205989376, -69157604832884410832094767821457449239462607633514496, -17606197962048199541292303356546736213305446700679168, -3771611289223683736165650779467210049219648068517888, -666978778010985924029894060672243653715164630351872, -94794358563772268601616070781259022956587072356352, -10407917548457744509520270826343009593385430286336, -828598241927878272267194402137524606589302996992, -42565058428395920557483456357940003429274353664, -1059265660552923184792065742223566128977805312]
private def outer41B34Coeffs : List Int := [607157975624838345883869567713038803641490955091, 15857995018718227837490332900687252745022862700720, 200844118608905413909983629359274225043966784353536, 1643041662955950625358006160842010215220130462838784, 9757014511963535406893725361013143081807919900262400, 44813625775923148220379040918066660316133116244656128, 165630367092592029857746077101339090355968783186657280, 506042141580433714834509911478724426625024289255981056, 1302893368341074313919030875520852232753419644963913728, 2867496963020817207116339785454645922028915796633190400, 5453414440652724306147648132578915766880503726121943040, 9036819076808037459034035653546655267134851407027372032, 13131868595357931640627162746338624005371548867416293376, 16816262809692598508740235873718382090977056507350220800, 19046531833396657125066051999055696548610001555230294016, 19130225606169210067365739945985964260455921988518543360, 17067573270656667177509869462914351869508483359113740288, 13537179676768254255953056869557039452943515635467419648, 9545293369908050096358488580903152308383347649160413184, 5978574956275983432642945996804408690164535169875181568, 3320653230059217189191458768850870633487212016738238464, 1631294583595650581007178005140370984364839801232293888, 706208129631019052568077123115225397431325306361217024, 268099617764056418563797533156711906852388280094162944, 88683005569436441424243983291302361884722876194488320, 25348666039653295971124660541877877126281279246958592, 6193564253104583112248174991853616771629978210009088, 1275265036336449089529703282312269289317196535693312, 217057986757826683095187298476909152831386358382592, 29729416308944716275074172533948182379161817448448, 3149344500162598279801388139596067385548986122240, 242176034896179357880768119846619302572580667392, 12028706722502702565151813966030201406254743552, 289713684937551640285009433770548001087946752]
private def outer41A34 (j : Nat) := outer41HornerInt j outer41A34Coeffs
private def outer41B34 (j : Nat) := outer41HornerInt j outer41B34Coeffs

private def outer41A24Coeffs : List Int := [85333937630747741075872034237557346872797, 1488514889612627954366447596892425558540592, 12394999803199157387754192632014208888996352, 65547268598709582571223835254604869076422656, 247026078719714677849609306587306912415940608, 705724404995765184178654640762391761655955456, 1587149549666031120994129527193759132296413184, 2880182637161283852615469594518174677094891520, 4288414056140352664145662351753161732081582080, 5298498436688496497853898599103660824723456000, 5472199087562500143913446121367674979971235840, 4743635642114433833363821221262346674482708480, 3456040156162795116878361088421736477328670720, 2113423778821822294247580797349980938612768768, 1080307456377935098610967249271776193489666048, 458234272281036485668060371501714738931302400, 159478542576940345412403282224684743218167808, 44785394167996800506179945036874786189344768, 9900586268523402152666584516084371134873600, 1659164834297204484750678514346707373785088, 198151912743472420052508665109113399672832, 15028710443849120591963855556019696435200, 544135532265214639455853160580312465408]
private def outer41B24Coeffs : List Int := [-31211816354422145545549281322040306884405, -567751257996143080637923300123379197403600, -4940246820653657515367182132756592669863936, -27360945048099261987204584596346562859323392, -108260985285260450858629769335979483379335168, -325621327908670312792774180621572894576607232, -773352847065479602592382013494959071031197696, -1487162441896103033424952000049793485594689536, -2355615598483570586321453657273490078561206272, -3109963549336759290043002393515303560569421824, -3449621992544897197463278180094232130433843200, -3230697765290361918296487385914122166511599616, -2560686486047407724040509924211847445757296640, -1717717278226111285186672889333265257071640576, -972871313064506319632045856562485285598789632, -462939406206989998938024170009340490303930368, -183610434401920183294938871318709590202253312, -59983987373865959767307210391775732631076864, -15866770337851486618171848980218421333458944, -3314095018364352382743037154147902815207424, -526187447175114474929477984572878627012608, -59686133833195360463990480952798560124928, -4309205471446376353877667971203147497472, -148823393440058704808438471269829050368]
private def outer41A24 (j : Nat) := outer41HornerInt j outer41A24Coeffs
private def outer41B24 (j : Nat) := outer41HornerInt j outer41B24Coeffs

set_option maxHeartbeats 2000000 in
private theorem outer41PrototypeCross35Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P33Coeffs)
        (outer41NatCoeffs outer41Q35Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q33Coeffs)
        (outer41NatCoeffs outer41P35Coeffs)) =
      [8 * 15600826093, 8 * 13817666464] ++ List.replicate 64 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41PrototypeCross35 (j : Nat) :
    outer41P33Int j * outer41Q35Int j -
      outer41Q33Int j * outer41P35Int j =
      8 * (15600826093 + 13817666464 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P33Coeffs)
            (outer41NatCoeffs outer41Q35Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q33Coeffs)
            (outer41NatCoeffs outer41P35Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([8 * 15600826093, 8 * 13817666464] ++
          List.replicate 64 0) := by rw [outer41PrototypeCross35Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41PrototypeEndpoint35Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A34Coeffs
        (outer41NatCoeffs outer41Q35Coeffs))
      (outer41CoeffMul outer41B34Coeffs
        (outer41NatCoeffs outer41P35Coeffs)) =
      [8428693448] ++ List.replicate 66 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41PrototypeEndpoint35 (j : Nat) :
    outer41A34 j * outer41Q35Int j + outer41B34 j * outer41P35Int j =
      8428693448 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A34Coeffs
            (outer41NatCoeffs outer41Q35Coeffs))
          (outer41CoeffMul outer41B34Coeffs
            (outer41NatCoeffs outer41P35Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([8428693448] ++ List.replicate 66 0) := by
          rw [outer41PrototypeEndpoint35Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41PrototypeCross25Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P23Coeffs)
        (outer41NatCoeffs outer41Q25Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q23Coeffs)
        (outer41NatCoeffs outer41P25Coeffs)) =
      [-108 * 91370185007570122207,
        -108 * 76509722917161697392] ++ List.replicate 44 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41PrototypeCross25 (j : Nat) :
    outer41P23Int j * outer41Q25Int j -
      outer41Q23Int j * outer41P25Int j =
      -108 * (91370185007570122207 + 76509722917161697392 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P23Coeffs)
            (outer41NatCoeffs outer41Q25Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q23Coeffs)
            (outer41NatCoeffs outer41P25Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-108 * 91370185007570122207,
            -108 * 76509722917161697392] ++
          List.replicate 44 0) := by rw [outer41PrototypeCross25Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41PrototypeEndpoint25Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A24Coeffs
        (outer41NatCoeffs outer41Q25Coeffs))
      (outer41CoeffMul outer41B24Coeffs
        (outer41NatCoeffs outer41P25Coeffs)) =
      [1848164145209522451468] ++ List.replicate 46 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41PrototypeEndpoint25 (j : Nat) :
    outer41A24 j * outer41Q25Int j + outer41B24 j * outer41P25Int j =
      1848164145209522451468 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A24Coeffs
            (outer41NatCoeffs outer41Q25Coeffs))
          (outer41CoeffMul outer41B24Coeffs
            (outer41NatCoeffs outer41P25Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([1848164145209522451468] ++ List.replicate 46 0) := by
          rw [outer41PrototypeEndpoint25Coeffs]
    _ = _ := by simp [outer41HornerInt]

private def outer41ModHorner {n : Nat} (j : ZMod n) :
    List (ZMod n) → ZMod n
  | [] => 0
  | a :: rest => a + j * outer41ModHorner j rest

private def outer41ModCoeffAdd {n : Nat} :
    List (ZMod n) → List (ZMod n) → List (ZMod n)
  | [], right => right
  | left, [] => left
  | a :: left, b :: right => (a + b) :: outer41ModCoeffAdd left right

private def outer41ModCoeffScale {n : Nat} (a : ZMod n) :
    List (ZMod n) → List (ZMod n) := List.map (a * ·)

private def outer41ModCoeffMul {n : Nat} :
    List (ZMod n) → List (ZMod n) → List (ZMod n)
  | [], _ => []
  | _, [] => []
  | a :: left, right =>
      outer41ModCoeffAdd (outer41ModCoeffScale a right)
        (0 :: outer41ModCoeffMul left right)

private def outer41ModCoeffs {n : Nat} (coefficients : List Nat) :
    List (ZMod n) := coefficients.map (Nat.cast ·)

private theorem outer41ModHorner_add {n : Nat}
    (j : ZMod n) (left right : List (ZMod n)) :
    outer41ModHorner j (outer41ModCoeffAdd left right) =
      outer41ModHorner j left + outer41ModHorner j right := by
  induction left generalizing right with
  | nil => simp [outer41ModCoeffAdd, outer41ModHorner]
  | cons a left ih =>
      cases right with
      | nil => simp [outer41ModCoeffAdd, outer41ModHorner]
      | cons b right =>
          simp only [outer41ModCoeffAdd, outer41ModHorner, ih]
          ring

private theorem outer41ModHorner_scale {n : Nat}
    (j a : ZMod n) (coefficients : List (ZMod n)) :
    outer41ModHorner j (outer41ModCoeffScale a coefficients) =
      a * outer41ModHorner j coefficients := by
  induction coefficients with
  | nil => simp [outer41ModCoeffScale, outer41ModHorner]
  | cons b coefficients ih =>
      simp only [outer41ModCoeffScale, List.map_cons, outer41ModHorner]
      rw [show outer41ModHorner j (List.map (fun x => a * x) coefficients) =
        a * outer41ModHorner j coefficients by
          simpa [outer41ModCoeffScale] using ih]
      ring

private theorem outer41ModHorner_mul {n : Nat}
    (j : ZMod n) (left right : List (ZMod n)) :
    outer41ModHorner j (outer41ModCoeffMul left right) =
      outer41ModHorner j left * outer41ModHorner j right := by
  induction left with
  | nil => simp [outer41ModCoeffMul, outer41ModHorner]
  | cons a left ih =>
      cases right with
      | nil => simp [outer41ModCoeffMul, outer41ModHorner]
      | cons b right =>
          simp only [outer41ModCoeffMul, outer41ModHorner_add,
            outer41ModHorner_scale, outer41ModHorner, ih]
          ring

private theorem outer41ModHorner_replicate_zero {n : Nat}
    (j : ZMod n) (count : Nat) :
    outer41ModHorner j (List.replicate count 0) = 0 := by
  induction count with
  | zero => simp [outer41ModHorner]
  | succ count ih =>
      rw [List.replicate_succ, outer41ModHorner, ih, mul_zero, add_zero]

private theorem outer41ModHorner_natCast {n : Nat}
    (j : Nat) (coefficients : List Nat) :
    (outer41HornerNat j coefficients : ZMod n) =
      outer41ModHorner (j : ZMod n) (outer41ModCoeffs coefficients) := by
  induction coefficients with
  | nil => simp [outer41HornerNat, outer41ModHorner, outer41ModCoeffs]
  | cons a coefficients ih =>
      simp only [outer41HornerNat, outer41ModCoeffs, List.map_cons,
        outer41ModHorner, Nat.cast_add, Nat.cast_mul, ih]

private theorem outer41NoCommonPrime_of_bezout
    {n zeros : Nat} (hn : n ≠ 1)
    (P Q U V : List Nat)
    (hcoeff :
      outer41ModCoeffAdd
        (outer41ModCoeffMul (outer41ModCoeffs U)
          (outer41ModCoeffs P))
        (outer41ModCoeffMul (outer41ModCoeffs V)
          (outer41ModCoeffs Q)) =
        ([1] ++ List.replicate zeros 0 : List (ZMod n)))
    (j : Nat) :
    ¬(n ∣ outer41HornerNat j P ∧ n ∣ outer41HornerNat j Q) := by
  rintro ⟨hP, hQ⟩
  have heval := congrArg (outer41ModHorner (j : ZMod n)) hcoeff
  rw [outer41ModHorner_add, outer41ModHorner_mul,
    outer41ModHorner_mul] at heval
  rw [← outer41ModHorner_natCast (n := n) j P,
    ← outer41ModHorner_natCast (n := n) j Q] at heval
  have hPzero : (outer41HornerNat j P : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hP
  have hQzero : (outer41HornerNat j Q : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hQ
  simp only [hPzero, hQzero, mul_zero, zero_add] at heval
  have hone : (1 : ZMod n) = 0 := by
    simpa [outer41ModHorner, outer41ModHorner_replicate_zero] using heval.symm
  exact hn (ZMod.one_eq_zero_iff.mp hone)

private def outer41Bezout35_7_left : List Nat :=
  [2, 5, 2, 1, 2, 3, 4, 4, 0, 1, 3, 5, 5, 1, 4, 3, 0, 4, 4, 1, 6,
    4, 5, 4, 4, 4, 4, 6, 4, 5, 1, 0, 5]

private def outer41Bezout35_7_right : List Nat :=
  [0, 2, 1, 2, 1, 6, 3, 2, 1, 2, 1, 6, 6, 6, 6, 0, 3, 5, 6, 0, 6,
    3, 0, 1, 5, 1, 2, 0, 2, 3, 4, 6]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout35_7_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout35_7_left)
        (outer41ModCoeffs outer41P35Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout35_7_right)
        (outer41ModCoeffs outer41Q35Coeffs)) =
      ([1] ++ List.replicate 65 0 : List (ZMod 7)) := by
  decide

private theorem outer41NoCommon35_7 (j : Nat) :
    ¬(7 ∣ outer41P35 j ∧ 7 ∣ outer41Q35 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P35Coeffs outer41Q35Coeffs
    outer41Bezout35_7_left outer41Bezout35_7_right
    outer41Bezout35_7_coeffs j

private def outer41Bezout35_4637_left : List Nat :=
  [182, 4292, 3451, 3559, 435, 853, 1870, 1881, 1348, 1704, 3623, 2333,
    2557, 3887, 521, 2308, 3550, 2615, 1170, 1983, 4490, 1873, 3484,
    469, 2917, 4110, 1422, 2136, 1257, 4309, 2622, 1010, 2303]

private def outer41Bezout35_4637_right : List Nat :=
  [3816, 2251, 405, 4228, 775, 680, 1655, 1211, 841, 1417, 1571, 2480,
    2736, 2211, 1111, 203, 2640, 1043, 3020, 3278, 354, 4130, 4213,
    3851, 4294, 4030, 2252, 647, 438, 2621, 1310, 1868]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout35_4637_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout35_4637_left)
        (outer41ModCoeffs outer41P35Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout35_4637_right)
        (outer41ModCoeffs outer41Q35Coeffs)) =
      ([1] ++ List.replicate 65 0 : List (ZMod 4637)) := by
  decide

private theorem outer41NoCommon35_4637 (j : Nat) :
    ¬(4637 ∣ outer41P35 j ∧ 4637 ∣ outer41Q35 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P35Coeffs outer41Q35Coeffs
    outer41Bezout35_4637_left outer41Bezout35_4637_right
    outer41Bezout35_4637_coeffs j



private def outer41P37Coeffs : List Nat := [83253740363351112270110680823915497195086082662415, 2316921716876235667455300629728710423354257218362176, 31322720580932972583556196112247108215623911291346944, 274038121921678250992352309511003198785306808203044864, 1743891299529120910364522696990965556250558625086832640, 8601796365412443473591233428058187400434152357118345216, 34221325618519937314848088721350074848279542920409776128, 112822069153972692670870810777932775202285334517549891584, 314281619267069371045856353608758467740647355409036738560, 750510400411365040950445247036634784402986723047483899904, 1553481694411700989944922559808910245018285103416048877568, 2811183133101184656344861620515181055149748455080732917760, 4477281556096239123819752236629659893811883373225383559168, 6308901676195276675884789400363912118600421775110825836544, 7897013335551551033307721813353631027622991591425397751808, 8807749892407484342363956888851901039129562988362764124160, 8772202632234350732121910398388212166112284946907820720128, 7812798205790420534843321833607359866387488409609440329728, 6226722158199211939949392684557462793661952739821353959424, 4440862230399276888296317838869535588979422470236220162048, 2832235721644621337930692984345742285942741291572266008576, 1612995260416736176787203208964461341184028380145714724864, 818520960508095849710743853584484438973688542764306792448, 368974468234724422288479697173222734551446546056524857344, 147155655033215745391555266243695268182697989966338719744, 51653519653703615201131881457031787298217606265444499456, 15850994585772773783581257188969949554074938556924559360, 4216235664952499880082063517922430999270817830168166400, 961404447163934742958471212195818129782444350639177728, 185231631421500175726820150257838115980648603235385344, 29574256234327252091680554211090736674814527237259264, 3808469998347231695231335387246338090804565073985536, 380144467642411001834436596487329310597599094374400, 27599667574501857988000813473557528319748762238976, 1296768776586364055504929850489063902990112391168, 29597967166462315482630109086176517547515445248]
private def outer41Q37Coeffs : List Nat := [30450961565652152234787211079471534971622564502879, 870181821290280893901824609390607739550542953027168, 12089562680857322296240797734086202640173308548743168, 108789457603425306769312607583154692341000961998104576, 712714049159085522508789141469678085033471196399337472, 3622645489006099933462776070121035988089097095172063232, 14866980987358882756074261560417941605277238470387957760, 50616073593545198066649904723378338246632452613092671488, 145778958799492537066291428940739171535953983160681758720, 360383299391686329373545963365680289577533983457915437056, 773283255996767818320775052004065867197938639310040334336, 1452731429421523312170318956499070217890264622955713527808, 2405836007334979992194074089863510751904385077506627076096, 3531113541907208625988120822578614200130776483502227456000, 4612592488959558357604171838063903447223441956489712893952, 5379797539903681325413429967584786977669467546332841377792, 5615784981810026020374404536625562687010475471705259114496, 5255240107743825523209378768782520266955506655394080489472, 4412964719919203397541040731155811372253875677971798294528, 3326303874328579839083246966436177571296966047056458153984, 2249827202303642724454473022745254262415066970434639495168, 1364187011111814535666610918679933878591445357263925018624, 740324767546201920046392153371610548955362821863009943552, 358721982040832093908449193337034566057865943903759237120, 154696797981815721531604905788211963502551413496160976896, 59124773111798272605289324699938064218066191679821447168, 19920096713862403696000268636985372246849155002519257088, 5876056745826496712527965029853072986106278371672457216, 1504473139417006128044837335101675780474042157367296000, 330632906768315691746258891887081005701711230610178048, 61467870829082827222486681088105363603999478450749440, 9480226004725280971017884670024412098417942899720192, 1180525384296801361616708908379990721979129421365248, 114054818416621183753345823909440943149663903547392, 8022391807330496682354447299828818542564468588544, 365484822363856020420709367796845935937621852160, 8095170507066616200377465732971355226670891008]
private def outer41P37 (j : Nat) := outer41HornerNat j outer41P37Coeffs
private def outer41Q37 (j : Nat) := outer41HornerNat j outer41Q37Coeffs
private def outer41P37Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P37Coeffs)
private def outer41Q37Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q37Coeffs)

private def outer41P31Coeffs : List Nat := [2977255887424773165937137356651488754818264517, 68457193941583670244085540275573255026536079760, 760012472556425353482583136335765044731056299008, 5425070631789858678945266594988737811280474673152, 27972379989046443774262612812863217560821803712512, 110963081327500576469219629943495947165553700896768, 352197220466741913994992377216420295700152418566144, 918399010263217391662418141561646091484003848683520, 2004693453128999322062996022738165703572475657322496, 3713442774882730579959494608844624916387640637390848, 5896940421207857647376125902509381296444611399516160, 8088642073837772361931826656875999049050777014239232, 9636575250057718236555859741093338501038965694398464, 10010411437140612926801993698543073719950914946596864, 9089400554334253560777741636121944833201857418493952, 7222611598939167820311384382133947566487224631427072, 5022603653950587944882924967930535520836087099424768, 3052934131263948952270273809332166692432840967061504, 1618034197836983740492910466815364128567009120092160, 744827414745323037046399100251808565518397173923840, 296156867196820780885498399544826223522451824836608, 100950476813146976958347867743556064872101226479616, 29201567310188776676297887839804619384203088232448, 7070887060002008965207871798998557943481212338176, 1406625298064365070987367352955102061001485320192, 223892651564033499491794289122533818971954610176, 27417303165507754916401175246694283748950671360, 2425198173624612026078282760303398036864761856, 137927506939779697506115565717472542711611392, 3787487297374586707948537669733385680977920]
private def outer41Q31Coeffs : List Nat := [1088963741489657664547252741831597823291549141, 25852262988214402254511229788323900628681456816, 296684104650151084626912961786039281067646481920, 2191908864254922978619591125246722300249451008000, 11713355796287401041126647925236040404212083654656, 48228448025517249978255687958449101840933171757056, 159138074007949193457752237619143647888574485889024, 432148195378833317793121115029087161738798414430208, 984190607562065771691675774657244565547549072556032, 1906036518201620696806038519256171615740939309416448, 3171651166255135047548359759552287802466220462047232, 4570046418400691673855550755486290360561017265586176, 5735268325321255475115673643661077180104251426209792, 6295155568054666522149689229069602041139716576772096, 6060572234859245278277514523742517533829141876441088, 5126149279702580873670717576505798623783709218701312, 3811307086871851989335076140256123996908412202909696, 2489584693011583482136650356928547233946986143023104, 1426375730660601142351737414569166925780860425732096, 714759642963339449130730471661143754880352673333248, 311948791359429756500069999857604851060087592058880, 117892634546025042296134380914120582770481340350464, 38281693016703799363530525603173040230899631783936, 10570604029413090538190175476275474782682217447424, 2447906982917241510292594685202555225383989411840, 466526330552429658575232166281278025797585600512, 71253209408318156604918379765560262981033394176, 8384820828235547571847024687096233445333925888, 713693203844611080717990057647107645525458944, 39107444660435787536660626410442973314547712, 1035893961675100638071394918217678134968320]
private def outer41P31 (j : Nat) := outer41HornerNat j outer41P31Coeffs
private def outer41Q31 (j : Nat) := outer41HornerNat j outer41Q31Coeffs
private def outer41P31Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P31Coeffs)
private def outer41Q31Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q31Coeffs)

private def outer41P29Coeffs : List Nat := [129746945218306758738024802264984121141298301, 2799529157216814504404062550936659554751872368, 29088119038401372123467449394718438459233880064, 193769383394930092558431029012794401296048451584, 929503247884630466817663578011619433077106147328, 3418906697186117143877003864317720050283949588480, 10025393891633643966026062947616140304349384409088, 24056363574630589254461053034293110904849466130432, 48110739357702672086660016389389528539374114832384, 81262499675790111813854509129072588472682496917504, 117048267940565129949375014480505089646109927669760, 144773485726140483157311389625515416434698969153536, 154511675585760317647618034258876554629758454857728, 142727844931415885738095964131260946647136967065600, 114281097761257771308536252349052980518967268343808, 79315600308027157678367172454857411978741506113536, 47645144336931990695253129343357446996123415740416, 24696081553256349990598596431316006200787314147328, 10992292538688602143276002293548813701357227737088, 4172316342278269827198410690014144616070438191104, 1337533872572140251021218612989684346668147802112, 357370618217370363322531281197597587736419631104, 78135909873813897987515640006628056039419805696, 13619597232202355789729338904829662026792960000, 1820341232040033531439134853771426403937419264, 175203355904525386509485104094385862216777728, 10811257645065557443352714008571682660286464, 321261428435216258679192654494184398389248]
private def outer41Q29Coeffs : List Nat := [47456357214223820178124580659475013892403605, 1059401329559995981033401495205519506612956432, 11404079074468672727383026112249461631298172416, 78819980193184751922205990860288738138727673856, 392915018445846063739883174840186053570374402048, 1504460006644459907696279859333724876995914891264, 4601047402803693106634874463008927181556332625920, 11538243957411173928928338162445096063261806166016, 24170547267831447829490135457807206660403187679232, 42869726380762910783077463206059104096888549277696, 65019035962580468636975205197667314665822688903168, 84940774510681645312375643673517576739673744605184, 96081461972203088397175346906569659573075129139200, 94434777789617484443217962666289131963928641798144, 80811117250713514320685277394504863349972637057024, 60248214568696650082215100497511811736833548615680, 39107889863306465810456234239622294030409671901184, 22057396355792892244383166795462441227397961351168, 10771913021769058271645242412346210875167576424448, 4531256865398297778185769032097171331936103170048, 1629940813815290988732551393685038805160227241984, 496414567498597330138606719740678879930549796864, 126294190755120041875374376000154076379409809408, 26347047028855117117586162556410717190175588352, 4390133007041605488252854787566745981913399296, 561883902008134151844418622303786544320741376, 51868720178161700774141833265305744729702400, 3074291549910874686066710768735320042110976, 87866373589118976732770640545417955115008]
private def outer41P29 (j : Nat) := outer41HornerNat j outer41P29Coeffs
private def outer41Q29 (j : Nat) := outer41HornerNat j outer41Q29Coeffs
private def outer41P29Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P29Coeffs)
private def outer41Q29Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q29Coeffs)

private def outer41P27Coeffs : List Nat := [15125972628772627188308852790989122576093135, 298937463796978242620369633621330487893557264, 2836274687105831182305104540142621050596721280, 17195349173402865918063251715291446472458700800, 74799553853679169324193851094488140287217139712, 248509252483418550929891361343917975957705064448, 655366553296070706284411037218276935967178752000, 1407574046111039785403514937334831182580696481792, 2506417325878772375397080392987024832740234100736, 3747376735136959976686980982153197911169438842880, 4746599470057392835823745196401162095854866137088, 5124881575821176397434836374105371998889042771968, 4734787150435288136516948046689859131235964551168, 3750051151030730189911361541250230228647497695232, 2546207288183723866695149780425526425387228200960, 1479329394230197694030075006961500619844230316032, 732623217469859733295668222904461012766432428032, 307380155723850066435439845939007998549255258112, 108283022136391688279951807565424750459336261632, 31625476316250095336265381327716401828935499776, 7522384170174414926093495271782497506771861504, 1420260498043793405640329538747958501492916224, 204800688166859587307417716333355533374324736, 21189217328069974668014219417257720273698816, 1400836435804736210417556751246305030832128, 44459495730966572086373121910536350466048]
private def outer41Q27Coeffs : List Nat := [5532489100809472968866799826476006953953371, 113471604329499668333521620654073102885575984, 1119063208953642233225683165135321483351553152, 7064247455564879313348020742178715155427514368, 32056691309796245594628189080173191993630097408, 111331925937188830869832151845828567613500293120, 307609167565536196753984264705164053406659117056, 693913996894912476444236919525262260196104732672, 1301386623043341115151148103329089758827726766080, 2055586783619108459556875300993373974780700524544, 2760236989915057657986668418052426245673741975552, 3171737194599972331696819774240832350344280276992, 3132509278935597588562799374186083536741664292864, 2665775521194512351273901474682249046998908928000, 1956349844556944234275317023514815966368713670656, 1237100456141504939300512193091431821767344128000, 672367462245653862126642585946364849260939182080, 312713815936370310337980499033256923084970000384, 123642101711343671868369026405962641483155636224, 41172931538046181738889241746524228312721522688, 11398515468867913892344943779483507891573358592, 2576367721232126900973891805422806393522487296, 463277940219913342143185836615192133280727040, 63755663958441842117522981362374043162902528, 6307133557448554920458881951733356559335424, 399377131551135670889567131225126621675520, 12159862080264361596272990608009942007808]
private def outer41P27 (j : Nat) := outer41HornerNat j outer41P27Coeffs
private def outer41Q27 (j : Nat) := outer41HornerNat j outer41Q27Coeffs
private def outer41P27Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P27Coeffs)
private def outer41Q27Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q27Coeffs)

private def outer41P21Coeffs : List Nat := [75168018582826613738166660047275727419, 1128384738281660810910431915276118733904, 8025587724352532841435547999962817521920, 35949103784643509331395079464038744379392, 113694073735615278931860697464543927009280, 269745904618747258475998830581614801584128, 497889799480465304290177509409900353028096, 731620274208764977920059952776383417024512, 868539536046328200994123582110956292931584, 840344934146876897409811091577071621636096, 665396374436354363321717134898784911753216, 431179331800143571749407371116797461790720, 227718863337801821726133693244732151431168, 97160668209034971418924730012205102137344, 33003104189609735206415926308533591605248, 8721249758001773580096152223181350895616, 1728891936438634105207558914289080205312, 241987565684683176197710648868501192704, 21330792391024360310233022775460626432, 890867760400857260237156878462746624]
private def outer41Q21Coeffs : List Nat := [27493520829719825218700999554801533347, 433252703946744027718428572124265948592, 3243707149726977011350375550428227037952, 15341407714352354121004587605031779004416, 51406944165908776589958408740082342494208, 129728228797753227143669364889558205857792, 255818559369760543384763722979190822141952, 403658574315106066848911460398977404370944, 517623551723629959234161880334268354265088, 544745121048859184882634285526240030883840, 473064635227550940191769700227599585771520, 339590766218704722041211446968827535949824, 201158598993595292447701602043732749713408, 97791218822623181536304493855019993399296, 38634687889462737072695526764649966993408, 12213429640104158935403453845851697315840, 3017035021082684926763444655967367593984, 561275836439927140145199341825769340928, 73977903643188219477811581954964848640, 6159523440847387841329422077618290688, 243656139596815660919564274451349504]
private def outer41P21 (j : Nat) := outer41HornerNat j outer41P21Coeffs
private def outer41Q21 (j : Nat) := outer41HornerNat j outer41Q21Coeffs
private def outer41P21Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P21Coeffs)
private def outer41Q21Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q21Coeffs)

private def outer41P19Coeffs : List Nat := [51193841245943427681686824766661, 687948139920111125547541470789572, 4351877893118752680513842268247456, 17211533874919231569469533081835008, 47665292482275679915829863571939328, 98091629211278995598479137687339008, 155331633686526193224975561489645568, 193327703812796517855590588413378560, 191463135268214492121914251640045568, 151742666132941207848913257929637888, 96241347410451101765576199029915648, 48570489313204378403473187441475584, 19265901339416958712039224069062656, 5880364529678096554180815844540416, 1333723772779664422027254931914752, 211820023527340401201403664531456, 21032437601283608465775821586432, 983093363921709439973993742336]
private def outer41Q19Coeffs : List Nat := [18724704564319620669300068350837, 265609180301529453769878540608420, 1779687215370040381032463643680032, 7484278738545159457760473941912064, 22136779774438640199319625189957632, 48902514354668169180992538125664256, 83619451082486948781163753655762944, 113161754022385418972216801735213056, 122867346812429001843391611105443840, 107833294981744310375758294866198528, 76679438278162779433305649329471488, 44074179777911630620990408230961152, 20325131919179953191381510465257472, 7418187252044203944600736811188224, 2095657570155842907045295680389120, 442174319873528538824189090463744, 65618005344763012939613277782016, 6111614894599919570836044906496, 268880236286279504950152134656]
private def outer41P19 (j : Nat) := outer41HornerNat j outer41P19Coeffs
private def outer41Q19 (j : Nat) := outer41HornerNat j outer41Q19Coeffs
private def outer41P19Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P19Coeffs)
private def outer41Q19Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q19Coeffs)

private def outer41P17Coeffs : List Nat := [12012756503655835242110687651023, 142511626995390222460330231548272, 789239335384066847401512310596864, 2706668518826299668193518641532928, 6428420921825073590619964856139776, 11200013942050790656208380275720192, 14787759075412217631202055284588544, 15066946832727845636862013985521664, 11943921539136473255284927836979200, 7366604157948740881241763949314048, 3506118094398977576545730389082112, 1264604835982609250893397833547776, 334601222949982767529123504979968, 61311547228901969921999693152256, 6957031212002361100273289527296, 368515060636988194543311519744]
private def outer41Q17Coeffs : List Nat := [4393796422765763431707995036343, 55406712512757734373950749248080, 327605982412766783123696632732416, 1205624914721612131366603661766656, 3090824493371096136845015667638272, 5853144577498075533958515252002816, 8469523670800792593003213739786240, 9552424770802053027745270578806784, 8486780301357689218417621290975232, 5959243553180473814819026633752576, 3296199744664593025793115019018240, 1421084316730229252945374376624128, 468144094503399926189515612356608, 113917407421645479838521858457600, 19310786200610424114178684878848, 2037407310686128856770713485312, 100790443934902754063127937024]
private def outer41P17 (j : Nat) := outer41HornerNat j outer41P17Coeffs
private def outer41Q17 (j : Nat) := outer41HornerNat j outer41Q17Coeffs
private def outer41P17Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P17Coeffs)
private def outer41Q17Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q17Coeffs)

private def outer41P15Coeffs : List Nat := [951623226909923136408843237, 9681698974911296377369982880, 45473959067519341079048284160, 130559679298086543984182902784, 255644847741904662606441218048, 360502846475337597412106567680, 376665487523568999360354058240, 295237471733606979344539844608, 173601549656426355115132190720, 75631907421341543367792656384, 23729574068368037835177984000, 5077408592841162164352843776, 664065410953000255085346816, 40094196407094914366570496]
private def outer41Q15Coeffs : List Nat := [348066551498414097997569109, 3801142419353211872749330624, 19277597784383551660580617216, 60178085307587354263149887488, 129179910845405603773872472064, 201718509312408663753597386752, 236294165788807346699345330176, 210937834507162731325977264128, 144199555041260756504995168256, 75121483429369355936328581120, 29357156611378993257236135936, 8345409402058910309348802560, 1631318155051482958488666112, 196272333613844299933286400, 10965934060060147519062016]
private def outer41P15 (j : Nat) := outer41HornerNat j outer41P15Coeffs
private def outer41Q15 (j : Nat) := outer41HornerNat j outer41Q15Coeffs
private def outer41P15Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P15Coeffs)
private def outer41Q15Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q15Coeffs)

private def outer41P13Coeffs : List Nat := [943803038524282148872147, 8274699036240404942195552, 32987474212201632561031168, 78930918540138318819880960, 125952043030662619667890176, 140738766878496009560784896, 112369337370769556634599424, 64107461780001361626136576, 25610803530755869618733056, 6823441329516712067858432, 1091171243637188528701440, 79344833340235302567936]
private def outer41Q13Coeffs : List Nat := [345206232491387951543963, 3284380632852644958193472, 14326176780976305469715456, 37883000531150799631151104, 67636949124757520032858112, 85898087640560025381896192, 79566949834967536558407680, 54164130250080312950259712, 26893142061269448885534720, 9498021001435539274989568, 2264921905804900233641984, 327427032486825231908864, 21701150999038715232256]
private def outer41P13 (j : Nat) := outer41HornerNat j outer41P13Coeffs
private def outer41Q13 (j : Nat) := outer41HornerNat j outer41Q13Coeffs
private def outer41P13Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P13Coeffs)
private def outer41Q13Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q13Coeffs)

private def outer41P11Coeffs : List Nat := [203891145560305476103, 1498052397128047681952, 4887794463999855607680, 9296099093932123471872, 11358695426651713961984, 9247544356842606952448, 5016803087872539230208, 1748901198846693998592, 355524704673573371904, 32111838865655857152]
private def outer41Q11Coeffs : List Nat := [74575405380426080747, 603626069733580513152, 2197040678662236985216, 4735697427230159712256, 6694981795247451275264, 6486882533680309338112, 4362778381701466816512, 2011217617134542651392, 608233594897964204032, 108968938597779505152, 8782725159837499392]
private def outer41P11 (j : Nat) := outer41HornerNat j outer41P11Coeffs
private def outer41Q11 (j : Nat) := outer41HornerNat j outer41Q11Coeffs
private def outer41P11Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P11Coeffs)
private def outer41Q11Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q11Coeffs)

private def outer41P9Coeffs : List Nat := [259447744752407491, 1432539575756566256, 3393095667113964288, 4469099290549278720, 3535084141548535808, 1679319352686411776, 443603574463660032, 50266553878315008]
private def outer41Q9Coeffs : List Nat := [94895836142258387, 594840481709068176, 1632456450862737664, 2561833773631731712, 2514452003641425920, 1580576813008027648, 621390600591114240, 139691344783212544, 13748117300051968]
private def outer41P9 (j : Nat) := outer41HornerNat j outer41P9Coeffs
private def outer41Q9 (j : Nat) := outer41HornerNat j outer41Q9Coeffs
private def outer41P9Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P9Coeffs)
private def outer41Q9Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q9Coeffs)

private def outer41P7Coeffs : List Nat := [1012242811728263, 3982509884744320, 6273033171538688, 4944851589742592, 1950656865632256, 308068916133888]
private def outer41Q7Coeffs : List Nat := [370238824352135, 1733161485969760, 3382596230933248, 3523067465768960, 2065242559741952, 646059752685568, 84258165096448]
private def outer41P7 (j : Nat) := outer41HornerNat j outer41P7Coeffs
private def outer41Q7 (j : Nat) := outer41HornerNat j outer41Q7Coeffs
private def outer41P7Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P7Coeffs)
private def outer41Q7Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q7Coeffs)

private def outer41P5Coeffs : List Nat := [111697841339, 262990801128, 206688610944, 54217672704]
private def outer41Q5Coeffs : List Nat := [40854701047, 126704333640, 147468784512, 76337551360, 14828765184]
private def outer41P5 (j : Nat) := outer41HornerNat j outer41P5Coeffs
private def outer41Q5 (j : Nat) := outer41HornerNat j outer41Q5Coeffs
private def outer41P5Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P5Coeffs)
private def outer41Q5Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q5Coeffs)

private def outer41P3Coeffs : List Nat := [2149551, 1667952]
private def outer41Q3Coeffs : List Nat := [786223, 1197264, 456192]
private def outer41P3 (j : Nat) := outer41HornerNat j outer41P3Coeffs
private def outer41Q3 (j : Nat) := outer41HornerNat j outer41Q3Coeffs
private def outer41P3Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P3Coeffs)
private def outer41Q3Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q3Coeffs)

private def outer41P1Coeffs : List Nat := [0]
private def outer41Q1Coeffs : List Nat := [1]
private def outer41P1 (j : Nat) := outer41HornerNat j outer41P1Coeffs
private def outer41Q1 (j : Nat) := outer41HornerNat j outer41Q1Coeffs
private def outer41P1Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41P1Coeffs)
private def outer41Q1Int (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41Q1Coeffs)

private def outer41A38Coeffs : List Int := [-15835421009931459872381979524275565561191489806475, -453517071413183755259477242912584849754047299795812, -6314667681329475507185529490528564829679148609507680, -56948758132085368048137181261341401017526497718219776, -373913876301898979315493852078676327950140441381634048, -1904768544442701251632937126095023942895022558743887872, -7834306959096505627949426284703887206638393751018405888, -26731849227143144646109557009882031559622749003054055424, -77161292197495375946173677984991533205517467277106085888, -191176614104858152451881553446357655386917341006709915648, -411126579827117435673416870532053086763314416247807934464, -774088327097478362685306526297616100516469704837222629376, -1284815768040697492257596114375953070739598313323533172736, -1889981714817670407092477655010172513645024592309071642624, -2474363719436495864389650762595285966849229359748390846464, -2892400192058560399063456950748947193970912806379880185856, -3026066047867598721178599879942385464032270363393813118976, -2838163946875511693290791080938951314401993197918252695552, -2388657455152500354344949161897566888556249731823046754304, -1804535297156318355236037077728511700196172882499908665344, -1223303503580487736917427010878700449608915441813058224128, -743433515843747762257679415509216891693145593005379420160, -404366591226149788987246020773040087936461664327967965184, -196380042971250888501465073651030624233231920180550959104, -84880647824697253983825347997715476496462243960241258496, -32515204989291595908283767740857773479776517641270722560, -10979934916518402336005816809905983297965035186575900672, -3246289919600764132016023723110839460682854618953154560, -833068019616625846801233245408556011318820608206176256, -183501037831949408134072705257406693029830254105985024, -34193124419075018471663730981278247962978467736190976, -5285781852486205155178114299544159322212471364648960, -659732050767671130062979654397688247587031358636032, -63886544615264966978003991387566843027927158751232, -4504068212234589620988324578554127999315306610688, -205673152432317123455638786212273645687335288832, -4566077579399145088229438316324752018349490176]
private def outer41B38Coeffs : List Int := [5791977566951610604679975371370646695225135598038, 170204578628135229983854662616945802448138769578884, 2433550115222857949009207723422125741521114307660512, 22554724403595016058138499831356405438868508732162048, 152321344989337569792736059655442332962088001775108096, 798845651733832007343961707386114830307989646089125888, 3385896055554934731329434056007256134831416560807051264, 11917992897857141771599691505837794892330027095546658816, 35526633179328877348931470636891262015904859768724914176, 91008719337896446342582128780281401127135379317537636352, 202613456188281283819455868358669953931686679282444140544, 395476233122139775330195475988801269790610989504652115968, 681470841257207616138332780949202434040025842776799182848, 1042395364900035224796295034987392681492470891459381297152, 1421536296702473129705665496421405702395727722443853266944, 1734165463536244910747415296065318212020670782038016524288, 1897330333421211382616513465250117897032770098067035652096, 1865162813931730747892939751748408837529884525235909165056, 1649420392500309660998077125543813270944742486158994309120, 1312931798373646544879842693658210127671885881488539910144, 940695703828591372667009605147323521280169410965907963904, 606313083799282739511463562382761279814620781034533289984, 351128478767178661661452069077005042696002638317692649472, 182370648859765120721617848113079436713167786911249465344, 84732661360849845651055111988413883405936801453684293632, 35098369261155079645682932522721515689058469499149221888, 12905689605042993603973138732123024416690087268441915392, 4189383716002656277360791006035556689882606179092267008, 1192300514859934076802734275614293584671767096534761472, 294901837815297392834875441082760721139420628470726656, 62682607739312374427828163846171460303163104444809216, 11283344556329090797606592258546980063612400413179904, 1686736217542872816935324651415256412311667458703360, 203781557970425779185167470594198569313543588413440, 19118824577148183981628994395032918011511331356672, 1307022981544106383538320566259255778981412077568, 57920610466883660954353644283635956921407635456, 1248841731117714895926000223268308244334903296]
private def outer41A38 (j : Nat) := outer41HornerInt j outer41A38Coeffs
private def outer41B38 (j : Nat) := outer41HornerInt j outer41B38Coeffs

private def outer41A36Coeffs : List Int := [-4570402646970957263838766908067363428574658296318, -123505887814372421530964957630364512470435895722516, -1619896522119410204043522339556251260529605643505568, -13737036042716355203844955322588859410223057737155584, -84651205284161332243973061238771317954572173764935680, -403909583845929688240871719296379296338880789368537088, -1552715952188990107022632529573818948312999408202416128, -4940540405840887665004043552828926771860597639032602624, -13265756312835952050930607562678566491913049202600443904, -30493548338068430080028630362649728341353599375606022144, -60667263147231234582339343236775824869000089344707395584, -105351496211734684846663316685269313212029065264445259776, -160737185139584445947177083249496824962293748610518482944, -216563896667829527205006110913636306591736346190842691584, -258659832957248681516693156833635121954572881626010746880, -274650700081680435564621349175906898903376674249659908096, -259769771709001101390269448542194359203769877723393032192, -219102726919354540511038263200180813730055540259910844416, -164862198725537668069260863712501344817092671429394038784, -110623058280581578186876083662266000758150729688495947776, -66119021806024872850558123336123633467025222163501154304, -35133058795846225484144242906170438669543555453874601984, -16549266303450470773075688664755220778339768215881646080, -6883916234934251843432342709798860477209892497645371392, -2515832708703138750448393139744460904593514601767763968, -802542073644987402973155842100855068691226471633518592, -221576835964828868010599083488834421455828334749417472, -52372016568352298892732549983781584666727531126194176, -10445984116482410603661468213445769722969911587766272, -1724542951669671219867860741154306729801353386786816, -229379985400962894878428852512558320001351705165824, -23623700962731786678818691859478308548024113037312, -1767969233579234970167856439429452158658685173760, -85547560759994558416941775557934658321242914816, -2009125095622893918565241134164099869681123328]
private def outer41B36Coeffs : List Int := [1671674506575472648973186215676904473754368792283, 46422122989762395929841375194090630084922073233492, 626234158529473813502748500515325224293298288138016, 5467009728343635426339684879208155858441413429712896, 34715049836456555476218327607969339293818507355275264, 170861796748000869535753673641721676652528683839127552, 678278363565812190300186593553144593025067763005128704, 2231302197856944509743666856419483360375204067514777600, 6202037221358228683920088097378986873532584376089444352, 14778181334728605058356079513110449034008652428380995584, 30522290656211790829501834228968759453459394803724713984, 55111804019268032954994789052339467171743069283245096960, 87581459587836920355663285071736866453657451651670212608, 123137852058757560219204113093383065301547067320083415040, 153793672195123941183843282586506910002767108610524708864, 171149670922089176977282917270424030436127584976633856000, 170079882428962700901270342173850850317032710014316314624, 151140819948671985939588838594069620270429359265212792832, 120188574991281452497837997632368632023812623054890074112, 85525804157022576432145682422973294497910939535982723072, 54423071012562887143763100392595915414553071859947012096, 30924886623541325156339492681029917721832852148122025984, 15657548956174887232843648250844653731464672850172968960, 7042174578851803799562407349182463437838307991016701952, 2802215010630893520511961779105280228902670966628286464, 981377173150377054932025519957041936068053713280827392, 300470311967361900136602706793013884462801605269389312, 79740032302918968263047999519968848781097996241600512, 18141014674671907326605442608640329583258367523028992, 3487160478174191832125709383679173700772373385445376, 555481168695644318713396867923748735012604722806784, 71367772913670467120100761156898940583410772475904, 7107121214198862808608715221993498193755904147456, 514801334074200606668287744978453129989613158400, 24131616779065652655400305252455403915772428288, 549504299657543635846903558061976032733298688]
private def outer41A36 (j : Nat) := outer41HornerInt j outer41A36Coeffs
private def outer41B36 (j : Nat) := outer41HornerInt j outer41B36Coeffs

private def outer41A32Coeffs : List Int := [-7029491145955094757730989080350640113871167809, -167311560652003733468900893947315389910958811972, -1925068374751729613082534071959048479286352154112, -14259572941822839208548355278955952606863421103104, -76402088214496324165838558188891246016529640030208, -315409552671516843949447187299477987816123250769920, -1043520978703837378284064481767024908233799295303680, -2841340393353417564628293316554441004175189155512320, -6488454637351889901130777882832867872172757311553536, -12600067334212687767463218101756828741547558409601024, -21023975041755820358712718202127301614042373341315072, -30377081864365544976204539384436329523079624909651968, -38228172867593407602028279116134784976188325008244736, -42077414372833484778763057404751432951647633126981632, -40623514116066016338628274766829273047108126939021312, -34457595764470219798931669509853592432542204886515712, -25692490353946807114565751738191738056394897864261632, -16830865941307042578850578654881724393832858077102080, -9670961176492380005369460153551775360721382803505152, -4860274548787615030485987756392585305696120162222080, -2127444283954753071093828389217484967337799756808192, -806389362173146558882095149843644615999282823036928, -262628405629599747726034592447598511605838335967232, -72736453108798818841979955415741646355012169760768, -16895007427274086758905349336856986042826429038592, -3229686011125236605898485220285854705339141718016, -494787642932482148725672266437919525926319685632, -58404751382225311891189783844008252208997990400, -4986728716003836041763891379293256803575398400, -274109018439901861982830157576360359303839744, -7283647362605994457803779720113363171147776]
private def outer41B32Coeffs : List Int := [2571112886668562480205858122419560532148298571, 63116275670479712525289590975929999892440674308, 749821147885579800110616697016496716005045491328, 5741508114021490528006942805811500297899416673280, 31840657594554654712708730230607185627838587666432, 136238609903139570497705580104378855206108355100672, 467856951226824900477977538833026539069677523435520, 1324378650090294575285469600124977709032843415388160, 3149610390068304828738897719040625069203735185457152, 6381633011954705854314695236786701851776335069839360, 11132953395501429671152408607230096001849364460863488, 16856176507149579790407684698652678804138424988073984, 22284148339390078977747787629819165894238859916476416, 25838103208206169674520049398194156814488271824355328, 26358793260609360403360305671293226078917846609428480, 23706621593888161182033958367048377152262983714340864, 18815777755854437960048144968162708040137014408904704, 13179016949492760280023951422602401643556062629986304, 8138099966340927654451092217697749284779183195553792, 4421434412382363838912036815061859965940769503576064, 2106836186828279071896612388778327792667988527677440, 876569554972608957666497726161770483726017548517376, 316527751253021174197723948633170069303956051329024, 98410264884585073321963844863786542793357522894848, 26067471267704189852645931603115684609903036465152, 5800995035288675051739794188006499880981900558336, 1064122770522361400717560432752296486852238508032, 156666116917897309986645317615500149142369337344, 17795897103223652149798436439755562936793300992, 1464035866879420003547335484536520633669910528, 77630921579325381660252232620803573267038208, 1992108680370870279057444026013911294672896]
private def outer41A32 (j : Nat) := outer41HornerInt j outer41A32Coeffs
private def outer41B32 (j : Nat) := outer41HornerInt j outer41B32Coeffs

private def outer41A30Coeffs : List Int := [-1079297508214584401712582410333123935445409881, -24024992759789496463423798049112760448519227920, -257892271232521537258896720464166723498080415744, -1777497249234617178262057869268596342609654992896, -8836589657174264707582961111887828997871735341056, -33744179273387246209744617437715045205927043006464, -102926120969624148366384699186495046070170499940352, -257440932690909280810920030505180468937556114800640, -537912286421385744655405241273241135447740753379328, -951657576254489560626946142115140222903014479888384, -1439770512162468516797417270809576353995413090467840, -1876330195030704150967984905733277512441892989566976, -2117338674011755382159648430530419767417217474363392, -2076144460637112929890261848456646514494238497964032, -1772509741123182150767970645902153324096871062306816, -1318470707391460881937535193270151149745623883841536, -853918033169626444264342967827149966147147859492864, -480560537878732888714716778744521981668199164280832, -234177497402418350185675034128900943854027994562560, -98298237677724878021800492064895464305242480312320, -35284968389083173613465019596405038393280790790144, -10724307224785349643293085797550390859150286389248, -2722894309713953014284971164304940790433011728384, -566914749366073431070094998360340172913537712128, -94279545455217249304610052995671410985010200576, -12043586993235909054197229048297914425260638208, -1109684730011492424488108568032293543529676800, -65650672300078587857596863086756367861547008, -1872975089521073926174289901739868292120576]
private def outer41B30Coeffs : List Int := [394764809329985837463064797803899913780399913, 9082235097912229747536442784883879923329125808, 100890108742473999058846759954684445912041249280, 720593569588977777707632100629810665444444262400, 3717700964991631199228506441307949559571287441408, 14756609071412597075314692504464996872774329827328, 46866232503857087126683576879367637402107879882752, 122285412150739643469958689631925236488427561549824, 267093587505178691655275757909685488058903126081536, 495071169871743902195261166357002063838605270319104, 786676662480027526087225208117027699547970035777536, 1079759503199268002845590738560057129809677079543808, 1287239442654000504928464252647734322044384917323776, 1338064716996386151510794217359970782180228326227968, 1215772793134883900268518796875381821807558922338304, 966733781789913144510913316822641144816038236389376, 672729575278539707375358586901806617062855061536768, 409196210323008953853773659752693548292426948411392, 217024144671891600805559730681939409860366128119808, 99973727925573014026035020200679675197301492547584, 39780081005799023852810517719809880227195754905600, 13569681559945917193795677827806974909048686641152, 3928156045594064142018327960272547610919413219328, 951878860621798195417367008291834130543360868352, 189502699474743882061427075209089712756306739200, 30186312130916171663018658038613174459266236416, 3699408620847543486453764089610361119554142208, 327488706608328029262068119477330789693128704, 18639993097683477510675745430302938315620352, 512266691151062954167327152612613549981696]
private def outer41A30 (j : Nat) := outer41HornerInt j outer41A30Coeffs
private def outer41B30 (j : Nat) := outer41HornerInt j outer41B30Coeffs

private def outer41A28Coeffs : List Int := [158393894894792831526223368876076114852616599, 3272498598687013427543446570681153086839982032, 32511884526241184466452607740133514772160520192, 206761530798514823228832344952230469752286728192, 945279215111368514675462733916086296725351432192, 3307654961861439959378774850608876076081188175872, 9208322541044451567298038385208215631629121486848, 20930981724028658384438760753463899450634955390976, 39556253583194494388146828298039352876563039256576, 62963938942107521494567526015203760738532058988544, 85206423424349002301045046019886439439416487313408, 98676998035490351771128719268665689704940305383424, 98226121165407233585943659382029110031416589025280, 84255348203361741001139610553026943358003895599104, 62328020325271217769459575908310162225367953178624, 39730917223642263981000772464927961811723212554240, 21769141071411807060260032283754129370681859637248, 10207446191061601663609281912897044144747603558400, 4069083083071088361334522352298809019658473046016, 1366240410640912383425168886897044774919923040256, 381394203445125253205400769951767499208984100864, 86930004348721124897546933839511790187410620416, 15763963890455593806215198140354829845731999744, 2187916547841607525199679816244340557531316224, 218302497811737572205759080884876736404127744, 13942845610207374288767769477787427851468800, 428218673305097579784138508174099539296256]
private def outer41B28Coeffs : List Int := [-57934290815341078462548344500203467771921887, -1240220559467457212306569924706939445694312112, -12785567370918549289762627597474923985274345984, -84507388323558018503203521557915667035702710272, -402235117555045389684966848905039761612784533504, -1468080742644999525025431175050494646817645395968, -4271805895052741347982869987412379147290086998016, -10171871349215663079493837917223989674416113975296, -20187700791810422521444127954534873029561408290816, -33839332414036175529287293214632480439289627279360, -48372208735131829086548526485479924322686736531456, -59378814129616169857003873532423956041959397654528, -62896620448243876920057900461008037233695110725632, -57664683310590970382535610789021257700898873802752, -45827081237196256728973193272304841897026303033344, -31569239768113025621476986728299623886767639232512, -18823168142850788253919844721134445434363195686912, -9684590882652133989270681709731638697191649837056, -4278888646988120200009910457087301291952515842048, -1612202093073692347284149707938323514571916050432, -513046108066357205541536554974930888732386000896, -136078454619201002422944562115717073868922290176, -29535846899744637555596283949859307783486177280, -5110934508700335132295639616954976360206434304, -678164389230233388191906794139836343862165504, -64800641665109888027415407157911314514313216, -3969868912982336352812258426781708062818304, -117119637143274551735832754372403292798976]
private def outer41A28 (j : Nat) := outer41HornerInt j outer41A28Coeffs
private def outer41B28 (j : Nat) := outer41HornerInt j outer41B28Coeffs

private def outer41A26Coeffs : List Int := [-1771685861911604415831644251307511737538037, -33786797540189033120355107415556374301558000, -308802926488535220240955855224074982935306112, -1800142207401784780124806457860203913162766336, -7514109494962681987503362274870620014226014208, -23902113806706324285194555128748255204359012352, -60203929507829905868846593108645728145444438016, -123160896996273423116374124612751152088266833920, -208253670019448331536759455175509515926211919872, -294658081085693379569462028758735950046639947776, -351839955617877573618466389632818854778279821312, -356535980050403565897094598879330335516537126912, -307592422676171050332172600785827105450408017920, -226157498678426711627507875431261106332390916096, -141566471570343967946081070306177100021676113920, -75204047484787247466430963459068537000450588672, -33714995810532283050907954239492451722931994624, -12647679447686831811667423477208039243854643200, -3921663908265355467807864760121508358004932608, -987618752402071083771205036977938843264090112, -196941832014588390897944092365419705983303680, -29927790188887991859509295063556794590691328, -3256541090447212750468547128527887578169344, -226010925732701645147492139554467680878592, -7517549517127525554010788866505220030464]
private def outer41B26Coeffs : List Int := [648013384768338194376196838917002330881337, 12841861695737685657646354755907092528292944, 122178053107854601308939179264445233200332160, 742785889891466288975567302085847779848005632, 3240186675939358386824068901331820004815962112, 10795500716689638664431266750933501700654759936, 28551222895310683968947571260470398003020038144, 61498299171656569974543689840931873608668545024, 109826727967391388236698510010666008823690428416, 164685898954976152967718600983519102179479650304, 209217416874573925354216567911688004881252089856, 226567323534765200739502772429520723955421282304, 209954072136293657607158443578262995227543339008, 166795320857639532274088094415394979663327526912, 113599365740593338334558625847964062680988254208, 66205701161317788413655901729863038285790576640, 32890663882677089392975204084998267025076781056, 13843394349074797039004721361566693128407089152, 4892327487319322656085641021977431534819344384, 1433489279208370401117946340173668490936320000, 342081188892364267317484747200849697415626752, 64799603655512028719797107152177410271608832, 9375210449391568026431023921949859909730304, 973250619567137379658057167611623794278400, 64561339110116861328644789656901132484608, 2056081919214365963490130288274931974144]
private def outer41A26 (j : Nat) := outer41HornerInt j outer41A26Coeffs
private def outer41B26 (j : Nat) := outer41HornerInt j outer41B26Coeffs

private def outer41A22Coeffs : List Int := [5260489488219904893438539043469785956291, 83540793655246162225874608280334817652608, 630330032288794152657304575604235991334912, 3004473318682316659596048946471221750407168, 10146345369872124669734907784346831530950656, 25805673291708531766796704768330288526786560, 51287786475525453452182621998950255320629248, 81565376707573667862558622948514918616268800, 105420292683564427658044307775611158287876096, 111822975402974368223307150732959678413668352, 97880206800379558686141204468614497703034880, 70823336341045217593192630001405627887255552, 42287777044456000085541418302533445129076736, 20722479137544647005128067569005408011943936, 8252678668032456921602270890065737111568384, 2629911537925698700875831819657175134896128, 654908107409922141453405652296516340023296, 122824112158574501414062270292323538567168, 16320278907948210689871993799010854895616, 1369941963590887293023932212325990268928, 54635306953667046574258689333560082432]
private def outer41B22Coeffs : List Int := [-1924081278789210087231074704862659067395, -31992966430230677000914809204757219183072, -253372327652908114037818071025351087998976, -1271127033442189777232472480116369824817152, -4532017135828959957064974309389344394379264, -12211051803810223269571609232168217620774912, -25810525848297787952282917759834530668085248, -43848773333965142756427405208437491352207360, -60849232235494613085342818979622689066450944, -69712022276743470835003916371681374342479872, -66364021612250486242141419066836821966061568, -52658490197306009059354907555735668206338048, -34826891227495894094605820467328148645609472, -19139613965678779669905495370310998416162816, -8683725749228586754451121787498249989390336, -3218217804336426949141826476642338181480448, -958607337389954371629093965620978959515648, -223999625203785470856661017381477730484224, -39555927180368489196289101598312739373056, -4964177080878965588970512195168776486912, -394644888725222508948752276156449816576, -14942989936045687951934000501486518272]
private def outer41A22 (j : Nat) := outer41HornerInt j outer41A22Coeffs
private def outer41B22 (j : Nat) := outer41HornerInt j outer41B22Coeffs

private def outer41A20Coeffs : List Int := [-836451292738682563117380364120259319, -11927394217123764195503284840162029064, -80337391671422615942178468831042654080, -339617750911477557572021737692128704512, -1009755347139281535347463531305967452160, -2242276600465086956852339240306447220736, -3854043899937182088256232821127376797696, -5242706158748497240954459491709438918656, -5721818310886896106751442159368329494528, -5047629983299615411944945447731359383552, -3607829537211400863504842427752853274624, -2084391333384407217926150773884577644544, -966166311589161795431556913682010079232, -354434063906942905183816650605356646400, -100640517244952482956019711488890503168, -21343063144574365254899246804349485056, -3183412017366442372609434220392087552, -298008319107989058429928501055324160, -13177406431583565162557018826866688]
private def outer41B20Coeffs : List Int := [305941163190525950709051288887480279, 4591068286773644469766123983020104360, 32642706312686257195475083803697985664, 146167622473909554411856916056946812928, 462121105954025313225660221003138957312, 1096045975733584283967061275046035587072, 2022386553195934479453749546251144134656, 2970809546514962677706263780241998610432, 3525639793103881074131158824685831979008, 3410093994343221304217809847322723483648, 2699297663576482011440379638613979168768, 1748602350836932219036542078386958237696, 923200677604696579202635094387658326016, 393779240287227864990336991343677538304, 133716064362779702700365703171606052864, 35324438598714514250553531103312871424, 7000570679674330577190122959411347456, 979555449477479967566897717757083648, 86320648426083749297947253934129152, 3604076972740804147024141901365248]
private def outer41A20 (j : Nat) := outer41HornerInt j outer41A20Coeffs
private def outer41B20 (j : Nat) := outer41HornerInt j outer41B20Coeffs

private def outer41A18Coeffs : List Int := [32050972563102519174188391743785, 410355033680794508847553137839352, 2463108289770432921958917992087680, 9200652990341049513466915628156928, 23938567951485224935414397398777856, 46001837852110252539235370336256000, 67538867560678399292931666629099520, 77279796752590677827755488950878208, 69647165675388600708130993334124544, 49603483305403631433519446060171264, 27825904310800383006692823502159872, 12165395191139973102875825066213376, 4063629193937354588780490301374464, 1002563539581083062677161159688192, 172293844927763285125920632864768, 18427137458950477049602070544384, 924002755347175752792941789184]
private def outer41B18Coeffs : List Int := [-11722992016950160718540068601929, -158847208418687970986293613554776, -1013013922184780076078324290189184, -4038187507781250422177759199320064, -11269699167844358542819381517385728, -23366929861483486016011111797096448, -37274103943865908554884583824293888, -46723818856473083857808347883372544, -46595825972119852374356707717939200, -37179976609369657049179867739848704, -23736998839029777817117139945914368, -12056565863605088519842962494980096, -4812302645826929352868336488153088, -1477769805699162887948366814117888, -337159081893689348304249592741888, -53855599859604406392971981750272, -5377466610110439916241336401920, -252718702317176274268155019264]
private def outer41A18 (j : Nat) := outer41HornerInt j outer41A18Coeffs
private def outer41B18 (j : Nat) := outer41HornerInt j outer41B18Coeffs

private def outer41A16Coeffs : List Int := [-12483024067268248114900116747, -135441904677694439473282811880, -682433432567735004276101384960, -2116419472177338833685525039104, -4513385514198864801964818956288, -7001416976238081567375142420480, -8147330038806662687741119037440, -7224854072042494243856290152448, -4906161818214085639396885790720, -2538852854339667235765647048704, -985543962015453036764410675200, -278286904545525273197602144256, -54033461573398334464428343296, -6457429332791512904421605376, -358361923843481469242572800]
private def outer41B16Coeffs : List Int := [4565801901950675494642209679, 52949347992793405754433638344, 286609440726789867414119812096, 960556736322395955318446614528, 2229114623971244113292444893184, 3794198363510258522961424678912, 4893388957692038873948939616256, 4869343299082949641802369466368, 3769303357046193297123795009536, 2269766397562891053999608299520, 1054557319766919466694230409216, 371242752628064133572628316160, 95856028249700864382963023872, 17137673554531032036802560000, 1897054817964254156025757696, 98013517632405188168908800]
private def outer41A16 (j : Nat) := outer41HornerInt j outer41A16Coeffs
private def outer41B16 (j : Nat) := outer41HornerInt j outer41B16Coeffs

private def outer41A14Coeffs : List Int := [-149352610335198613757622529, -1416194752710257499287703104, -6157407956051917378812018688, -16231997759515448571890028544, -28895656213954637617546788864, -36594273966195833133769687040, -33806702678777569474611511296, -22955196468666838229494792192, -11370195909901057361258217472, -4006582804502079378091409408, -953379308774316004293476352, -137548205006029065667215360, -9099280389776464725147648]
private def outer41B14Coeffs : List Int := [54627342593834819924555609, 558787411427630147930372576, 2639040464341354668778919936, 7619388896570111866333548544, 15004335863041697312062570496, 21281360114007131595874500608, 22366663506408782050623488000, 17636678923071005425477353472, 10433877560709744366962343936, 4573961534358455922391515136, 1444185413348506483753484288, 311008839199801435611987968, 40944260411413903276244992, 2488692072417494625681408]
private def outer41A14 (j : Nat) := outer41HornerInt j outer41A14Coeffs
private def outer41B14 (j : Nat) := outer41HornerInt j outer41B14Coeffs

private def outer41A12Coeffs : List Int := [132888373515771406028799, 1050249356149726693431328, 3737085219829349649989632, 7884094527729169347358720, 10920975452858374180306944, 10378514535458175615762432, 6852782827628493650526208, 3104288031911501438648320, 923306859238075834302464, 162819225970429730488320, 12926974096804964990976]
private def outer41B12Coeffs : List Int := [-48605368801329137163239, -420441351792452548246912, -1653811254330731193369600, -3904800000009044326526976, -6148944235563365921849344, -6780779593288941292224512, -5343293945009457692934144, -3008763242311600100605952, -1186428888692499907870720, -312018282850839015981056, -49254363320287131336704, -3535582658955204100096]
private def outer41A12 (j : Nat) := outer41HornerInt j outer41A12Coeffs
private def outer41B12 (j : Nat) := outer41HornerInt j outer41B12Coeffs

private def outer41A10Coeffs : List Int := [4113762288585046151, 25906208177520704368, 71421263722338002688, 112588077803383289856, 110997933948505686016, 70079885166603403264, 27671097876619984896, 6247329229915029504, 617464624689709056]
private def outer41B10Coeffs : List Int := [-1504653326003312503, -10599237210524094864, -33200983213397392640, -60696373238258112512, -71368356348926033920, -55972166179069362176, -29279258267395031040, -9850842732082233344, -1934249486805106688, -168879213590347776]
private def outer41A10 (j : Nat) := outer41HornerInt j outer41A10Coeffs
private def outer41B10 (j : Nat) := outer41HornerInt j outer41B10Coeffs

private def outer41A8Coeffs : List Int := [6831595986963439, 31972646482791584, 62382619414958464, 64950375019970560, 38058445730217984, 11899876269883392, 1551101828530176]
private def outer41B8Coeffs : List Int := [-2498730578628307, -13560535782308480, -31552874493606272, -40804294382104576, -31673598542086144, -14757390187495424, -3821330776457216, -424232978743296]
private def outer41A8 (j : Nat) := outer41HornerInt j outer41A8Coeffs
private def outer41B8 (j : Nat) := outer41HornerInt j outer41B8Coeffs

private def outer41A6Coeffs : List Int := [5553438875669, 17426954523928, 20522950392704, 10749700429824, 2112991395840]
private def outer41B6Coeffs : List Int := [-2031230705337, -7891135480760, -12268457767552, -9541476321280, -3712027787264, -577912176640]
private def outer41A6 (j : Nat) := outer41HornerInt j outer41A6Coeffs
private def outer41B6 (j : Nat) := outer41HornerInt j outer41B6Coeffs

private def outer41A4Coeffs : List Int := [737342875, 1176650304, 469707264]
private def outer41B4Coeffs : List Int := [-269691179, -631793184, -493416960, -128466944]
private def outer41A4 (j : Nat) := outer41HornerInt j outer41A4Coeffs
private def outer41B4 (j : Nat) := outer41HornerInt j outer41B4Coeffs

private def outer41A2Coeffs : List Int := [4563]
private def outer41B2Coeffs : List Int := [-1667, -1248]
private def outer41A2 (j : Nat) := outer41HornerInt j outer41A2Coeffs
private def outer41B2 (j : Nat) := outer41HornerInt j outer41B2Coeffs

private def outer41AlphaCoeffs : List Nat := [880726507905651468676512142588845996400733435842335, 25946014265775153471170796642578301400233303057744384, 371899939872706897222641335397431296089632124095813376, 3455500323415753152612674926513134677243646397695062016, 23394997001154399368904797681150924813467181919835586560, 123002843268690072685344621327811393605779797976231706624, 522657505998217674469287076440179120591623695454628216832, 1844332643986928545646848586844770733882574788267465506816, 5511680380923574203100483023977989377149043186040381112320, 14154942760979901669989741006275724322799536346163593609216, 31592926416715375255384765104629274577712823288826200850432, 61821530033693579327935355166159793649179013020559511388160, 106798653537247856132236077596854736274743090498951312310272, 163776458905947370747437536882248327095709541524500000014336, 223912762681518408450210362108067712069844529324068754685952, 273851244976111071551587440227335282334332370656694538076160, 300380577204964860535511370479986089567933313462632880013312, 296040952672053129831139975368540783152491726545906084872192, 262466576350492783035297614986718170284227060951742746198016, 209456521837493591772714352896142269193644266574563520806912, 150456670022259681254735820748699534156359591833120123387904, 97223510334198024085973708525761702323887972061551595094016, 56448708665012867537800445124426517571812153956058919862272, 29393956238706380989340909521624210563808497908812313788416, 13692118652934933404585270750986497747367336791148096126976, 5686238004445891702234729788805568224578893307376780181504, 2096231288643449019638266177952135859484048370663056998400, 682228143468984738196259107032016496969353351006382981120, 194665221177757099872616449765137725731562629492377649152, 48273069764807465043574837717664683847168920452109172736, 10287289743258878606435507930609773828220326856471085056, 1856606812397731972047070604657359900644499885836468224, 278265360655608314946369696480349311112311403089756160, 33706097851850582517943536392621980513453711508373504, 3170575964168330533956585479421784604175458361147392, 217317823836501016104666677236075861454150741000192, 9655665152333796554706427619099924323051870617600, 208734975058246632604774323031988663695976693760]
private def outer41GammaCoeffs : List Nat := [322135304972939448917639188187910827469061048799311, 9730625825301830902132033709374559979505965305044832, 143114370045184772627859596932739322797172144270245632, 1365485552928185118177278723455880390756543689033437184, 9501007246616532884264920633194105549489352971117068288, 51381278183288679923362599873235595923691797110894624768, 224773847183276837722910390172347996902788307981738967040, 817387018779755604387668226246090493620544474463424479232, 2519888271383143601929453072129829232930947617308509470720, 6683342004493198074342927152497296291245156155287838654464, 15423294191938977543155606233784013858901407264466171592704, 31244943415987587509507819566723657568476128932005802934272, 55956597682051689645471369479318550523913128447363696820224, 89088595724207103677995429496214288981822642634143867863040, 126656264018280926014300310213796877969525258038220096012288, 161358186999429176512225994841820389735516818223754471538688, 184711937351197828302275536595984878317192810081208147902464, 190377919201338060343938687054790176483707070101371976941568, 176914308888323231767193793186260483763446832133854547935232, 148351070911251853521386696631324682688878565973306780942336, 112283864693327355855297310873833794247540821210857830612992, 76687635745330725322060184002648883727386519394588332916736, 47223491729074806084589273464902257009527205889047787470848, 26182340394266982909762482261089885674794288901512935505920, 13043628349905454414465826311991263531941765184667678408704, 5823017359423617738106659523276521623831745683379969851392, 2321300876886085375772096050426689937329282820474669105152, 822647846521823617225177760436778407405154909526786310144, 257730232600089546047339875929094432886218742569359114240, 70881975205114888902872086449245181064687430957323517952, 16962005665878059208592573068735887606949180639648153600, 3492024872556725938138694609047793495187949000471871488, 609465200883226005103356457549043117851050847808520192, 88422224893755303071480328265516406388859659834359808, 10377181940722533393907925578220289001473286200098816, 946563980559882966083542859070749161439811443097600, 62964972128555692317099599149754198348975887613952, 2717122794988971123564711914339476365888653885440, 57089907708238395242331438777979805455309864960]
private def outer41Alpha (j : Nat) := outer41HornerNat j outer41AlphaCoeffs
private def outer41Gamma (j : Nat) := outer41HornerNat j outer41GammaCoeffs
private def outer41AlphaInt (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41AlphaCoeffs)
private def outer41GammaInt (j : Nat) := outer41HornerInt j (outer41NatCoeffs outer41GammaCoeffs)

set_option maxHeartbeats 2000000 in
private theorem outer41Cross37Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P35Coeffs)
        (outer41NatCoeffs outer41Q37Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q35Coeffs)
        (outer41NatCoeffs outer41P37Coeffs)) =
      [135547848, 109910592] ++ List.replicate 68 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross37 (j : Nat) :
    outer41P35Int j * outer41Q37Int j -
      outer41Q35Int j * outer41P37Int j =
      72 * (1882609 + 1526536 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P35Coeffs)
            (outer41NatCoeffs outer41Q37Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q35Coeffs)
            (outer41NatCoeffs outer41P37Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([135547848, 109910592] ++ List.replicate 68 0) := by
          rw [outer41Cross37Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint37Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A36Coeffs
        (outer41NatCoeffs outer41Q37Coeffs))
      (outer41CoeffMul outer41B36Coeffs
        (outer41NatCoeffs outer41P37Coeffs)) =
      [43923] ++ List.replicate 70 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint37 (j : Nat) :
    outer41A36 j * outer41Q37Int j +
      outer41B36 j * outer41P37Int j = 43923 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A36Coeffs
            (outer41NatCoeffs outer41Q37Coeffs))
          (outer41CoeffMul outer41B36Coeffs
            (outer41NatCoeffs outer41P37Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([43923] ++ List.replicate 70 0) := by
          rw [outer41Endpoint37Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross33Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P31Coeffs)
        (outer41NatCoeffs outer41Q33Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q31Coeffs)
        (outer41NatCoeffs outer41P33Coeffs)) =
      [3544775454752, 3007055591808] ++ List.replicate 60 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross33 (j : Nat) :
    outer41P31Int j * outer41Q33Int j -
      outer41Q31Int j * outer41P33Int j =
      32 * (110774232961 + 93970487244 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P31Coeffs)
            (outer41NatCoeffs outer41Q33Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q31Coeffs)
            (outer41NatCoeffs outer41P33Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([3544775454752, 3007055591808] ++ List.replicate 60 0) := by
          rw [outer41Cross33Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint33Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A32Coeffs
        (outer41NatCoeffs outer41Q33Coeffs))
      (outer41CoeffMul outer41B32Coeffs
        (outer41NatCoeffs outer41P33Coeffs)) =
      [31451824818] ++ List.replicate 62 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint33 (j : Nat) :
    outer41A32 j * outer41Q33Int j +
      outer41B32 j * outer41P33Int j = 31451824818 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A32Coeffs
            (outer41NatCoeffs outer41Q33Coeffs))
          (outer41CoeffMul outer41B32Coeffs
            (outer41NatCoeffs outer41P33Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([31451824818] ++ List.replicate 62 0) := by
          rw [outer41Endpoint33Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross31Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P29Coeffs)
        (outer41NatCoeffs outer41Q31Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q29Coeffs)
        (outer41NatCoeffs outer41P31Coeffs)) =
      [-209913533074344, -153773826352640] ++ List.replicate 56 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross31 (j : Nat) :
    outer41P29Int j * outer41Q31Int j -
      outer41Q29Int j * outer41P31Int j =
      -8 * (26239191634293 + 19221728294080 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P29Coeffs)
            (outer41NatCoeffs outer41Q31Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q29Coeffs)
            (outer41NatCoeffs outer41P31Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-209913533074344, -153773826352640] ++ List.replicate 56 0) := by
          rw [outer41Cross31Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint31Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A30Coeffs
        (outer41NatCoeffs outer41Q31Coeffs))
      (outer41CoeffMul outer41B30Coeffs
        (outer41NatCoeffs outer41P31Coeffs)) =
      [1214679324800] ++ List.replicate 58 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint31 (j : Nat) :
    outer41A30 j * outer41Q31Int j +
      outer41B30 j * outer41P31Int j = 1214679324800 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A30Coeffs
            (outer41NatCoeffs outer41Q31Coeffs))
          (outer41CoeffMul outer41B30Coeffs
            (outer41NatCoeffs outer41P31Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([1214679324800] ++ List.replicate 58 0) := by
          rw [outer41Endpoint31Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross29Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P27Coeffs)
        (outer41NatCoeffs outer41Q29Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q27Coeffs)
        (outer41NatCoeffs outer41P29Coeffs)) =
      [106748467934229004, 97717727235875328] ++ List.replicate 52 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross29 (j : Nat) :
    outer41P27Int j * outer41Q29Int j -
      outer41Q27Int j * outer41P29Int j =
      4 * (26687116983557251 + 24429431808968832 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P27Coeffs)
            (outer41NatCoeffs outer41Q29Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q27Coeffs)
            (outer41NatCoeffs outer41P29Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([106748467934229004, 97717727235875328] ++ List.replicate 52 0) := by
          rw [outer41Cross29Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint29Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A28Coeffs
        (outer41NatCoeffs outer41Q29Coeffs))
      (outer41CoeffMul outer41B28Coeffs
        (outer41NatCoeffs outer41P29Coeffs)) =
      [572738492625408] ++ List.replicate 54 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint29 (j : Nat) :
    outer41A28 j * outer41Q29Int j +
      outer41B28 j * outer41P29Int j = 572738492625408 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A28Coeffs
            (outer41NatCoeffs outer41Q29Coeffs))
          (outer41CoeffMul outer41B28Coeffs
            (outer41NatCoeffs outer41P29Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([572738492625408] ++ List.replicate 54 0) := by
          rw [outer41Endpoint29Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross27Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P25Coeffs)
        (outer41NatCoeffs outer41Q27Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q25Coeffs)
        (outer41NatCoeffs outer41P27Coeffs)) =
      [-718785542982069235712, -497874529068625035264] ++ List.replicate 48 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross27 (j : Nat) :
    outer41P25Int j * outer41Q27Int j -
      outer41Q25Int j * outer41P27Int j =
      -4096 * (175484751704606747 + 121551398698394784 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P25Coeffs)
            (outer41NatCoeffs outer41Q27Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q25Coeffs)
            (outer41NatCoeffs outer41P27Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-718785542982069235712, -497874529068625035264] ++ List.replicate 48 0) := by
          rw [outer41Cross27Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint27Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A26Coeffs
        (outer41NatCoeffs outer41Q27Coeffs))
      (outer41CoeffMul outer41B26Coeffs
        (outer41NatCoeffs outer41P27Coeffs)) =
      [44929151108448768] ++ List.replicate 50 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint27 (j : Nat) :
    outer41A26 j * outer41Q27Int j +
      outer41B26 j * outer41P27Int j = 44929151108448768 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A26Coeffs
            (outer41NatCoeffs outer41Q27Coeffs))
          (outer41CoeffMul outer41B26Coeffs
            (outer41NatCoeffs outer41P27Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([44929151108448768] ++ List.replicate 50 0) := by
          rw [outer41Endpoint27Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross23Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P21Coeffs)
        (outer41NatCoeffs outer41Q23Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q21Coeffs)
        (outer41NatCoeffs outer41P23Coeffs)) =
      [398539016886648042651208, 305864413925103408461568] ++ List.replicate 40 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross23 (j : Nat) :
    outer41P21Int j * outer41Q23Int j -
      outer41Q21Int j * outer41P23Int j =
      8 * (49817377110831005331401 + 38233051740637926057696 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P21Coeffs)
            (outer41NatCoeffs outer41Q23Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q21Coeffs)
            (outer41NatCoeffs outer41P23Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([398539016886648042651208, 305864413925103408461568] ++ List.replicate 40 0) := by
          rw [outer41Cross23Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint23Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A22Coeffs
        (outer41NatCoeffs outer41Q23Coeffs))
      (outer41CoeffMul outer41B22Coeffs
        (outer41NatCoeffs outer41P23Coeffs)) =
      [3980114426571624327584] ++ List.replicate 42 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint23 (j : Nat) :
    outer41A22 j * outer41Q23Int j +
      outer41B22 j * outer41P23Int j = 3980114426571624327584 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A22Coeffs
            (outer41NatCoeffs outer41Q23Coeffs))
          (outer41CoeffMul outer41B22Coeffs
            (outer41NatCoeffs outer41P23Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([3980114426571624327584] ++ List.replicate 42 0) := by
          rw [outer41Endpoint23Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross21Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P19Coeffs)
        (outer41NatCoeffs outer41Q21Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q19Coeffs)
        (outer41NatCoeffs outer41P21Coeffs)) =
      [3193539037979412844664, 2403433453804544403168] ++ List.replicate 36 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross21 (j : Nat) :
    outer41P19Int j * outer41Q21Int j -
      outer41Q19Int j * outer41P21Int j =
      8 * (399192379747426605583 + 300429181725568050396 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P19Coeffs)
            (outer41NatCoeffs outer41Q21Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q19Coeffs)
            (outer41NatCoeffs outer41P21Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([3193539037979412844664, 2403433453804544403168] ++ List.replicate 36 0) := by
          rw [outer41Cross21Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint21Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A20Coeffs
        (outer41NatCoeffs outer41Q21Coeffs))
      (outer41CoeffMul outer41B20Coeffs
        (outer41NatCoeffs outer41P21Coeffs)) =
      [20310724547543276059208] ++ List.replicate 38 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint21 (j : Nat) :
    outer41A20 j * outer41Q21Int j +
      outer41B20 j * outer41P21Int j = 20310724547543276059208 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A20Coeffs
            (outer41NatCoeffs outer41Q21Coeffs))
          (outer41CoeffMul outer41B20Coeffs
            (outer41NatCoeffs outer41P21Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([20310724547543276059208] ++ List.replicate 38 0) := by
          rw [outer41Endpoint21Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross19Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P17Coeffs)
        (outer41NatCoeffs outer41Q19Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q17Coeffs)
        (outer41NatCoeffs outer41P19Coeffs)) =
      [-9057265934203804472, -6240319712995158752] ++ List.replicate 32 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross19 (j : Nat) :
    outer41P17Int j * outer41Q19Int j -
      outer41Q17Int j * outer41P19Int j =
      -8 * (1132158241775475559 + 780039964124394844 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P17Coeffs)
            (outer41NatCoeffs outer41Q19Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q17Coeffs)
            (outer41NatCoeffs outer41P19Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-9057265934203804472, -6240319712995158752] ++ List.replicate 32 0) := by
          rw [outer41Cross19Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint19Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A18Coeffs
        (outer41NatCoeffs outer41Q19Coeffs))
      (outer41CoeffMul outer41B18Coeffs
        (outer41NatCoeffs outer41P19Coeffs)) =
      [829924053674808976] ++ List.replicate 34 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint19 (j : Nat) :
    outer41A18 j * outer41Q19Int j +
      outer41B18 j * outer41P19Int j = 829924053674808976 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A18Coeffs
            (outer41NatCoeffs outer41Q19Coeffs))
          (outer41CoeffMul outer41B18Coeffs
            (outer41NatCoeffs outer41P19Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([829924053674808976] ++ List.replicate 34 0) := by
          rw [outer41Endpoint19Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross17Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P15Coeffs)
        (outer41NatCoeffs outer41Q17Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q15Coeffs)
        (outer41NatCoeffs outer41P17Coeffs)) =
      [25544030447087713784, 29728010499682684800] ++ List.replicate 28 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross17 (j : Nat) :
    outer41P15Int j * outer41Q17Int j -
      outer41Q15Int j * outer41P17Int j =
      8 * (3193003805885964223 + 3716001312460335600 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P15Coeffs)
            (outer41NatCoeffs outer41Q17Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q15Coeffs)
            (outer41NatCoeffs outer41P17Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([25544030447087713784, 29728010499682684800] ++ List.replicate 28 0) := by
          rw [outer41Cross17Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint17Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A16Coeffs
        (outer41NatCoeffs outer41Q17Coeffs))
      (outer41CoeffMul outer41B16Coeffs
        (outer41NatCoeffs outer41P17Coeffs)) =
      [29853776087536915396] ++ List.replicate 30 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint17 (j : Nat) :
    outer41A16 j * outer41Q17Int j +
      outer41B16 j * outer41P17Int j = 29853776087536915396 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A16Coeffs
            (outer41NatCoeffs outer41Q17Coeffs))
          (outer41CoeffMul outer41B16Coeffs
            (outer41NatCoeffs outer41P17Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([29853776087536915396] ++ List.replicate 30 0) := by
          rw [outer41Endpoint17Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross15Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P13Coeffs)
        (outer41NatCoeffs outer41Q15Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q13Coeffs)
        (outer41NatCoeffs outer41P15Coeffs)) =
      [-1945988748943021208, -1345541959521969408] ++ List.replicate 24 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross15 (j : Nat) :
    outer41P13Int j * outer41Q15Int j -
      outer41Q13Int j * outer41P15Int j =
      -8 * (243248593617877651 + 168192744940246176 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P13Coeffs)
            (outer41NatCoeffs outer41Q15Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q13Coeffs)
            (outer41NatCoeffs outer41P15Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-1945988748943021208, -1345541959521969408] ++ List.replicate 24 0) := by
          rw [outer41Cross15Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint15Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A14Coeffs
        (outer41NatCoeffs outer41Q15Coeffs))
      (outer41CoeffMul outer41B14Coeffs
        (outer41NatCoeffs outer41P15Coeffs)) =
      [46319273757209672] ++ List.replicate 26 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint15 (j : Nat) :
    outer41A14 j * outer41Q15Int j +
      outer41B14 j * outer41P15Int j = 46319273757209672 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A14Coeffs
            (outer41NatCoeffs outer41Q15Coeffs))
          (outer41CoeffMul outer41B14Coeffs
            (outer41NatCoeffs outer41P15Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([46319273757209672] ++ List.replicate 26 0) := by
          rw [outer41Endpoint15Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross13Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P11Coeffs)
        (outer41NatCoeffs outer41Q13Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q11Coeffs)
        (outer41NatCoeffs outer41P13Coeffs)) =
      [-286827986950837620, -247915765599959296] ++ List.replicate 20 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross13 (j : Nat) :
    outer41P11Int j * outer41Q13Int j -
      outer41Q11Int j * outer41P13Int j =
      -4 * (71706996737709405 + 61978941399989824 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P11Coeffs)
            (outer41NatCoeffs outer41Q13Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q11Coeffs)
            (outer41NatCoeffs outer41P13Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-286827986950837620, -247915765599959296] ++ List.replicate 20 0) := by
          rw [outer41Cross13Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint13Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A12Coeffs
        (outer41NatCoeffs outer41Q13Coeffs))
      (outer41CoeffMul outer41B12Coeffs
        (outer41NatCoeffs outer41P13Coeffs)) =
      [23776391613186304] ++ List.replicate 22 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint13 (j : Nat) :
    outer41A12 j * outer41Q13Int j +
      outer41B12 j * outer41P13Int j = 23776391613186304 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A12Coeffs
            (outer41NatCoeffs outer41Q13Coeffs))
          (outer41CoeffMul outer41B12Coeffs
            (outer41NatCoeffs outer41P13Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([23776391613186304] ++ List.replicate 22 0) := by
          rw [outer41Endpoint13Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross11Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P9Coeffs)
        (outer41NatCoeffs outer41Q11Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q9Coeffs)
        (outer41NatCoeffs outer41P11Coeffs)) =
      [1797328133849916, 1884503953965312] ++ List.replicate 16 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross11 (j : Nat) :
    outer41P9Int j * outer41Q11Int j -
      outer41Q9Int j * outer41P11Int j =
      108 * (16641927165277 + 17449110684864 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P9Coeffs)
            (outer41NatCoeffs outer41Q11Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q9Coeffs)
            (outer41NatCoeffs outer41P11Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([1797328133849916, 1884503953965312] ++ List.replicate 16 0) := by
          rw [outer41Cross11Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint11Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A10Coeffs
        (outer41NatCoeffs outer41Q11Coeffs))
      (outer41CoeffMul outer41B10Coeffs
        (outer41NatCoeffs outer41P11Coeffs)) =
      [21268539938988] ++ List.replicate 18 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint11 (j : Nat) :
    outer41A10 j * outer41Q11Int j +
      outer41B10 j * outer41P11Int j = 21268539938988 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A10Coeffs
            (outer41NatCoeffs outer41Q11Coeffs))
          (outer41CoeffMul outer41B10Coeffs
            (outer41NatCoeffs outer41P11Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([21268539938988] ++ List.replicate 18 0) := by
          rw [outer41Endpoint11Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross9Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P7Coeffs)
        (outer41NatCoeffs outer41Q9Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q7Coeffs)
        (outer41NatCoeffs outer41P9Coeffs)) =
      [-373344219151504, -323763502358592] ++ List.replicate 12 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross9 (j : Nat) :
    outer41P7Int j * outer41Q9Int j -
      outer41Q7Int j * outer41P9Int j =
      -16 * (23334013696969 + 20235218897412 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P7Coeffs)
            (outer41NatCoeffs outer41Q9Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q7Coeffs)
            (outer41NatCoeffs outer41P9Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-373344219151504, -323763502358592] ++ List.replicate 12 0) := by
          rw [outer41Cross9Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint9Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A8Coeffs
        (outer41NatCoeffs outer41Q9Coeffs))
      (outer41CoeffMul outer41B8Coeffs
        (outer41NatCoeffs outer41P9Coeffs)) =
      [40985168665156] ++ List.replicate 14 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint9 (j : Nat) :
    outer41A8 j * outer41Q9Int j +
      outer41B8 j * outer41P9Int j = 40985168665156 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A8Coeffs
            (outer41NatCoeffs outer41Q9Coeffs))
          (outer41CoeffMul outer41B8Coeffs
            (outer41NatCoeffs outer41P9Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([40985168665156] ++ List.replicate 14 0) := by
          rw [outer41Endpoint9Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross7Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P5Coeffs)
        (outer41NatCoeffs outer41Q7Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q5Coeffs)
        (outer41NatCoeffs outer41P7Coeffs)) =
      [-110225569682596, -88573541853440] ++ List.replicate 8 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross7 (j : Nat) :
    outer41P5Int j * outer41Q7Int j -
      outer41Q5Int j * outer41P7Int j =
      -4 * (27556392420649 + 22143385463360 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P5Coeffs)
            (outer41NatCoeffs outer41Q7Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q5Coeffs)
            (outer41NatCoeffs outer41P7Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-110225569682596, -88573541853440] ++ List.replicate 8 0) := by
          rw [outer41Cross7Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint7Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A6Coeffs
        (outer41NatCoeffs outer41Q7Coeffs))
      (outer41CoeffMul outer41B6Coeffs
        (outer41NatCoeffs outer41P7Coeffs)) =
      [25222271863684] ++ List.replicate 10 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint7 (j : Nat) :
    outer41A6 j * outer41Q7Int j +
      outer41B6 j * outer41P7Int j = 25222271863684 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A6Coeffs
            (outer41NatCoeffs outer41Q7Coeffs))
          (outer41CoeffMul outer41B6Coeffs
            (outer41NatCoeffs outer41P7Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([25222271863684] ++ List.replicate 10 0) := by
          rw [outer41Endpoint7Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross5Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P3Coeffs)
        (outer41NatCoeffs outer41Q5Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q3Coeffs)
        (outer41NatCoeffs outer41P5Coeffs)) =
      [-148420792700, -113547214656] ++ List.replicate 4 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross5 (j : Nat) :
    outer41P3Int j * outer41Q5Int j -
      outer41Q3Int j * outer41P5Int j =
      -4 * (37105198175 + 28386803664 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P3Coeffs)
            (outer41NatCoeffs outer41Q5Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q3Coeffs)
            (outer41NatCoeffs outer41P5Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-148420792700, -113547214656] ++ List.replicate 4 0) := by
          rw [outer41Cross5Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint5Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A4Coeffs
        (outer41NatCoeffs outer41Q5Coeffs))
      (outer41CoeffMul outer41B4Coeffs
        (outer41NatCoeffs outer41P5Coeffs)) =
      [204790641444] ++ List.replicate 6 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint5 (j : Nat) :
    outer41A4 j * outer41Q5Int j +
      outer41B4 j * outer41P5Int j = 204790641444 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A4Coeffs
            (outer41NatCoeffs outer41Q5Coeffs))
          (outer41CoeffMul outer41B4Coeffs
            (outer41NatCoeffs outer41P5Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([204790641444] ++ List.replicate 6 0) := by
          rw [outer41Endpoint5Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Cross3Coeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P1Coeffs)
        (outer41NatCoeffs outer41Q3Coeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q1Coeffs)
        (outer41NatCoeffs outer41P3Coeffs)) =
      [-2149551, -1667952] ++ List.replicate 1 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Cross3 (j : Nat) :
    outer41P1Int j * outer41Q3Int j -
      outer41Q1Int j * outer41P3Int j =
      -1 * (2149551 + 1667952 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P1Coeffs)
            (outer41NatCoeffs outer41Q3Coeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q1Coeffs)
            (outer41NatCoeffs outer41P3Coeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-2149551, -1667952] ++ List.replicate 1 0) := by
          rw [outer41Cross3Coeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41Endpoint3Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A2Coeffs
        (outer41NatCoeffs outer41Q3Coeffs))
      (outer41CoeffMul outer41B2Coeffs
        (outer41NatCoeffs outer41P3Coeffs)) =
      [4234032] ++ List.replicate 2 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Endpoint3 (j : Nat) :
    outer41A2 j * outer41Q3Int j +
      outer41B2 j * outer41P3Int j = 4234032 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A2Coeffs
            (outer41NatCoeffs outer41Q3Coeffs))
          (outer41CoeffMul outer41B2Coeffs
            (outer41NatCoeffs outer41P3Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([4234032] ++ List.replicate 2 0) := by
          rw [outer41Endpoint3Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41RootCrossCoeffs :
    outer41CoeffSub
      (outer41CoeffMul (outer41NatCoeffs outer41P37Coeffs)
        (outer41NatCoeffs outer41GammaCoeffs))
      (outer41CoeffMul (outer41NatCoeffs outer41Q37Coeffs)
        (outer41NatCoeffs outer41AlphaCoeffs)) =
      [13600, 11200] ++ List.replicate 72 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41RootCross (j : Nat) :
    outer41P37Int j * outer41GammaInt j -
      outer41Q37Int j * outer41AlphaInt j =
      800 * (17 + 14 * (j : Int)) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffSub
          (outer41CoeffMul (outer41NatCoeffs outer41P37Coeffs)
            (outer41NatCoeffs outer41GammaCoeffs))
          (outer41CoeffMul (outer41NatCoeffs outer41Q37Coeffs)
            (outer41NatCoeffs outer41AlphaCoeffs))) := by
          symm
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([13600, 11200] ++ List.replicate 72 0) := by
          rw [outer41RootCrossCoeffs]
    _ = _ := by
      simp [outer41HornerInt]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41RootEndpointCoeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A38Coeffs
        (outer41NatCoeffs outer41GammaCoeffs))
      (outer41CoeffMul outer41B38Coeffs
        (outer41NatCoeffs outer41AlphaCoeffs)) =
      [5] ++ List.replicate 74 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41RootEndpoint (j : Nat) :
    outer41A38 j * outer41GammaInt j +
      outer41B38 j * outer41AlphaInt j = 5 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A38Coeffs
            (outer41NatCoeffs outer41GammaCoeffs))
          (outer41CoeffMul outer41B38Coeffs
            (outer41NatCoeffs outer41AlphaCoeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([5] ++ List.replicate 74 0) := by
          rw [outer41RootEndpointCoeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41RootDeterminantCoeffs :
    outer41CoeffAdd
      (outer41CoeffMul (outer41NatCoeffs outer41P37Coeffs)
        outer41B38Coeffs)
      (outer41CoeffMul (outer41NatCoeffs outer41Q37Coeffs)
        outer41A38Coeffs) =
      [245] ++ List.replicate 72 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41RootDeterminant (j : Nat) :
    outer41P37Int j * outer41B38 j +
      outer41Q37Int j * outer41A38 j = 245 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul (outer41NatCoeffs outer41P37Coeffs)
            outer41B38Coeffs)
          (outer41CoeffMul (outer41NatCoeffs outer41Q37Coeffs)
            outer41A38Coeffs)) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([245] ++ List.replicate 72 0) := by
          rw [outer41RootDeterminantCoeffs]
    _ = _ := by simp [outer41HornerInt]

private def outer41Bezout37_3_left : List Nat :=
  [1, 1, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 2, 1, 2, 0, 2, 2, 1, 0, 0, 0, 2, 0, 1, 1, 1, 1, 2, 2, 0, 0, 2]

private def outer41Bezout37_3_right : List Nat :=
  [1, 2, 1, 1, 2, 1, 1, 0, 1, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2, 2, 1, 0, 1, 2, 0, 0, 2, 0, 0, 0, 2]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout37_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout37_3_left)
        (outer41ModCoeffs outer41P37Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout37_3_right)
        (outer41ModCoeffs outer41Q37Coeffs)) =
      ([1] ++ List.replicate 68 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon37_3 (j : Nat) :
    ¬(3 ∣ outer41P37 j ∧ 3 ∣ outer41Q37 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P37Coeffs outer41Q37Coeffs
    outer41Bezout37_3_left outer41Bezout37_3_right
    outer41Bezout37_3_coeffs j

private def outer41Bezout37_11_left : List Nat :=
  [7, 5, 9, 10, 6, 10, 9, 2, 1, 10, 5, 0, 7, 5, 6, 6, 4, 3, 8, 0, 5, 1, 9, 7, 8, 2, 7, 0, 6, 2, 2, 6, 3, 10, 2]

private def outer41Bezout37_11_right : List Nat :=
  [2, 2, 0, 7, 1, 1, 8, 10, 7, 0, 1, 7, 4, 5, 8, 1, 4, 5, 8, 2, 4, 0, 7, 0, 0, 7, 7, 0, 7, 2, 6, 6, 7, 3]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout37_11_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout37_11_left)
        (outer41ModCoeffs outer41P37Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout37_11_right)
        (outer41ModCoeffs outer41Q37Coeffs)) =
      ([1] ++ List.replicate 69 0 : List (ZMod 11)) := by
  decide

private theorem outer41NoCommon37_11 (j : Nat) :
    ¬(11 ∣ outer41P37 j ∧ 11 ∣ outer41Q37 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P37Coeffs outer41Q37Coeffs
    outer41Bezout37_11_left outer41Bezout37_11_right
    outer41Bezout37_11_coeffs j

private def outer41Bezout33_3_left : List Nat :=
  [2, 1, 2, 2, 2, 2, 2, 2, 0, 0, 0, 2, 2, 2, 1, 2, 1, 0, 2, 1, 1, 1, 2, 0, 1, 1, 1, 2, 2, 0, 1]

private def outer41Bezout33_3_right : List Nat :=
  [1, 0, 1, 2, 0, 1, 0, 2, 0, 2, 2, 1, 0, 1, 2, 1, 1, 2, 1, 2, 1, 1, 0, 1, 1, 2, 0, 1]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout33_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout33_3_left)
        (outer41ModCoeffs outer41P33Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout33_3_right)
        (outer41ModCoeffs outer41Q33Coeffs)) =
      ([1] ++ List.replicate 61 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon33_3 (j : Nat) :
    ¬(3 ∣ outer41P33 j ∧ 3 ∣ outer41Q33 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P33Coeffs outer41Q33Coeffs
    outer41Bezout33_3_left outer41Bezout33_3_right
    outer41Bezout33_3_coeffs j

private def outer41Bezout33_41801_left : List Nat :=
  [28194, 1392, 30026, 37117, 20956, 5534, 8976, 36790, 8935, 35277, 27700, 6723, 17814, 20822, 9285, 28020, 7727, 10989, 38852, 18924, 1687, 23633, 20692, 29700, 963, 13137, 25366, 38586, 15418, 6620, 4424]

private def outer41Bezout33_41801_right : List Nat :=
  [30158, 37964, 7684, 24654, 17936, 11046, 34928, 30078, 24787, 10582, 4087, 12439, 25515, 36085, 15274, 38489, 24098, 609, 18439, 19151, 16701, 16032, 10638, 14676, 39912, 1151, 33998, 25478, 20588, 36076]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout33_41801_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout33_41801_left)
        (outer41ModCoeffs outer41P33Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout33_41801_right)
        (outer41ModCoeffs outer41Q33Coeffs)) =
      ([1] ++ List.replicate 61 0 : List (ZMod 41801)) := by
  decide

private theorem outer41NoCommon33_41801 (j : Nat) :
    ¬(41801 ∣ outer41P33 j ∧ 41801 ∣ outer41Q33 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P33Coeffs outer41Q33Coeffs
    outer41Bezout33_41801_left outer41Bezout33_41801_right
    outer41Bezout33_41801_coeffs j

private def outer41Bezout31_5_left : List Nat :=
  [0, 3, 4, 4, 2, 1, 0, 4, 3, 4, 2, 1, 0, 1, 1, 0, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4, 0, 4, 2]

private def outer41Bezout31_5_right : List Nat :=
  [1, 3, 4, 4, 3, 0, 3, 2, 4, 4, 0, 1, 3, 0, 3, 1, 1, 3, 3, 4, 2, 4, 1, 0, 4, 3, 4, 3]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout31_5_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout31_5_left)
        (outer41ModCoeffs outer41P31Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout31_5_right)
        (outer41ModCoeffs outer41Q31Coeffs)) =
      ([1] ++ List.replicate 57 0 : List (ZMod 5)) := by
  decide

private theorem outer41NoCommon31_5 (j : Nat) :
    ¬(5 ∣ outer41P31 j ∧ 5 ∣ outer41Q31 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P31Coeffs outer41Q31Coeffs
    outer41Bezout31_5_left outer41Bezout31_5_right
    outer41Bezout31_5_coeffs j

private def outer41Bezout31_19483_left : List Nat :=
  [140, 14138, 4569, 16232, 8577, 16820, 19175, 3949, 3271, 8313, 6549, 2087, 14593, 11339, 18859, 17716, 927, 18461, 2584, 651, 1860, 3720, 4551, 15124, 3545, 8496, 8029, 4474, 12436]

private def outer41Bezout31_19483_right : List Nat :=
  [11602, 14692, 4170, 10365, 16215, 6920, 15113, 9036, 3850, 17496, 10018, 3429, 2330, 12657, 16665, 10027, 14086, 509, 14089, 17556, 6595, 2872, 5995, 13618, 2445, 15428, 4878, 803]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout31_19483_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout31_19483_left)
        (outer41ModCoeffs outer41P31Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout31_19483_right)
        (outer41ModCoeffs outer41Q31Coeffs)) =
      ([1] ++ List.replicate 57 0 : List (ZMod 19483)) := by
  decide

private theorem outer41NoCommon31_19483 (j : Nat) :
    ¬(19483 ∣ outer41P31 j ∧ 19483 ∣ outer41Q31 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P31Coeffs outer41Q31Coeffs
    outer41Bezout31_19483_left outer41Bezout31_19483_right
    outer41Bezout31_19483_coeffs j

private def outer41Bezout29_3_left : List Nat :=
  [0, 0, 2, 1, 2, 0, 2, 0, 0, 0, 2, 0, 2, 2, 0, 2, 1, 1, 2, 0, 0, 1, 1, 0, 1, 1]

private def outer41Bezout29_3_right : List Nat :=
  [1, 1, 0, 2, 2, 2, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 1, 1]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout29_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout29_3_left)
        (outer41ModCoeffs outer41P29Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout29_3_right)
        (outer41ModCoeffs outer41Q29Coeffs)) =
      ([1] ++ List.replicate 52 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon29_3 (j : Nat) :
    ¬(3 ∣ outer41P29 j ∧ 3 ∣ outer41Q29 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P29Coeffs outer41Q29Coeffs
    outer41Bezout29_3_left outer41Bezout29_3_right
    outer41Bezout29_3_coeffs j

private def outer41Bezout29_117517_left : List Nat :=
  [36994, 66221, 104035, 2657, 20998, 81841, 26885, 42903, 113805, 3626, 115659, 89226, 61590, 6186, 51553, 25707, 76402, 4876, 2982, 85021, 49119, 12442, 116584, 71398, 28971, 86636, 5243]

private def outer41Bezout29_117517_right : List Nat :=
  [76355, 92108, 13852, 75630, 79695, 67070, 28214, 105475, 79468, 111058, 53413, 37742, 102691, 2627, 40270, 5405, 77138, 32744, 36013, 73037, 63228, 14060, 103080, 108566, 65181, 50606]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout29_117517_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout29_117517_left)
        (outer41ModCoeffs outer41P29Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout29_117517_right)
        (outer41ModCoeffs outer41Q29Coeffs)) =
      ([1] ++ List.replicate 53 0 : List (ZMod 117517)) := by
  decide

private theorem outer41NoCommon29_117517 (j : Nat) :
    ¬(117517 ∣ outer41P29 j ∧ 117517 ∣ outer41Q29 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P29Coeffs outer41Q29Coeffs
    outer41Bezout29_117517_left outer41Bezout29_117517_right
    outer41Bezout29_117517_coeffs j

private def outer41Bezout27_3_left : List Nat :=
  [1, 2, 1, 2, 2, 2, 1, 0, 1, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0, 1, 2, 1, 1]

private def outer41Bezout27_3_right : List Nat :=
  [0, 1, 0, 2, 2, 2, 0, 2, 1, 0, 1, 0, 1, 2, 2, 2, 0, 2, 1, 1]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout27_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_3_left)
        (outer41ModCoeffs outer41P27Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_3_right)
        (outer41ModCoeffs outer41Q27Coeffs)) =
      ([1] ++ List.replicate 47 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon27_3 (j : Nat) :
    ¬(3 ∣ outer41P27 j ∧ 3 ∣ outer41Q27 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P27Coeffs outer41Q27Coeffs
    outer41Bezout27_3_left outer41Bezout27_3_right
    outer41Bezout27_3_coeffs j

private def outer41Bezout27_7_left : List Nat :=
  [6, 2, 3, 4, 4, 6, 3, 3, 1, 3, 5, 3, 4, 1, 6, 4, 4, 3, 2, 5, 0, 4, 0, 6, 4]

private def outer41Bezout27_7_right : List Nat :=
  [4, 4, 4, 6, 0, 5, 5, 5, 3, 5, 6, 0, 6, 0, 0, 3, 2, 4, 3, 4, 2, 4, 2, 2]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout27_7_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_7_left)
        (outer41ModCoeffs outer41P27Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_7_right)
        (outer41ModCoeffs outer41Q27Coeffs)) =
      ([1] ++ List.replicate 49 0 : List (ZMod 7)) := by
  decide

private theorem outer41NoCommon27_7 (j : Nat) :
    ¬(7 ∣ outer41P27 j ∧ 7 ∣ outer41Q27 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P27Coeffs outer41Q27Coeffs
    outer41Bezout27_7_left outer41Bezout27_7_right
    outer41Bezout27_7_coeffs j

private def outer41Bezout27_47_left : List Nat :=
  [29, 34, 44, 34, 6, 36, 30, 43, 15, 35, 13, 5, 14, 23, 38, 24, 46, 28, 44, 0, 27, 29, 13, 44, 1]

private def outer41Bezout27_47_right : List Nat :=
  [9, 32, 31, 23, 44, 22, 36, 3, 33, 7, 35, 6, 11, 14, 24, 1, 31, 43, 18, 4, 36, 36, 17, 36]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout27_47_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_47_left)
        (outer41ModCoeffs outer41P27Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_47_right)
        (outer41ModCoeffs outer41Q27Coeffs)) =
      ([1] ++ List.replicate 49 0 : List (ZMod 47)) := by
  decide

private theorem outer41NoCommon27_47 (j : Nat) :
    ¬(47 ∣ outer41P27 j ∧ 47 ∣ outer41Q27 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P27Coeffs outer41Q27Coeffs
    outer41Bezout27_47_left outer41Bezout27_47_right
    outer41Bezout27_47_coeffs j

private def outer41Bezout27_9491_left : List Nat :=
  [3668, 9187, 1550, 4652, 433, 4414, 5907, 2784, 7054, 6344, 8820, 3641, 8264, 1889, 5585, 2471, 3476, 285, 453, 5846, 672, 1143, 2818, 6031, 1892]

private def outer41Bezout27_9491_right : List Nat :=
  [9197, 5000, 8669, 7480, 2554, 7213, 4379, 3672, 8695, 8801, 167, 6324, 5778, 9486, 699, 855, 6973, 6968, 2925, 7689, 1921, 3151, 9026, 1387]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout27_9491_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_9491_left)
        (outer41ModCoeffs outer41P27Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout27_9491_right)
        (outer41ModCoeffs outer41Q27Coeffs)) =
      ([1] ++ List.replicate 49 0 : List (ZMod 9491)) := by
  decide

private theorem outer41NoCommon27_9491 (j : Nat) :
    ¬(9491 ∣ outer41P27 j ∧ 9491 ∣ outer41Q27 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P27Coeffs outer41Q27Coeffs
    outer41Bezout27_9491_left outer41Bezout27_9491_right
    outer41Bezout27_9491_coeffs j

private def outer41Bezout25_3_left : List Nat :=
  [2, 2, 2, 2, 0, 1, 1, 0, 1, 2, 0, 1, 2, 0, 0, 1, 1, 2, 1, 2, 2]

private def outer41Bezout25_3_right : List Nat :=
  [2, 1, 1, 2, 2, 1, 2, 0, 0, 1, 1, 1, 2, 2, 0, 1, 2, 2]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout25_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout25_3_left)
        (outer41ModCoeffs outer41P25Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout25_3_right)
        (outer41ModCoeffs outer41Q25Coeffs)) =
      ([1] ++ List.replicate 43 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon25_3 (j : Nat) :
    ¬(3 ∣ outer41P25 j ∧ 3 ∣ outer41Q25 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P25Coeffs outer41Q25Coeffs
    outer41Bezout25_3_left outer41Bezout25_3_right
    outer41Bezout25_3_coeffs j

private def outer41Bezout25_73_left : List Nat :=
  [32, 71, 19, 41, 56, 40, 39, 2, 11, 24, 37, 35, 63, 48, 40, 67, 64, 14, 19, 51, 58, 16, 7]

private def outer41Bezout25_73_right : List Nat :=
  [72, 5, 9, 52, 52, 12, 63, 5, 34, 54, 24, 72, 47, 50, 16, 28, 56, 61, 5, 62, 71, 36]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout25_73_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout25_73_left)
        (outer41ModCoeffs outer41P25Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout25_73_right)
        (outer41ModCoeffs outer41Q25Coeffs)) =
      ([1] ++ List.replicate 45 0 : List (ZMod 73)) := by
  decide

private theorem outer41NoCommon25_73 (j : Nat) :
    ¬(73 ∣ outer41P25 j ∧ 73 ∣ outer41Q25 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P25Coeffs outer41Q25Coeffs
    outer41Bezout25_73_left outer41Bezout25_73_right
    outer41Bezout25_73_coeffs j

private def outer41Bezout25_18889231_left : List Nat :=
  [15604587, 16505752, 16265599, 10600276, 12163692, 15502363, 12694743, 4254331, 14802973, 8075603, 237187, 4635939, 10059906, 11402098, 7317710, 14132662, 8775295, 15267936, 5155478, 3898176, 17125074, 18299188, 18425233]

private def outer41Bezout25_18889231_right : List Nat :=
  [2932798, 12871226, 13092206, 17419072, 14639582, 9064170, 2770947, 15231077, 11867316, 306207, 15146805, 7771602, 14831636, 7195360, 15340240, 5549166, 5114554, 2520024, 11369202, 16980821, 12029083, 14682839]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout25_18889231_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout25_18889231_left)
        (outer41ModCoeffs outer41P25Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout25_18889231_right)
        (outer41ModCoeffs outer41Q25Coeffs)) =
      ([1] ++ List.replicate 45 0 : List (ZMod 18889231)) := by
  decide

private theorem outer41NoCommon25_18889231 (j : Nat) :
    ¬(18889231 ∣ outer41P25 j ∧ 18889231 ∣ outer41Q25 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P25Coeffs outer41Q25Coeffs
    outer41Bezout25_18889231_left outer41Bezout25_18889231_right
    outer41Bezout25_18889231_coeffs j

private def outer41Bezout23_10639_left : List Nat :=
  [5915, 3824, 106, 1429, 3963, 3799, 403, 7278, 1557, 5533, 7223, 4019, 4216, 7627, 10407, 5544, 6161, 176, 2746, 6339, 8585]

private def outer41Bezout23_10639_right : List Nat :=
  [9000, 5817, 1165, 5627, 6761, 6477, 2661, 3374, 9384, 5950, 8004, 5287, 7707, 2113, 5182, 6780, 1468, 1517, 5462, 6845]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout23_10639_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23_10639_left)
        (outer41ModCoeffs outer41P23Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23_10639_right)
        (outer41ModCoeffs outer41Q23Coeffs)) =
      ([1] ++ List.replicate 41 0 : List (ZMod 10639)) := by
  decide

private theorem outer41NoCommon23_10639 (j : Nat) :
    ¬(10639 ∣ outer41P23 j ∧ 10639 ∣ outer41Q23 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P23Coeffs outer41Q23Coeffs
    outer41Bezout23_10639_left outer41Bezout23_10639_right
    outer41Bezout23_10639_coeffs j

private def outer41Bezout23_290737_left : List Nat :=
  [274164, 274629, 28524, 200512, 97348, 215145, 34531, 142071, 249563, 222471, 253363, 265452, 5759, 264149, 54905, 29269, 268142, 23275, 264577, 57085, 280216]

private def outer41Bezout23_290737_right : List Nat :=
  [66839, 31363, 123071, 284622, 259424, 167289, 226661, 230302, 268598, 244189, 116155, 248552, 214123, 244007, 229925, 27165, 73393, 94434, 235346, 65724]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout23_290737_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23_290737_left)
        (outer41ModCoeffs outer41P23Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23_290737_right)
        (outer41ModCoeffs outer41Q23Coeffs)) =
      ([1] ++ List.replicate 41 0 : List (ZMod 290737)) := by
  decide

private theorem outer41NoCommon23_290737 (j : Nat) :
    ¬(290737 ∣ outer41P23 j ∧ 290737 ∣ outer41Q23 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P23Coeffs outer41Q23Coeffs
    outer41Bezout23_290737_left outer41Bezout23_290737_right
    outer41Bezout23_290737_coeffs j

private def outer41Bezout21_229_left : List Nat :=
  [50, 76, 55, 28, 219, 70, 185, 141, 197, 228, 140, 215, 197, 29, 199, 117, 51, 199, 96]

private def outer41Bezout21_229_right : List Nat :=
  [80, 88, 2, 106, 67, 10, 161, 228, 40, 54, 179, 41, 85, 212, 9, 40, 142, 107]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout21_229_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout21_229_left)
        (outer41ModCoeffs outer41P21Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout21_229_right)
        (outer41ModCoeffs outer41Q21Coeffs)) =
      ([1] ++ List.replicate 37 0 : List (ZMod 229)) := by
  decide

private theorem outer41NoCommon21_229 (j : Nat) :
    ¬(229 ∣ outer41P21 j ∧ 229 ∣ outer41Q21 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P21Coeffs outer41Q21Coeffs
    outer41Bezout21_229_left outer41Bezout21_229_right
    outer41Bezout21_229_coeffs j

private def outer41Bezout21_220030169_left : List Nat :=
  [192241403, 198291021, 151011860, 170716078, 93217385, 196730239, 85984315, 64916638, 14362166, 149109034, 124387314, 10311189, 181120359, 31216993, 45998121, 122377488, 158110639, 136342196, 97235826]

private def outer41Bezout21_220030169_right : List Nat :=
  [18092288, 50436393, 19878917, 217506866, 24536668, 209015521, 199625120, 82434126, 18915704, 24558457, 161053406, 132789994, 3226540, 140024517, 37503596, 56433071, 178788675, 153301277]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout21_220030169_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout21_220030169_left)
        (outer41ModCoeffs outer41P21Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout21_220030169_right)
        (outer41ModCoeffs outer41Q21Coeffs)) =
      ([1] ++ List.replicate 37 0 : List (ZMod 220030169)) := by
  decide

private theorem outer41NoCommon21_220030169 (j : Nat) :
    ¬(220030169 ∣ outer41P21 j ∧ 220030169 ∣ outer41Q21 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P21Coeffs outer41Q21Coeffs
    outer41Bezout21_220030169_left outer41Bezout21_220030169_right
    outer41Bezout21_220030169_coeffs j

private def outer41Bezout19_13_left : List Nat :=
  [1, 7, 8, 4, 5, 12, 10, 0, 11, 9, 3, 1, 9, 10, 8, 2, 11]

private def outer41Bezout19_13_right : List Nat :=
  [4, 9, 5, 6, 1, 10, 1, 5, 7, 11, 1, 12, 3, 5, 6]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout19_13_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout19_13_left)
        (outer41ModCoeffs outer41P19Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout19_13_right)
        (outer41ModCoeffs outer41Q19Coeffs)) =
      ([1] ++ List.replicate 33 0 : List (ZMod 13)) := by
  decide

private theorem outer41NoCommon19_13 (j : Nat) :
    ¬(13 ∣ outer41P19 j ∧ 13 ∣ outer41Q19 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P19Coeffs outer41Q19Coeffs
    outer41Bezout19_13_left outer41Bezout19_13_right
    outer41Bezout19_13_coeffs j

private def outer41Bezout19_17519263_left : List Nat :=
  [17368902, 2508605, 12290935, 8608655, 15697185, 3126236, 14594224, 9804749, 7636027, 9068153, 3894213, 10388373, 9373338, 7560996, 11536322, 7691147, 6542800]

private def outer41Bezout19_17519263_right : List Nat :=
  [419677, 16318095, 17015359, 692630, 10635645, 16069572, 8199313, 3459231, 5598, 14122797, 8385811, 12995187, 17058462, 6786923, 10128884, 2356782]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout19_17519263_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout19_17519263_left)
        (outer41ModCoeffs outer41P19Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout19_17519263_right)
        (outer41ModCoeffs outer41Q19Coeffs)) =
      ([1] ++ List.replicate 33 0 : List (ZMod 17519263)) := by
  decide

private theorem outer41NoCommon19_17519263 (j : Nat) :
    ¬(17519263 ∣ outer41P19 j ∧ 17519263 ∣ outer41Q19 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P19Coeffs outer41Q19Coeffs
    outer41Bezout19_17519263_left outer41Bezout19_17519263_right
    outer41Bezout19_17519263_coeffs j

private def outer41Bezout17_2731930457_left : List Nat :=
  [1320760069, 626451539, 2009040674, 1084853842, 2188449508, 1854190260, 1299818473, 300044785, 578541519, 1620136580, 787917905, 2721921938, 196350850, 99296862, 1468593982]

private def outer41Bezout17_2731930457_right : List Nat :=
  [1851114404, 439914709, 1325107373, 111471337, 1864509580, 2682373689, 2570178840, 295136067, 1283015785, 1442685706, 1956926886, 374854810, 1948333750, 606551128]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout17_2731930457_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout17_2731930457_left)
        (outer41ModCoeffs outer41P17Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout17_2731930457_right)
        (outer41ModCoeffs outer41Q17Coeffs)) =
      ([1] ++ List.replicate 29 0 : List (ZMod 2731930457)) := by
  decide

private theorem outer41NoCommon17_2731930457 (j : Nat) :
    ¬(2731930457 ∣ outer41P17 j ∧ 2731930457 ∣ outer41Q17 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P17Coeffs outer41Q17Coeffs
    outer41Bezout17_2731930457_left outer41Bezout17_2731930457_right
    outer41Bezout17_2731930457_coeffs j

private def outer41Bezout15_31_left : List Nat :=
  [6, 29, 22, 27, 22, 8, 29, 2, 26, 3, 17, 23, 15]

private def outer41Bezout15_31_right : List Nat :=
  [28, 1, 19, 10, 26, 16, 16, 21, 18, 18, 1, 12]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout15_31_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout15_31_left)
        (outer41ModCoeffs outer41P15Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout15_31_right)
        (outer41ModCoeffs outer41Q15Coeffs)) =
      ([1] ++ List.replicate 25 0 : List (ZMod 31)) := by
  decide

private theorem outer41NoCommon15_31 (j : Nat) :
    ¬(31 ∣ outer41P15 j ∧ 31 ∣ outer41Q15 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P15Coeffs outer41Q15Coeffs
    outer41Bezout15_31_left outer41Bezout15_31_right
    outer41Bezout15_31_coeffs j

private def outer41Bezout15_211_left : List Nat :=
  [84, 204, 115, 125, 2, 156, 13, 146, 194, 52, 118, 37, 196]

private def outer41Bezout15_211_right : List Nat :=
  [39, 161, 19, 105, 18, 61, 20, 9, 131, 150, 48, 101]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout15_211_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout15_211_left)
        (outer41ModCoeffs outer41P15Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout15_211_right)
        (outer41ModCoeffs outer41Q15Coeffs)) =
      ([1] ++ List.replicate 25 0 : List (ZMod 211)) := by
  decide

private theorem outer41NoCommon15_211 (j : Nat) :
    ¬(211 ∣ outer41P15 j ∧ 211 ∣ outer41Q15 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P15Coeffs outer41Q15Coeffs
    outer41Bezout15_211_left outer41Bezout15_211_right
    outer41Bezout15_211_coeffs j

private def outer41Bezout15_11633_left : List Nat :=
  [5238, 9621, 4487, 7523, 8379, 11091, 11518, 3586, 8796, 5142, 6053, 8986, 6695]

private def outer41Bezout15_11633_right : List Nat :=
  [5879, 1845, 5414, 8208, 6318, 8083, 10644, 7772, 5346, 3115, 5488, 11511]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout15_11633_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout15_11633_left)
        (outer41ModCoeffs outer41P15Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout15_11633_right)
        (outer41ModCoeffs outer41Q15Coeffs)) =
      ([1] ++ List.replicate 25 0 : List (ZMod 11633)) := by
  decide

private theorem outer41NoCommon15_11633 (j : Nat) :
    ¬(11633 ∣ outer41P15 j ∧ 11633 ∣ outer41Q15 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P15Coeffs outer41Q15Coeffs
    outer41Bezout15_11633_left outer41Bezout15_11633_right
    outer41Bezout15_11633_coeffs j

private def outer41Bezout13_1487_left : List Nat :=
  [828, 323, 1477, 541, 1187, 79, 213, 243, 1114, 77, 951]

private def outer41Bezout13_1487_right : List Nat :=
  [682, 917, 525, 887, 1213, 321, 715, 90, 644, 101]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout13_1487_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout13_1487_left)
        (outer41ModCoeffs outer41P13Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout13_1487_right)
        (outer41ModCoeffs outer41Q13Coeffs)) =
      ([1] ++ List.replicate 21 0 : List (ZMod 1487)) := by
  decide

private theorem outer41NoCommon13_1487 (j : Nat) :
    ¬(1487 ∣ outer41P13 j ∧ 1487 ∣ outer41Q13 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P13Coeffs outer41Q13Coeffs
    outer41Bezout13_1487_left outer41Bezout13_1487_right
    outer41Bezout13_1487_coeffs j

private def outer41Bezout13_6481_left : List Nat :=
  [5884, 6302, 1276, 4121, 6106, 2911, 5129, 4090, 56, 3609, 2750]

private def outer41Bezout13_6481_right : List Nat :=
  [5848, 957, 6269, 1112, 3899, 376, 1039, 4446, 754, 882]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout13_6481_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout13_6481_left)
        (outer41ModCoeffs outer41P13Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout13_6481_right)
        (outer41ModCoeffs outer41Q13Coeffs)) =
      ([1] ++ List.replicate 21 0 : List (ZMod 6481)) := by
  decide

private theorem outer41NoCommon13_6481 (j : Nat) :
    ¬(6481 ∣ outer41P13 j ∧ 6481 ∣ outer41Q13 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P13Coeffs outer41Q13Coeffs
    outer41Bezout13_6481_left outer41Bezout13_6481_right
    outer41Bezout13_6481_coeffs j

private def outer41Bezout11_3_left : List Nat :=
  [2, 1, 1, 2, 2, 1, 1]

private def outer41Bezout11_3_right : List Nat :=
  [1, 2, 1, 1]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout11_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout11_3_left)
        (outer41ModCoeffs outer41P11Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout11_3_right)
        (outer41ModCoeffs outer41Q11Coeffs)) =
      ([1] ++ List.replicate 15 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon11_3 (j : Nat) :
    ¬(3 ∣ outer41P11 j ∧ 3 ∣ outer41Q11 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P11Coeffs outer41Q11Coeffs
    outer41Bezout11_3_left outer41Bezout11_3_right
    outer41Bezout11_3_coeffs j

private def outer41Bezout11_53_left : List Nat :=
  [24, 29, 51, 37, 29, 14, 29, 51, 18]

private def outer41Bezout11_53_right : List Nat :=
  [5, 23, 13, 30, 1, 2, 21, 17]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout11_53_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout11_53_left)
        (outer41ModCoeffs outer41P11Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout11_53_right)
        (outer41ModCoeffs outer41Q11Coeffs)) =
      ([1] ++ List.replicate 17 0 : List (ZMod 53)) := by
  decide

private theorem outer41NoCommon11_53 (j : Nat) :
    ¬(53 ∣ outer41P11 j ∧ 53 ∣ outer41Q11 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P11Coeffs outer41Q11Coeffs
    outer41Bezout11_53_left outer41Bezout11_53_right
    outer41Bezout11_53_coeffs j

private def outer41Bezout11_2791_left : List Nat :=
  [979, 2519, 1066, 1994, 1935, 2395, 425, 417, 221]

private def outer41Bezout11_2791_right : List Nat :=
  [2788, 900, 1699, 235, 215, 1332, 1945, 1198]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout11_2791_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout11_2791_left)
        (outer41ModCoeffs outer41P11Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout11_2791_right)
        (outer41ModCoeffs outer41Q11Coeffs)) =
      ([1] ++ List.replicate 17 0 : List (ZMod 2791)) := by
  decide

private theorem outer41NoCommon11_2791 (j : Nat) :
    ¬(2791 ∣ outer41P11 j ∧ 2791 ∣ outer41Q11 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P11Coeffs outer41Q11Coeffs
    outer41Bezout11_2791_left outer41Bezout11_2791_right
    outer41Bezout11_2791_coeffs j

private def outer41Bezout9_3200983_left : List Nat :=
  [3198256, 1196266, 895039, 3127709, 755727, 683030, 2885763]

private def outer41Bezout9_3200983_right : List Nat :=
  [1381116, 752223, 2187590, 2136243, 302036, 1552646]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout9_3200983_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout9_3200983_left)
        (outer41ModCoeffs outer41P9Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout9_3200983_right)
        (outer41ModCoeffs outer41Q9Coeffs)) =
      ([1] ++ List.replicate 13 0 : List (ZMod 3200983)) := by
  decide

private theorem outer41NoCommon9_3200983 (j : Nat) :
    ¬(3200983 ∣ outer41P9 j ∧ 3200983 ∣ outer41Q9 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P9Coeffs outer41Q9Coeffs
    outer41Bezout9_3200983_left outer41Bezout9_3200983_right
    outer41Bezout9_3200983_coeffs j

private def outer41Bezout7_7_left : List Nat :=
  [5, 6, 0, 0, 4]

private def outer41Bezout7_7_right : List Nat :=
  [0, 2, 6, 2]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout7_7_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout7_7_left)
        (outer41ModCoeffs outer41P7Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout7_7_right)
        (outer41ModCoeffs outer41Q7Coeffs)) =
      ([1] ++ List.replicate 9 0 : List (ZMod 7)) := by
  decide

private theorem outer41NoCommon7_7 (j : Nat) :
    ¬(7 ∣ outer41P7 j ∧ 7 ∣ outer41Q7 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P7Coeffs outer41Q7Coeffs
    outer41Bezout7_7_left outer41Bezout7_7_right
    outer41Bezout7_7_coeffs j

private def outer41Bezout7_358727_left : List Nat :=
  [349492, 299460, 129130, 46032, 197568]

private def outer41Bezout7_358727_right : List Nat :=
  [341935, 66281, 236065, 353823]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout7_358727_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout7_358727_left)
        (outer41ModCoeffs outer41P7Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout7_358727_right)
        (outer41ModCoeffs outer41Q7Coeffs)) =
      ([1] ++ List.replicate 9 0 : List (ZMod 358727)) := by
  decide

private theorem outer41NoCommon7_358727 (j : Nat) :
    ¬(358727 ∣ outer41P7 j ∧ 358727 ∣ outer41Q7 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P7Coeffs outer41Q7Coeffs
    outer41Bezout7_358727_left outer41Bezout7_358727_right
    outer41Bezout7_358727_coeffs j

private def outer41Bezout5_3_left : List Nat :=
  [2]

private def outer41Bezout5_3_right : List Nat :=
  [0]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout5_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout5_3_left)
        (outer41ModCoeffs outer41P5Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout5_3_right)
        (outer41ModCoeffs outer41Q5Coeffs)) =
      ([1] ++ List.replicate 4 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon5_3 (j : Nat) :
    ¬(3 ∣ outer41P5 j ∧ 3 ∣ outer41Q5 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P5Coeffs outer41Q5Coeffs
    outer41Bezout5_3_left outer41Bezout5_3_right
    outer41Bezout5_3_coeffs j

private def outer41Bezout5_31_left : List Nat :=
  [20, 12, 13]

private def outer41Bezout5_31_right : List Nat :=
  [28, 29]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout5_31_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout5_31_left)
        (outer41ModCoeffs outer41P5Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout5_31_right)
        (outer41ModCoeffs outer41Q5Coeffs)) =
      ([1] ++ List.replicate 5 0 : List (ZMod 31)) := by
  decide

private theorem outer41NoCommon5_31 (j : Nat) :
    ¬(31 ∣ outer41P5 j ∧ 31 ∣ outer41Q5 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P5Coeffs outer41Q5Coeffs
    outer41Bezout5_31_left outer41Bezout5_31_right
    outer41Bezout5_31_coeffs j

private def outer41Bezout5_811_left : List Nat :=
  [43, 223, 650]

private def outer41Bezout5_811_right : List Nat :=
  [650, 614]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout5_811_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout5_811_left)
        (outer41ModCoeffs outer41P5Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout5_811_right)
        (outer41ModCoeffs outer41Q5Coeffs)) =
      ([1] ++ List.replicate 5 0 : List (ZMod 811)) := by
  decide

private theorem outer41NoCommon5_811 (j : Nat) :
    ¬(811 ∣ outer41P5 j ∧ 811 ∣ outer41Q5 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P5Coeffs outer41Q5Coeffs
    outer41Bezout5_811_left outer41Bezout5_811_right
    outer41Bezout5_811_coeffs j

private def outer41Bezout3_3_left : List Nat :=
  [0]

private def outer41Bezout3_3_right : List Nat :=
  [1]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout3_3_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout3_3_left)
        (outer41ModCoeffs outer41P3Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout3_3_right)
        (outer41ModCoeffs outer41Q3Coeffs)) =
      ([1] ++ List.replicate 2 0 : List (ZMod 3)) := by
  decide

private theorem outer41NoCommon3_3 (j : Nat) :
    ¬(3 ∣ outer41P3 j ∧ 3 ∣ outer41Q3 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P3Coeffs outer41Q3Coeffs
    outer41Bezout3_3_left outer41Bezout3_3_right
    outer41Bezout3_3_coeffs j

private def outer41Bezout3_11_left : List Nat :=
  [7]

private def outer41Bezout3_11_right : List Nat :=
  [0]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout3_11_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout3_11_left)
        (outer41ModCoeffs outer41P3Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout3_11_right)
        (outer41ModCoeffs outer41Q3Coeffs)) =
      ([1] ++ List.replicate 2 0 : List (ZMod 11)) := by
  decide

private theorem outer41NoCommon3_11 (j : Nat) :
    ¬(11 ∣ outer41P3 j ∧ 11 ∣ outer41Q3 j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P3Coeffs outer41Q3Coeffs
    outer41Bezout3_11_left outer41Bezout3_11_right
    outer41Bezout3_11_coeffs j

private def outer41Bezout23_13_left : List Nat :=
  [4, 11, 9, 7, 11, 12, 1, 3, 11, 1, 2, 4, 11, 2, 11, 5, 1, 12, 2, 12, 10]

private def outer41Bezout23_13_right : List Nat :=
  [6, 1, 10, 3, 9, 5, 0, 2, 1, 12, 6, 6, 10, 4, 6, 2, 11, 0, 9]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout23_13_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23_13_left)
        (outer41ModCoeffs outer41P23Coeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23_13_right)
        (outer41ModCoeffs outer41Q23Coeffs)) =
      ([1, 1] ++ List.replicate 40 0 : List (ZMod 13)) := by
  decide

private def outer41P23QuotientCoeffs : List Nat :=
  [400931119917863589749283510266749220312429077982894081335083, 8256605504319066738961020606470123793069280442479186097654240, 80968263850832878235999388486950934346575304508324407247637504, 502876435097523038753784077876285703219743953084088280468938752, 2219160581969002125129989158829459390714739978634000605042638848, 7399176662552857287213736742898023765503550619378070311962411008, 19349453255780029146292777375098388759184723056449251720954904576, 40661117004932966984277903771521309181465654706243131973876842496, 69780738373043070255661469013253575914064180419364724607767543808, 98845164622292198607840810674696501622388715354160791596006637568, 116320569390921290191645880815853060849919844158787383990671114240, 114071507850369101054684391656004703515793283477341651212913606656, 93221785673811563142633414958655266077076512848584640492566740992, 63290550702707286492682480702180553442141794439921050174548344832, 35466958273781282798445989120982489375677891020567633693511778304, 16231350697509205817927249949649782825105239880876185687418732544, 5969125136281408271934211942815621809023325403351376110576205824, 1721699443087118394946483414436756338225181081874554640324886528, 375207244975269014442763239550585504187219333171571454600282112, 58098654912072400923093430182456185752152214986933230473576448, 5697628175014628250891275700218133068330712338383498125508608, 266074744031170274240132683040793094153761339485474669985792]

private def outer41Q23QuotientCoeffs : List Nat :=
  [1462365376964904464319534229629678772200155200158442295187787, 31540849038652770758678020739154394794011807261399765253751232, 324682003074677624366817433706096052201972986272359184313479168, 2122087221006046278620387891405975233997146287028454549553176576, 9882204729209454411612886942702932850710161102333220358006439936, 34878202062785756969343873447994446642992267838682165016284626944, 96883592979046433284462128777326920137761851821965421527840063488, 217105781826505309848567953627140925887896611393445759354421641216, 399091617531681524635074809381442621509549723782073742806625550336, 608637645310382163953698908967193664599878764621696561839893118976, 775717475435190074243477586614759685696802987279532492892336553984, 829648786594288408409876958222053812211247300652085023182168260608, 745604638468430490772938281356414600384785591255219888335219589120, 562301007922450953109403969662376700500933883750110331683225993216, 354395078537166255817689293630628075061476535101549839614356750336, 185306856936029446976083242302517261246570451767846170549217656832, 79483203019787966868893215263339997438074480567122685397674491904, 27503263821605456042783659310944204141154029398973107776331448320, 7490124086017931282621296238081800934998188144255110853685149696, 1545978372918172099255108149277695799954900421183869350540476416, 227354428000362586293609288216945100831265258543443858455265280, 21228709506103023365469775411831450880253895891078375744208896, 946043534333049863964916206367264334768929207059465493282816]

private def outer41P23Quotient (j : Nat) :=
  outer41HornerNat j outer41P23QuotientCoeffs

private def outer41Q23Quotient (j : Nat) :=
  outer41HornerNat j outer41Q23QuotientCoeffs

private def outer41Bezout23Quotient_13_left : List Nat :=
  [2]

private def outer41Bezout23Quotient_13_right : List Nat :=
  [0]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout23Quotient_13_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23Quotient_13_left)
        (outer41ModCoeffs outer41P23QuotientCoeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23Quotient_13_right)
        (outer41ModCoeffs outer41Q23QuotientCoeffs)) =
      ([1] ++ List.replicate 22 0 : List (ZMod 13)) := by
  decide

private theorem outer41NoCommon23Quotient_13 (j : Nat) :
    ¬(13 ∣ outer41P23Quotient j ∧
      13 ∣ outer41Q23Quotient j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P23QuotientCoeffs outer41Q23QuotientCoeffs
    outer41Bezout23Quotient_13_left outer41Bezout23Quotient_13_right
    outer41Bezout23Quotient_13_coeffs j

private def outer41Bezout23Quotient_10639_left : List Nat :=
  [2206, 4727, 4383, 8004, 5139, 10150, 3236, 4698, 3845, 3186, 2055, 3410, 4746, 6411, 2410, 2057, 37, 8085, 6523, 9742, 4421]

private def outer41Bezout23Quotient_10639_right : List Nat :=
  [2834, 10289, 10105, 5285, 6923, 10629, 6075, 8740, 2074, 3906, 5500, 3930, 9221, 810, 7407, 5194, 4098, 5433, 5712, 10393]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout23Quotient_10639_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23Quotient_10639_left)
        (outer41ModCoeffs outer41P23QuotientCoeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23Quotient_10639_right)
        (outer41ModCoeffs outer41Q23QuotientCoeffs)) =
      ([1] ++ List.replicate 41 0 : List (ZMod 10639)) := by
  decide

private theorem outer41NoCommon23Quotient_10639 (j : Nat) :
    ¬(10639 ∣ outer41P23Quotient j ∧
      10639 ∣ outer41Q23Quotient j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P23QuotientCoeffs outer41Q23QuotientCoeffs
    outer41Bezout23Quotient_10639_left outer41Bezout23Quotient_10639_right
    outer41Bezout23Quotient_10639_coeffs j

private def outer41Bezout23Quotient_290737_left : List Nat :=
  [84974, 27023, 45321, 56643, 256006, 114083, 139851, 180855, 270933, 178045, 69626, 75726, 259206, 191701, 226645, 191261, 131951, 57483, 98137, 138676, 278077]

private def outer41Bezout23Quotient_290737_right : List Nat :=
  [162538, 34762, 104369, 165841, 14240, 250966, 3618, 266722, 152526, 197340, 244943, 121053, 73830, 66514, 287282, 55473, 32, 187645, 85436, 112587]

set_option maxHeartbeats 2000000 in
private theorem outer41Bezout23Quotient_290737_coeffs :
    outer41ModCoeffAdd
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23Quotient_290737_left)
        (outer41ModCoeffs outer41P23QuotientCoeffs))
      (outer41ModCoeffMul (outer41ModCoeffs outer41Bezout23Quotient_290737_right)
        (outer41ModCoeffs outer41Q23QuotientCoeffs)) =
      ([1] ++ List.replicate 41 0 : List (ZMod 290737)) := by
  decide

private theorem outer41NoCommon23Quotient_290737 (j : Nat) :
    ¬(290737 ∣ outer41P23Quotient j ∧
      290737 ∣ outer41Q23Quotient j) :=
  outer41NoCommonPrime_of_bezout (by norm_num)
    outer41P23QuotientCoeffs outer41Q23QuotientCoeffs
    outer41Bezout23Quotient_290737_left outer41Bezout23Quotient_290737_right
    outer41Bezout23Quotient_290737_coeffs j

private def outer41CoeffAffine (scale shift : Int) : List Int → List Int
  | [] => []
  | a :: rest =>
      outer41CoeffAdd [a]
        (outer41CoeffMul [shift, scale]
          (outer41CoeffAffine scale shift rest))

private theorem outer41HornerInt_affine
    (scale shift j : Int) (coefficients : List Int) :
    outer41HornerInt j (outer41CoeffAffine scale shift coefficients) =
      outer41HornerInt (scale * j + shift) coefficients := by
  induction coefficients with
  | nil => simp [outer41CoeffAffine, outer41HornerInt]
  | cons a coefficients ih =>
      simp only [outer41CoeffAffine, outer41HornerInt_add,
        outer41HornerInt_mul, outer41HornerInt, ih]
      ring

set_option maxHeartbeats 2000000 in
private theorem outer41P23QuotientCoeffs_exact :
    outer41CoeffAffine 13 12 (outer41NatCoeffs outer41P23Coeffs) =
      outer41CoeffScale 13 (outer41NatCoeffs outer41P23QuotientCoeffs) := by
  decide

set_option maxHeartbeats 2000000 in
private theorem outer41Q23QuotientCoeffs_exact :
    outer41CoeffAffine 13 12 (outer41NatCoeffs outer41Q23Coeffs) =
      outer41CoeffScale 13 (outer41NatCoeffs outer41Q23QuotientCoeffs) := by
  decide

private def outer41P23QuotientInt (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41P23QuotientCoeffs)

private def outer41Q23QuotientInt (j : Nat) :=
  outer41HornerInt j (outer41NatCoeffs outer41Q23QuotientCoeffs)

private theorem outer41P23Quotient_exact (j : Nat) :
    outer41HornerInt (13 * j + 12)
      (outer41NatCoeffs outer41P23Coeffs) =
      13 * outer41HornerInt j
        (outer41NatCoeffs outer41P23QuotientCoeffs) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAffine 13 12
          (outer41NatCoeffs outer41P23Coeffs)) := by
          rw [outer41HornerInt_affine]
    _ = outer41HornerInt j
        (outer41CoeffScale 13
          (outer41NatCoeffs outer41P23QuotientCoeffs)) := by
          rw [outer41P23QuotientCoeffs_exact]
    _ = _ := by rw [outer41HornerInt_scale]

private theorem outer41Q23Quotient_exact (j : Nat) :
    outer41HornerInt (13 * j + 12)
      (outer41NatCoeffs outer41Q23Coeffs) =
      13 * outer41HornerInt j
        (outer41NatCoeffs outer41Q23QuotientCoeffs) := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAffine 13 12
          (outer41NatCoeffs outer41Q23Coeffs)) := by
          rw [outer41HornerInt_affine]
    _ = outer41HornerInt j
        (outer41CoeffScale 13
          (outer41NatCoeffs outer41Q23QuotientCoeffs)) := by
          rw [outer41Q23QuotientCoeffs_exact]
    _ = _ := by rw [outer41HornerInt_scale]

private theorem outer41HornerNat_scale_eq_of_int
    (leftJ rightJ scale : Nat) (left right : List Nat)
    (h : outer41HornerInt leftJ (outer41NatCoeffs left) =
      scale * outer41HornerInt rightJ (outer41NatCoeffs right)) :
    outer41HornerNat leftJ left =
      scale * outer41HornerNat rightJ right := by
  apply Int.ofNat_injective
  calc
    (outer41HornerNat leftJ left : Int) =
        outer41HornerInt leftJ (outer41NatCoeffs left) :=
      outer41HornerNat_cast leftJ left
    _ = scale * outer41HornerInt rightJ (outer41NatCoeffs right) := h
    _ = (scale * outer41HornerNat rightJ right : Nat) := by
      rw [Nat.cast_mul, outer41HornerNat_cast]

private theorem outer41P23QuotientNat_exact (j : Nat) :
    outer41HornerNat (13 * j + 12) outer41P23Coeffs =
      13 * outer41HornerNat j outer41P23QuotientCoeffs := by
  apply outer41HornerNat_scale_eq_of_int
    (leftJ := 13 * j + 12) (rightJ := j) (scale := 13)
    (left := outer41P23Coeffs) (right := outer41P23QuotientCoeffs)
  exact outer41P23Quotient_exact j

private theorem outer41Q23QuotientNat_exact (j : Nat) :
    outer41HornerNat (13 * j + 12) outer41Q23Coeffs =
      13 * outer41HornerNat j outer41Q23QuotientCoeffs := by
  apply outer41HornerNat_scale_eq_of_int
    (leftJ := 13 * j + 12) (rightJ := j) (scale := 13)
    (left := outer41Q23Coeffs) (right := outer41Q23QuotientCoeffs)
  exact outer41Q23Quotient_exact j

set_option maxHeartbeats 2000000 in
private theorem outer41P23_at_twelve_mod_thirteen :
    outer41ModHorner (12 : ZMod 13)
      (outer41ModCoeffs outer41P23Coeffs) = 0 := by
  decide

set_option maxHeartbeats 2000000 in
private theorem outer41Q23_at_twelve_mod_thirteen :
    outer41ModHorner (12 : ZMod 13)
      (outer41ModCoeffs outer41Q23Coeffs) = 0 := by
  decide

set_option maxHeartbeats 2000000 in
private theorem outer41Common23_thirteen_iff (j : Nat) :
    (13 ∣ outer41P23 j ∧ 13 ∣ outer41Q23 j) ↔ j % 13 = 12 := by
  constructor
  · rintro ⟨hP, hQ⟩
    change 13 ∣ outer41HornerNat j outer41P23Coeffs at hP
    change 13 ∣ outer41HornerNat j outer41Q23Coeffs at hQ
    have heval := congrArg (outer41ModHorner (j : ZMod 13))
      outer41Bezout23_13_coeffs
    rw [outer41ModHorner_add, outer41ModHorner_mul,
      outer41ModHorner_mul] at heval
    rw [← outer41ModHorner_natCast (n := 13) j outer41P23Coeffs,
      ← outer41ModHorner_natCast (n := 13) j outer41Q23Coeffs] at heval
    have hPzero' : (outer41HornerNat j outer41P23Coeffs : ZMod 13) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hP
    have hQzero' : (outer41HornerNat j outer41Q23Coeffs : ZMod 13) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hQ
    simp only [hPzero', hQzero', mul_zero, zero_add] at heval
    have hcast : ((j + 1 : Nat) : ZMod 13) = 0 := by
      simpa [outer41ModHorner, outer41ModHorner_replicate_zero,
        add_comm] using heval.symm
    have hdvd : 13 ∣ j + 1 :=
      (ZMod.natCast_eq_zero_iff _ _).mp hcast
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    omega
  · intro hj
    have hjcast : (j : ZMod 13) = (12 : Nat) := by
      rw [ZMod.natCast_eq_natCast_iff]
      simpa [Nat.ModEq] using hj
    constructor
    · apply (ZMod.natCast_eq_zero_iff _ _).mp
      change (outer41HornerNat j outer41P23Coeffs : ZMod 13) = 0
      rw [outer41ModHorner_natCast, hjcast]
      exact outer41P23_at_twelve_mod_thirteen
    · apply (ZMod.natCast_eq_zero_iff _ _).mp
      change (outer41HornerNat j outer41Q23Coeffs : ZMod 13) = 0
      rw [outer41ModHorner_natCast, hjcast]
      exact outer41Q23_at_twelve_mod_thirteen

set_option maxHeartbeats 2000000 in
private theorem outer41P23Quotient_reconstruct
    (j : Nat) (hj : j % 13 = 12) :
    outer41P23 j = 13 * outer41P23Quotient (j / 13) := by
  change outer41HornerNat j outer41P23Coeffs =
    13 * outer41HornerNat (j / 13) outer41P23QuotientCoeffs
  have hjEq : j = 13 * (j / 13) + 12 := by omega
  calc
    _ = outer41HornerNat (13 * (j / 13) + 12) outer41P23Coeffs :=
      congrArg (fun x => outer41HornerNat x outer41P23Coeffs) hjEq
    _ = _ := outer41P23QuotientNat_exact (j / 13)

set_option maxHeartbeats 2000000 in
private theorem outer41Q23Quotient_reconstruct
    (j : Nat) (hj : j % 13 = 12) :
    outer41Q23 j = 13 * outer41Q23Quotient (j / 13) := by
  change outer41HornerNat j outer41Q23Coeffs =
    13 * outer41HornerNat (j / 13) outer41Q23QuotientCoeffs
  have hjEq : j = 13 * (j / 13) + 12 := by omega
  calc
    _ = outer41HornerNat (13 * (j / 13) + 12) outer41Q23Coeffs :=
      congrArg (fun x => outer41HornerNat x outer41Q23Coeffs) hjEq
    _ = _ := outer41Q23QuotientNat_exact (j / 13)

private theorem outer41HornerNat_odd_of_mod_two
    (j : Nat) (coefficients : List Nat) (count : Nat)
    (hcoeff : outer41ModCoeffs coefficients =
      ([1] ++ List.replicate count 0 : List (ZMod 2))) :
    Odd (outer41HornerNat j coefficients) := by
  have heval := congrArg (outer41ModHorner (j : ZMod 2)) hcoeff
  rw [← outer41ModHorner_natCast] at heval
  have hone : (outer41HornerNat j coefficients : ZMod 2) = 1 := by
    simpa [outer41ModHorner, outer41ModHorner_replicate_zero] using heval
  exact ZMod.natCast_eq_one_iff_odd.mp hone

private theorem outer41HornerNat_pos_of_head
    (j : Nat) (coefficients : List Nat)
    (hhead : 0 < coefficients.headD 0) :
    0 < outer41HornerNat j coefficients := by
  cases coefficients with
  | nil => simp at hhead
  | cons a coefficients =>
      simp only [List.headD_cons] at hhead
      simp only [outer41HornerNat]
      omega

private theorem outer41Gcd_coprime_prime
    {P Q p : Nat} (hp : p.Prime)
    (hNoCommon : ¬(p ∣ P ∧ p ∣ Q)) :
    (P.gcd Q).Coprime p := by
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hpd
  exact hNoCommon ⟨
    hpd.trans (Nat.gcd_dvd_left P Q),
    hpd.trans (Nat.gcd_dvd_right P Q)⟩

private theorem outer41Coprime_of_support
    {P Q S : Nat} {A B : Int}
    (hendpoint : A * Q + B * P = S)
    (hSupport : (P.gcd Q).Coprime S) :
    P.Coprime Q := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.eq_one_of_dvd_coprimes hSupport dvd_rfl
  have hdPInt : ((P.gcd Q : Nat) : Int) ∣ (P : Int) := by
    exact_mod_cast Nat.gcd_dvd_left P Q
  have hdQInt : ((P.gcd Q : Nat) : Int) ∣ (Q : Int) := by
    exact_mod_cast Nat.gcd_dvd_right P Q
  have hdEndpoint : ((P.gcd Q : Nat) : Int) ∣ A * Q + B * P :=
    dvd_add (dvd_mul_of_dvd_right hdQInt A)
      (dvd_mul_of_dvd_right hdPInt B)
  have hdSInt : ((P.gcd Q : Nat) : Int) ∣ (S : Int) := by
    rw [← hendpoint]
    exact hdEndpoint
  exact_mod_cast hdSInt

set_option maxHeartbeats 1000000 in
private theorem outer41P37ModTwoCoeffs :
    outer41ModCoeffs outer41P37Coeffs =
      ([1] ++ List.replicate 35 0 : List (ZMod 2)) := by
  decide

private theorem outer41P37Odd (j : Nat) : Odd (outer41P37 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P37Coeffs 35
  exact outer41P37ModTwoCoeffs

private theorem outer41P37Pos (j : Nat) : 0 < outer41P37 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P37Coeffs]

private theorem outer41P37Cast (j : Nat) :
    (outer41P37 j : Int) = outer41P37Int j := by
  exact outer41HornerNat_cast j outer41P37Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q37ModTwoCoeffs :
    outer41ModCoeffs outer41Q37Coeffs =
      ([1] ++ List.replicate 36 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q37Odd (j : Nat) : Odd (outer41Q37 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q37Coeffs 36
  exact outer41Q37ModTwoCoeffs

private theorem outer41Q37Pos (j : Nat) : 0 < outer41Q37 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q37Coeffs]

private theorem outer41Q37Cast (j : Nat) :
    (outer41Q37 j : Int) = outer41Q37Int j := by
  exact outer41HornerNat_cast j outer41Q37Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P35ModTwoCoeffs :
    outer41ModCoeffs outer41P35Coeffs =
      ([1] ++ List.replicate 33 0 : List (ZMod 2)) := by
  decide

private theorem outer41P35Odd (j : Nat) : Odd (outer41P35 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P35Coeffs 33
  exact outer41P35ModTwoCoeffs

private theorem outer41P35Pos (j : Nat) : 0 < outer41P35 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P35Coeffs]

private theorem outer41P35Cast (j : Nat) :
    (outer41P35 j : Int) = outer41P35Int j := by
  exact outer41HornerNat_cast j outer41P35Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q35ModTwoCoeffs :
    outer41ModCoeffs outer41Q35Coeffs =
      ([1] ++ List.replicate 34 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q35Odd (j : Nat) : Odd (outer41Q35 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q35Coeffs 34
  exact outer41Q35ModTwoCoeffs

private theorem outer41Q35Pos (j : Nat) : 0 < outer41Q35 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q35Coeffs]

private theorem outer41Q35Cast (j : Nat) :
    (outer41Q35 j : Int) = outer41Q35Int j := by
  exact outer41HornerNat_cast j outer41Q35Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P33ModTwoCoeffs :
    outer41ModCoeffs outer41P33Coeffs =
      ([1] ++ List.replicate 31 0 : List (ZMod 2)) := by
  decide

private theorem outer41P33Odd (j : Nat) : Odd (outer41P33 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P33Coeffs 31
  exact outer41P33ModTwoCoeffs

private theorem outer41P33Pos (j : Nat) : 0 < outer41P33 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P33Coeffs]

private theorem outer41P33Cast (j : Nat) :
    (outer41P33 j : Int) = outer41P33Int j := by
  exact outer41HornerNat_cast j outer41P33Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q33ModTwoCoeffs :
    outer41ModCoeffs outer41Q33Coeffs =
      ([1] ++ List.replicate 32 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q33Odd (j : Nat) : Odd (outer41Q33 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q33Coeffs 32
  exact outer41Q33ModTwoCoeffs

private theorem outer41Q33Pos (j : Nat) : 0 < outer41Q33 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q33Coeffs]

private theorem outer41Q33Cast (j : Nat) :
    (outer41Q33 j : Int) = outer41Q33Int j := by
  exact outer41HornerNat_cast j outer41Q33Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P31ModTwoCoeffs :
    outer41ModCoeffs outer41P31Coeffs =
      ([1] ++ List.replicate 29 0 : List (ZMod 2)) := by
  decide

private theorem outer41P31Odd (j : Nat) : Odd (outer41P31 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P31Coeffs 29
  exact outer41P31ModTwoCoeffs

private theorem outer41P31Pos (j : Nat) : 0 < outer41P31 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P31Coeffs]

private theorem outer41P31Cast (j : Nat) :
    (outer41P31 j : Int) = outer41P31Int j := by
  exact outer41HornerNat_cast j outer41P31Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q31ModTwoCoeffs :
    outer41ModCoeffs outer41Q31Coeffs =
      ([1] ++ List.replicate 30 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q31Odd (j : Nat) : Odd (outer41Q31 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q31Coeffs 30
  exact outer41Q31ModTwoCoeffs

private theorem outer41Q31Pos (j : Nat) : 0 < outer41Q31 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q31Coeffs]

private theorem outer41Q31Cast (j : Nat) :
    (outer41Q31 j : Int) = outer41Q31Int j := by
  exact outer41HornerNat_cast j outer41Q31Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P29ModTwoCoeffs :
    outer41ModCoeffs outer41P29Coeffs =
      ([1] ++ List.replicate 27 0 : List (ZMod 2)) := by
  decide

private theorem outer41P29Odd (j : Nat) : Odd (outer41P29 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P29Coeffs 27
  exact outer41P29ModTwoCoeffs

private theorem outer41P29Pos (j : Nat) : 0 < outer41P29 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P29Coeffs]

private theorem outer41P29Cast (j : Nat) :
    (outer41P29 j : Int) = outer41P29Int j := by
  exact outer41HornerNat_cast j outer41P29Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q29ModTwoCoeffs :
    outer41ModCoeffs outer41Q29Coeffs =
      ([1] ++ List.replicate 28 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q29Odd (j : Nat) : Odd (outer41Q29 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q29Coeffs 28
  exact outer41Q29ModTwoCoeffs

private theorem outer41Q29Pos (j : Nat) : 0 < outer41Q29 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q29Coeffs]

private theorem outer41Q29Cast (j : Nat) :
    (outer41Q29 j : Int) = outer41Q29Int j := by
  exact outer41HornerNat_cast j outer41Q29Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P27ModTwoCoeffs :
    outer41ModCoeffs outer41P27Coeffs =
      ([1] ++ List.replicate 25 0 : List (ZMod 2)) := by
  decide

private theorem outer41P27Odd (j : Nat) : Odd (outer41P27 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P27Coeffs 25
  exact outer41P27ModTwoCoeffs

private theorem outer41P27Pos (j : Nat) : 0 < outer41P27 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P27Coeffs]

private theorem outer41P27Cast (j : Nat) :
    (outer41P27 j : Int) = outer41P27Int j := by
  exact outer41HornerNat_cast j outer41P27Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q27ModTwoCoeffs :
    outer41ModCoeffs outer41Q27Coeffs =
      ([1] ++ List.replicate 26 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q27Odd (j : Nat) : Odd (outer41Q27 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q27Coeffs 26
  exact outer41Q27ModTwoCoeffs

private theorem outer41Q27Pos (j : Nat) : 0 < outer41Q27 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q27Coeffs]

private theorem outer41Q27Cast (j : Nat) :
    (outer41Q27 j : Int) = outer41Q27Int j := by
  exact outer41HornerNat_cast j outer41Q27Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P25ModTwoCoeffs :
    outer41ModCoeffs outer41P25Coeffs =
      ([1] ++ List.replicate 23 0 : List (ZMod 2)) := by
  decide

private theorem outer41P25Odd (j : Nat) : Odd (outer41P25 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P25Coeffs 23
  exact outer41P25ModTwoCoeffs

private theorem outer41P25Pos (j : Nat) : 0 < outer41P25 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P25Coeffs]

private theorem outer41P25Cast (j : Nat) :
    (outer41P25 j : Int) = outer41P25Int j := by
  exact outer41HornerNat_cast j outer41P25Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q25ModTwoCoeffs :
    outer41ModCoeffs outer41Q25Coeffs =
      ([1] ++ List.replicate 24 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q25Odd (j : Nat) : Odd (outer41Q25 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q25Coeffs 24
  exact outer41Q25ModTwoCoeffs

private theorem outer41Q25Pos (j : Nat) : 0 < outer41Q25 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q25Coeffs]

private theorem outer41Q25Cast (j : Nat) :
    (outer41Q25 j : Int) = outer41Q25Int j := by
  exact outer41HornerNat_cast j outer41Q25Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P23ModTwoCoeffs :
    outer41ModCoeffs outer41P23Coeffs =
      ([1] ++ List.replicate 21 0 : List (ZMod 2)) := by
  decide

private theorem outer41P23Odd (j : Nat) : Odd (outer41P23 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P23Coeffs 21
  exact outer41P23ModTwoCoeffs

private theorem outer41P23Pos (j : Nat) : 0 < outer41P23 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P23Coeffs]

private theorem outer41P23Cast (j : Nat) :
    (outer41P23 j : Int) = outer41P23Int j := by
  exact outer41HornerNat_cast j outer41P23Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q23ModTwoCoeffs :
    outer41ModCoeffs outer41Q23Coeffs =
      ([1] ++ List.replicate 22 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q23Odd (j : Nat) : Odd (outer41Q23 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q23Coeffs 22
  exact outer41Q23ModTwoCoeffs

private theorem outer41Q23Pos (j : Nat) : 0 < outer41Q23 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q23Coeffs]

private theorem outer41Q23Cast (j : Nat) :
    (outer41Q23 j : Int) = outer41Q23Int j := by
  exact outer41HornerNat_cast j outer41Q23Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P21ModTwoCoeffs :
    outer41ModCoeffs outer41P21Coeffs =
      ([1] ++ List.replicate 19 0 : List (ZMod 2)) := by
  decide

private theorem outer41P21Odd (j : Nat) : Odd (outer41P21 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P21Coeffs 19
  exact outer41P21ModTwoCoeffs

private theorem outer41P21Pos (j : Nat) : 0 < outer41P21 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P21Coeffs]

private theorem outer41P21Cast (j : Nat) :
    (outer41P21 j : Int) = outer41P21Int j := by
  exact outer41HornerNat_cast j outer41P21Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q21ModTwoCoeffs :
    outer41ModCoeffs outer41Q21Coeffs =
      ([1] ++ List.replicate 20 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q21Odd (j : Nat) : Odd (outer41Q21 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q21Coeffs 20
  exact outer41Q21ModTwoCoeffs

private theorem outer41Q21Pos (j : Nat) : 0 < outer41Q21 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q21Coeffs]

private theorem outer41Q21Cast (j : Nat) :
    (outer41Q21 j : Int) = outer41Q21Int j := by
  exact outer41HornerNat_cast j outer41Q21Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P19ModTwoCoeffs :
    outer41ModCoeffs outer41P19Coeffs =
      ([1] ++ List.replicate 17 0 : List (ZMod 2)) := by
  decide

private theorem outer41P19Odd (j : Nat) : Odd (outer41P19 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P19Coeffs 17
  exact outer41P19ModTwoCoeffs

private theorem outer41P19Pos (j : Nat) : 0 < outer41P19 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P19Coeffs]

private theorem outer41P19Cast (j : Nat) :
    (outer41P19 j : Int) = outer41P19Int j := by
  exact outer41HornerNat_cast j outer41P19Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q19ModTwoCoeffs :
    outer41ModCoeffs outer41Q19Coeffs =
      ([1] ++ List.replicate 18 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q19Odd (j : Nat) : Odd (outer41Q19 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q19Coeffs 18
  exact outer41Q19ModTwoCoeffs

private theorem outer41Q19Pos (j : Nat) : 0 < outer41Q19 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q19Coeffs]

private theorem outer41Q19Cast (j : Nat) :
    (outer41Q19 j : Int) = outer41Q19Int j := by
  exact outer41HornerNat_cast j outer41Q19Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P17ModTwoCoeffs :
    outer41ModCoeffs outer41P17Coeffs =
      ([1] ++ List.replicate 15 0 : List (ZMod 2)) := by
  decide

private theorem outer41P17Odd (j : Nat) : Odd (outer41P17 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P17Coeffs 15
  exact outer41P17ModTwoCoeffs

private theorem outer41P17Pos (j : Nat) : 0 < outer41P17 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P17Coeffs]

private theorem outer41P17Cast (j : Nat) :
    (outer41P17 j : Int) = outer41P17Int j := by
  exact outer41HornerNat_cast j outer41P17Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q17ModTwoCoeffs :
    outer41ModCoeffs outer41Q17Coeffs =
      ([1] ++ List.replicate 16 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q17Odd (j : Nat) : Odd (outer41Q17 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q17Coeffs 16
  exact outer41Q17ModTwoCoeffs

private theorem outer41Q17Pos (j : Nat) : 0 < outer41Q17 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q17Coeffs]

private theorem outer41Q17Cast (j : Nat) :
    (outer41Q17 j : Int) = outer41Q17Int j := by
  exact outer41HornerNat_cast j outer41Q17Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P15ModTwoCoeffs :
    outer41ModCoeffs outer41P15Coeffs =
      ([1] ++ List.replicate 13 0 : List (ZMod 2)) := by
  decide

private theorem outer41P15Odd (j : Nat) : Odd (outer41P15 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P15Coeffs 13
  exact outer41P15ModTwoCoeffs

private theorem outer41P15Pos (j : Nat) : 0 < outer41P15 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P15Coeffs]

private theorem outer41P15Cast (j : Nat) :
    (outer41P15 j : Int) = outer41P15Int j := by
  exact outer41HornerNat_cast j outer41P15Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q15ModTwoCoeffs :
    outer41ModCoeffs outer41Q15Coeffs =
      ([1] ++ List.replicate 14 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q15Odd (j : Nat) : Odd (outer41Q15 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q15Coeffs 14
  exact outer41Q15ModTwoCoeffs

private theorem outer41Q15Pos (j : Nat) : 0 < outer41Q15 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q15Coeffs]

private theorem outer41Q15Cast (j : Nat) :
    (outer41Q15 j : Int) = outer41Q15Int j := by
  exact outer41HornerNat_cast j outer41Q15Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P13ModTwoCoeffs :
    outer41ModCoeffs outer41P13Coeffs =
      ([1] ++ List.replicate 11 0 : List (ZMod 2)) := by
  decide

private theorem outer41P13Odd (j : Nat) : Odd (outer41P13 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P13Coeffs 11
  exact outer41P13ModTwoCoeffs

private theorem outer41P13Pos (j : Nat) : 0 < outer41P13 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P13Coeffs]

private theorem outer41P13Cast (j : Nat) :
    (outer41P13 j : Int) = outer41P13Int j := by
  exact outer41HornerNat_cast j outer41P13Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q13ModTwoCoeffs :
    outer41ModCoeffs outer41Q13Coeffs =
      ([1] ++ List.replicate 12 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q13Odd (j : Nat) : Odd (outer41Q13 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q13Coeffs 12
  exact outer41Q13ModTwoCoeffs

private theorem outer41Q13Pos (j : Nat) : 0 < outer41Q13 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q13Coeffs]

private theorem outer41Q13Cast (j : Nat) :
    (outer41Q13 j : Int) = outer41Q13Int j := by
  exact outer41HornerNat_cast j outer41Q13Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P11ModTwoCoeffs :
    outer41ModCoeffs outer41P11Coeffs =
      ([1] ++ List.replicate 9 0 : List (ZMod 2)) := by
  decide

private theorem outer41P11Odd (j : Nat) : Odd (outer41P11 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P11Coeffs 9
  exact outer41P11ModTwoCoeffs

private theorem outer41P11Pos (j : Nat) : 0 < outer41P11 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P11Coeffs]

private theorem outer41P11Cast (j : Nat) :
    (outer41P11 j : Int) = outer41P11Int j := by
  exact outer41HornerNat_cast j outer41P11Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q11ModTwoCoeffs :
    outer41ModCoeffs outer41Q11Coeffs =
      ([1] ++ List.replicate 10 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q11Odd (j : Nat) : Odd (outer41Q11 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q11Coeffs 10
  exact outer41Q11ModTwoCoeffs

private theorem outer41Q11Pos (j : Nat) : 0 < outer41Q11 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q11Coeffs]

private theorem outer41Q11Cast (j : Nat) :
    (outer41Q11 j : Int) = outer41Q11Int j := by
  exact outer41HornerNat_cast j outer41Q11Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P9ModTwoCoeffs :
    outer41ModCoeffs outer41P9Coeffs =
      ([1] ++ List.replicate 7 0 : List (ZMod 2)) := by
  decide

private theorem outer41P9Odd (j : Nat) : Odd (outer41P9 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P9Coeffs 7
  exact outer41P9ModTwoCoeffs

private theorem outer41P9Pos (j : Nat) : 0 < outer41P9 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P9Coeffs]

private theorem outer41P9Cast (j : Nat) :
    (outer41P9 j : Int) = outer41P9Int j := by
  exact outer41HornerNat_cast j outer41P9Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q9ModTwoCoeffs :
    outer41ModCoeffs outer41Q9Coeffs =
      ([1] ++ List.replicate 8 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q9Odd (j : Nat) : Odd (outer41Q9 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q9Coeffs 8
  exact outer41Q9ModTwoCoeffs

private theorem outer41Q9Pos (j : Nat) : 0 < outer41Q9 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q9Coeffs]

private theorem outer41Q9Cast (j : Nat) :
    (outer41Q9 j : Int) = outer41Q9Int j := by
  exact outer41HornerNat_cast j outer41Q9Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P7ModTwoCoeffs :
    outer41ModCoeffs outer41P7Coeffs =
      ([1] ++ List.replicate 5 0 : List (ZMod 2)) := by
  decide

private theorem outer41P7Odd (j : Nat) : Odd (outer41P7 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P7Coeffs 5
  exact outer41P7ModTwoCoeffs

private theorem outer41P7Pos (j : Nat) : 0 < outer41P7 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P7Coeffs]

private theorem outer41P7Cast (j : Nat) :
    (outer41P7 j : Int) = outer41P7Int j := by
  exact outer41HornerNat_cast j outer41P7Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q7ModTwoCoeffs :
    outer41ModCoeffs outer41Q7Coeffs =
      ([1] ++ List.replicate 6 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q7Odd (j : Nat) : Odd (outer41Q7 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q7Coeffs 6
  exact outer41Q7ModTwoCoeffs

private theorem outer41Q7Pos (j : Nat) : 0 < outer41Q7 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q7Coeffs]

private theorem outer41Q7Cast (j : Nat) :
    (outer41Q7 j : Int) = outer41Q7Int j := by
  exact outer41HornerNat_cast j outer41Q7Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P5ModTwoCoeffs :
    outer41ModCoeffs outer41P5Coeffs =
      ([1] ++ List.replicate 3 0 : List (ZMod 2)) := by
  decide

private theorem outer41P5Odd (j : Nat) : Odd (outer41P5 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P5Coeffs 3
  exact outer41P5ModTwoCoeffs

private theorem outer41P5Pos (j : Nat) : 0 < outer41P5 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P5Coeffs]

private theorem outer41P5Cast (j : Nat) :
    (outer41P5 j : Int) = outer41P5Int j := by
  exact outer41HornerNat_cast j outer41P5Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q5ModTwoCoeffs :
    outer41ModCoeffs outer41Q5Coeffs =
      ([1] ++ List.replicate 4 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q5Odd (j : Nat) : Odd (outer41Q5 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q5Coeffs 4
  exact outer41Q5ModTwoCoeffs

private theorem outer41Q5Pos (j : Nat) : 0 < outer41Q5 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q5Coeffs]

private theorem outer41Q5Cast (j : Nat) :
    (outer41Q5 j : Int) = outer41Q5Int j := by
  exact outer41HornerNat_cast j outer41Q5Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P3ModTwoCoeffs :
    outer41ModCoeffs outer41P3Coeffs =
      ([1] ++ List.replicate 1 0 : List (ZMod 2)) := by
  decide

private theorem outer41P3Odd (j : Nat) : Odd (outer41P3 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P3Coeffs 1
  exact outer41P3ModTwoCoeffs

private theorem outer41P3Pos (j : Nat) : 0 < outer41P3 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P3Coeffs]

private theorem outer41P3Cast (j : Nat) :
    (outer41P3 j : Int) = outer41P3Int j := by
  exact outer41HornerNat_cast j outer41P3Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41Q3ModTwoCoeffs :
    outer41ModCoeffs outer41Q3Coeffs =
      ([1] ++ List.replicate 2 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q3Odd (j : Nat) : Odd (outer41Q3 j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q3Coeffs 2
  exact outer41Q3ModTwoCoeffs

private theorem outer41Q3Pos (j : Nat) : 0 < outer41Q3 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q3Coeffs]

private theorem outer41Q3Cast (j : Nat) :
    (outer41Q3 j : Int) = outer41Q3Int j := by
  exact outer41HornerNat_cast j outer41Q3Coeffs

set_option maxHeartbeats 1000000 in
private theorem outer41P23QuotientModTwoCoeffs :
    outer41ModCoeffs outer41P23QuotientCoeffs =
      ([1] ++ List.replicate 21 0 : List (ZMod 2)) := by
  decide

private theorem outer41P23QuotientOdd (j : Nat) :
    Odd (outer41P23Quotient j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41P23QuotientCoeffs 21
  exact outer41P23QuotientModTwoCoeffs

private theorem outer41P23QuotientPos (j : Nat) :
    0 < outer41P23Quotient j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41P23QuotientCoeffs]

set_option maxHeartbeats 1000000 in
private theorem outer41Q23QuotientModTwoCoeffs :
    outer41ModCoeffs outer41Q23QuotientCoeffs =
      ([1] ++ List.replicate 22 0 : List (ZMod 2)) := by
  decide

private theorem outer41Q23QuotientOdd (j : Nat) :
    Odd (outer41Q23Quotient j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41Q23QuotientCoeffs 22
  exact outer41Q23QuotientModTwoCoeffs

private theorem outer41Q23QuotientPos (j : Nat) :
    0 < outer41Q23Quotient j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41Q23QuotientCoeffs]

set_option maxHeartbeats 1000000 in
private theorem outer41AlphaModTwoCoeffs :
    outer41ModCoeffs outer41AlphaCoeffs =
      ([1] ++ List.replicate 37 0 : List (ZMod 2)) := by
  decide

private theorem outer41AlphaOdd (j : Nat) : Odd (outer41Alpha j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41AlphaCoeffs 37
  exact outer41AlphaModTwoCoeffs

private theorem outer41AlphaPos (j : Nat) : 0 < outer41Alpha j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41AlphaCoeffs]

set_option maxHeartbeats 1000000 in
private theorem outer41GammaModTwoCoeffs :
    outer41ModCoeffs outer41GammaCoeffs =
      ([1] ++ List.replicate 38 0 : List (ZMod 2)) := by
  decide

private theorem outer41GammaOdd (j : Nat) : Odd (outer41Gamma j) := by
  apply outer41HornerNat_odd_of_mod_two j outer41GammaCoeffs 38
  exact outer41GammaModTwoCoeffs

private theorem outer41GammaPos (j : Nat) : 0 < outer41Gamma j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41GammaCoeffs]

private theorem outer41AlphaCast (j : Nat) :
    (outer41Alpha j : Int) = outer41AlphaInt j := by
  exact outer41HornerNat_cast j outer41AlphaCoeffs

private theorem outer41GammaCast (j : Nat) :
    (outer41Gamma j : Int) = outer41GammaInt j := by
  exact outer41HornerNat_cast j outer41GammaCoeffs

private theorem outer41RawCoprime35 (j : Nat) :
    (outer41P35 j).Coprime (outer41Q35 j) := by
  refine outer41Coprime_of_support
    (A := outer41A34 j) (B := outer41B34 j) (S := 8428693448) ?_ ?_
  · rw [outer41P35Cast, outer41Q35Cast]
    exact outer41PrototypeEndpoint35 j
  · have h2 : ((outer41P35 j).gcd (outer41Q35 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P35Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right
    have h7 := outer41Gcd_coprime_prime (by norm_num : Nat.Prime 7)
      (outer41NoCommon35_7 j)
    have h4637 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 4637) (outer41NoCommon35_4637 j)
    rw [show 8428693448 = 2 ^ 3 * 7 ^ 2 * 4637 ^ 2 by norm_num]
    exact (h2.pow_right 3).mul_right (h7.pow_right 2) |>.mul_right
      (h4637.pow_right 2)

private theorem outer41RawCoprime37 (j : Nat) :
    (outer41P37 j).Coprime (outer41Q37 j) := by
  refine outer41Coprime_of_support
    (A := outer41A36 j) (B := outer41B36 j) (S := 43923) ?_ ?_
  · rw [outer41P37Cast, outer41Q37Cast]
    exact outer41Endpoint37 j
  · have h2 : ((outer41P37 j).gcd (outer41Q37 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P37Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon37_3 j)
    have h11 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 11) (outer41NoCommon37_11 j)
    rw [show 43923 = 2 ^ 0 * 3 ^ 1 * 11 ^ 4 by norm_num]
    exact (((h2.pow_right 0).mul_right (h3.pow_right 1)).mul_right (h11.pow_right 4))

private theorem outer41RawCoprime33 (j : Nat) :
    (outer41P33 j).Coprime (outer41Q33 j) := by
  refine outer41Coprime_of_support
    (A := outer41A32 j) (B := outer41B32 j) (S := 31451824818) ?_ ?_
  · rw [outer41P33Cast, outer41Q33Cast]
    exact outer41Endpoint33 j
  · have h2 : ((outer41P33 j).gcd (outer41Q33 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P33Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon33_3 j)
    have h41801 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 41801) (outer41NoCommon33_41801 j)
    rw [show 31451824818 = 2 ^ 1 * 3 ^ 2 * 41801 ^ 2 by norm_num]
    exact (((h2.pow_right 1).mul_right (h3.pow_right 2)).mul_right (h41801.pow_right 2))

private theorem outer41RawCoprime31 (j : Nat) :
    (outer41P31 j).Coprime (outer41Q31 j) := by
  refine outer41Coprime_of_support
    (A := outer41A30 j) (B := outer41B30 j) (S := 1214679324800) ?_ ?_
  · rw [outer41P31Cast, outer41Q31Cast]
    exact outer41Endpoint31 j
  · have h2 : ((outer41P31 j).gcd (outer41Q31 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P31Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h5 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 5) (outer41NoCommon31_5 j)
    have h19483 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 19483) (outer41NoCommon31_19483 j)
    rw [show 1214679324800 = 2 ^ 7 * 5 ^ 2 * 19483 ^ 2 by norm_num]
    exact (((h2.pow_right 7).mul_right (h5.pow_right 2)).mul_right (h19483.pow_right 2))

private theorem outer41RawCoprime29 (j : Nat) :
    (outer41P29 j).Coprime (outer41Q29 j) := by
  refine outer41Coprime_of_support
    (A := outer41A28 j) (B := outer41B28 j) (S := 572738492625408) ?_ ?_
  · rw [outer41P29Cast, outer41Q29Cast]
    exact outer41Endpoint29 j
  · have h2 : ((outer41P29 j).gcd (outer41Q29 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P29Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon29_3 j)
    have h117517 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 117517) (outer41NoCommon29_117517 j)
    rw [show 572738492625408 = 2 ^ 9 * 3 ^ 4 * 117517 ^ 2 by norm_num]
    exact (((h2.pow_right 9).mul_right (h3.pow_right 4)).mul_right (h117517.pow_right 2))

private theorem outer41RawCoprime27 (j : Nat) :
    (outer41P27 j).Coprime (outer41Q27 j) := by
  refine outer41Coprime_of_support
    (A := outer41A26 j) (B := outer41B26 j) (S := 44929151108448768) ?_ ?_
  · rw [outer41P27Cast, outer41Q27Cast]
    exact outer41Endpoint27 j
  · have h2 : ((outer41P27 j).gcd (outer41Q27 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P27Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon27_3 j)
    have h7 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 7) (outer41NoCommon27_7 j)
    have h47 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 47) (outer41NoCommon27_47 j)
    have h9491 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 9491) (outer41NoCommon27_9491 j)
    rw [show 44929151108448768 = 2 ^ 9 * 3 ^ 2 * 7 ^ 2 * 47 ^ 2 * 9491 ^ 2 by norm_num]
    exact (((((h2.pow_right 9).mul_right (h3.pow_right 2)).mul_right (h7.pow_right 2)).mul_right (h47.pow_right 2)).mul_right (h9491.pow_right 2))

private theorem outer41RawCoprime25 (j : Nat) :
    (outer41P25 j).Coprime (outer41Q25 j) := by
  refine outer41Coprime_of_support
    (A := outer41A24 j) (B := outer41B24 j) (S := 1848164145209522451468) ?_ ?_
  · rw [outer41P25Cast, outer41Q25Cast]
    exact outer41PrototypeEndpoint25 j
  · have h2 : ((outer41P25 j).gcd (outer41Q25 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P25Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon25_3 j)
    have h73 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 73) (outer41NoCommon25_73 j)
    have h18889231 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 18889231) (outer41NoCommon25_18889231 j)
    rw [show 1848164145209522451468 = 2 ^ 2 * 3 ^ 5 * 73 ^ 2 * 18889231 ^ 2 by norm_num]
    exact ((((h2.pow_right 2).mul_right (h3.pow_right 5)).mul_right (h73.pow_right 2)).mul_right (h18889231.pow_right 2))

private theorem outer41RawCoprime21 (j : Nat) :
    (outer41P21 j).Coprime (outer41Q21 j) := by
  refine outer41Coprime_of_support
    (A := outer41A20 j) (B := outer41B20 j) (S := 20310724547543276059208) ?_ ?_
  · rw [outer41P21Cast, outer41Q21Cast]
    exact outer41Endpoint21 j
  · have h2 : ((outer41P21 j).gcd (outer41Q21 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P21Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h229 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 229) (outer41NoCommon21_229 j)
    have h220030169 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 220030169) (outer41NoCommon21_220030169 j)
    rw [show 20310724547543276059208 = 2 ^ 3 * 229 ^ 2 * 220030169 ^ 2 by norm_num]
    exact (((h2.pow_right 3).mul_right (h229.pow_right 2)).mul_right (h220030169.pow_right 2))

private theorem outer41RawCoprime19 (j : Nat) :
    (outer41P19 j).Coprime (outer41Q19 j) := by
  refine outer41Coprime_of_support
    (A := outer41A18 j) (B := outer41B18 j) (S := 829924053674808976) ?_ ?_
  · rw [outer41P19Cast, outer41Q19Cast]
    exact outer41Endpoint19 j
  · have h2 : ((outer41P19 j).gcd (outer41Q19 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P19Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h13 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 13) (outer41NoCommon19_13 j)
    have h17519263 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 17519263) (outer41NoCommon19_17519263 j)
    rw [show 829924053674808976 = 2 ^ 4 * 13 ^ 2 * 17519263 ^ 2 by norm_num]
    exact (((h2.pow_right 4).mul_right (h13.pow_right 2)).mul_right (h17519263.pow_right 2))

private theorem outer41RawCoprime17 (j : Nat) :
    (outer41P17 j).Coprime (outer41Q17 j) := by
  refine outer41Coprime_of_support
    (A := outer41A16 j) (B := outer41B16 j) (S := 29853776087536915396) ?_ ?_
  · rw [outer41P17Cast, outer41Q17Cast]
    exact outer41Endpoint17 j
  · have h2 : ((outer41P17 j).gcd (outer41Q17 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P17Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h2731930457 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 2731930457) (outer41NoCommon17_2731930457 j)
    rw [show 29853776087536915396 = 2 ^ 2 * 2731930457 ^ 2 by norm_num]
    exact ((h2.pow_right 2).mul_right (h2731930457.pow_right 2))

private theorem outer41RawCoprime15 (j : Nat) :
    (outer41P15 j).Coprime (outer41Q15 j) := by
  refine outer41Coprime_of_support
    (A := outer41A14 j) (B := outer41B14 j) (S := 46319273757209672) ?_ ?_
  · rw [outer41P15Cast, outer41Q15Cast]
    exact outer41Endpoint15 j
  · have h2 : ((outer41P15 j).gcd (outer41Q15 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P15Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h31 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 31) (outer41NoCommon15_31 j)
    have h211 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 211) (outer41NoCommon15_211 j)
    have h11633 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 11633) (outer41NoCommon15_11633 j)
    rw [show 46319273757209672 = 2 ^ 3 * 31 ^ 2 * 211 ^ 2 * 11633 ^ 2 by norm_num]
    exact ((((h2.pow_right 3).mul_right (h31.pow_right 2)).mul_right (h211.pow_right 2)).mul_right (h11633.pow_right 2))

private theorem outer41RawCoprime13 (j : Nat) :
    (outer41P13 j).Coprime (outer41Q13 j) := by
  refine outer41Coprime_of_support
    (A := outer41A12 j) (B := outer41B12 j) (S := 23776391613186304) ?_ ?_
  · rw [outer41P13Cast, outer41Q13Cast]
    exact outer41Endpoint13 j
  · have h2 : ((outer41P13 j).gcd (outer41Q13 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P13Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h1487 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 1487) (outer41NoCommon13_1487 j)
    have h6481 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 6481) (outer41NoCommon13_6481 j)
    rw [show 23776391613186304 = 2 ^ 8 * 1487 ^ 2 * 6481 ^ 2 by norm_num]
    exact (((h2.pow_right 8).mul_right (h1487.pow_right 2)).mul_right (h6481.pow_right 2))

private theorem outer41RawCoprime11 (j : Nat) :
    (outer41P11 j).Coprime (outer41Q11 j) := by
  refine outer41Coprime_of_support
    (A := outer41A10 j) (B := outer41B10 j) (S := 21268539938988) ?_ ?_
  · rw [outer41P11Cast, outer41Q11Cast]
    exact outer41Endpoint11 j
  · have h2 : ((outer41P11 j).gcd (outer41Q11 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P11Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon11_3 j)
    have h53 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 53) (outer41NoCommon11_53 j)
    have h2791 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 2791) (outer41NoCommon11_2791 j)
    rw [show 21268539938988 = 2 ^ 2 * 3 ^ 5 * 53 ^ 2 * 2791 ^ 2 by norm_num]
    exact ((((h2.pow_right 2).mul_right (h3.pow_right 5)).mul_right (h53.pow_right 2)).mul_right (h2791.pow_right 2))

private theorem outer41RawCoprime9 (j : Nat) :
    (outer41P9 j).Coprime (outer41Q9 j) := by
  refine outer41Coprime_of_support
    (A := outer41A8 j) (B := outer41B8 j) (S := 40985168665156) ?_ ?_
  · rw [outer41P9Cast, outer41Q9Cast]
    exact outer41Endpoint9 j
  · have h2 : ((outer41P9 j).gcd (outer41Q9 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P9Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3200983 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3200983) (outer41NoCommon9_3200983 j)
    rw [show 40985168665156 = 2 ^ 2 * 3200983 ^ 2 by norm_num]
    exact ((h2.pow_right 2).mul_right (h3200983.pow_right 2))

private theorem outer41RawCoprime7 (j : Nat) :
    (outer41P7 j).Coprime (outer41Q7 j) := by
  refine outer41Coprime_of_support
    (A := outer41A6 j) (B := outer41B6 j) (S := 25222271863684) ?_ ?_
  · rw [outer41P7Cast, outer41Q7Cast]
    exact outer41Endpoint7 j
  · have h2 : ((outer41P7 j).gcd (outer41Q7 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P7Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h7 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 7) (outer41NoCommon7_7 j)
    have h358727 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 358727) (outer41NoCommon7_358727 j)
    rw [show 25222271863684 = 2 ^ 2 * 7 ^ 2 * 358727 ^ 2 by norm_num]
    exact (((h2.pow_right 2).mul_right (h7.pow_right 2)).mul_right (h358727.pow_right 2))

private theorem outer41RawCoprime5 (j : Nat) :
    (outer41P5 j).Coprime (outer41Q5 j) := by
  refine outer41Coprime_of_support
    (A := outer41A4 j) (B := outer41B4 j) (S := 204790641444) ?_ ?_
  · rw [outer41P5Cast, outer41Q5Cast]
    exact outer41Endpoint5 j
  · have h2 : ((outer41P5 j).gcd (outer41Q5 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P5Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon5_3 j)
    have h31 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 31) (outer41NoCommon5_31 j)
    have h811 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 811) (outer41NoCommon5_811 j)
    rw [show 204790641444 = 2 ^ 2 * 3 ^ 4 * 31 ^ 2 * 811 ^ 2 by norm_num]
    exact ((((h2.pow_right 2).mul_right (h3.pow_right 4)).mul_right (h31.pow_right 2)).mul_right (h811.pow_right 2))

private theorem outer41RawCoprime3 (j : Nat) :
    (outer41P3 j).Coprime (outer41Q3 j) := by
  refine outer41Coprime_of_support
    (A := outer41A2 j) (B := outer41B2 j) (S := 4234032) ?_ ?_
  · rw [outer41P3Cast, outer41Q3Cast]
    exact outer41Endpoint3 j
  · have h2 : ((outer41P3 j).gcd (outer41Q3 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P3Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right

    have h3 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 3) (outer41NoCommon3_3 j)
    have h11 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 11) (outer41NoCommon3_11 j)
    rw [show 4234032 = 2 ^ 4 * 3 ^ 7 * 11 ^ 2 by norm_num]
    exact (((h2.pow_right 4).mul_right (h3.pow_right 7)).mul_right (h11.pow_right 2))

private theorem outer41P23QuotientCast (j : Nat) :
    (outer41P23Quotient j : Int) = outer41P23QuotientInt j := by
  exact outer41HornerNat_cast j outer41P23QuotientCoeffs

private theorem outer41Q23QuotientCast (j : Nat) :
    (outer41Q23Quotient j : Int) = outer41Q23QuotientInt j := by
  exact outer41HornerNat_cast j outer41Q23QuotientCoeffs

private theorem outer41RawCoprime23_off
    (j : Nat) (hj : j % 13 ≠ 12) :
    (outer41P23 j).Coprime (outer41Q23 j) := by
  refine outer41Coprime_of_support
    (A := outer41A22 j) (B := outer41B22 j)
    (S := 3980114426571624327584) ?_ ?_
  · rw [outer41P23Cast, outer41Q23Cast]
    exact outer41Endpoint23 j
  · have h2 : ((outer41P23 j).gcd (outer41Q23 j)).Coprime 2 :=
      (Odd.of_dvd_nat (outer41P23Odd j)
        (Nat.gcd_dvd_left _ _)).coprime_two_right
    have h13 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 13) (by
        intro hCommon
        exact hj ((outer41Common23_thirteen_iff j).mp hCommon))
    have h10639 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 10639) (outer41NoCommon23_10639 j)
    have h290737 := outer41Gcd_coprime_prime
      (by norm_num : Nat.Prime 290737) (outer41NoCommon23_290737 j)
    rw [show 3980114426571624327584 =
      2 ^ 5 * 13 ^ 1 * 10639 ^ 2 * 290737 ^ 2 by norm_num]
    exact ((((h2.pow_right 5).mul_right (h13.pow_right 1)).mul_right
      (h10639.pow_right 2)).mul_right (h290737.pow_right 2))

private theorem outer41Quotient23Endpoint (j : Nat) :
    outer41A22 (13 * j + 12) * (outer41Q23Quotient j : Int) +
      outer41B22 (13 * j + 12) * (outer41P23Quotient j : Int) =
      306162648197817255968 := by
  have h := outer41Endpoint23 (13 * j + 12)
  rw [show outer41P23Int (13 * j + 12) =
      13 * outer41P23QuotientInt j by
        exact outer41P23Quotient_exact j,
    show outer41Q23Int (13 * j + 12) =
      13 * outer41Q23QuotientInt j by
        exact outer41Q23Quotient_exact j] at h
  rw [outer41P23QuotientCast, outer41Q23QuotientCast]
  ring_nf at h ⊢
  omega

private theorem outer41QuotientCoprime23 (j : Nat) :
    (outer41P23Quotient j).Coprime (outer41Q23Quotient j) := by
  refine outer41Coprime_of_support
    (A := outer41A22 (13 * j + 12))
    (B := outer41B22 (13 * j + 12))
    (S := 306162648197817255968) (outer41Quotient23Endpoint j) ?_
  have h2 : ((outer41P23Quotient j).gcd
      (outer41Q23Quotient j)).Coprime 2 :=
    (Odd.of_dvd_nat (outer41P23QuotientOdd j)
      (Nat.gcd_dvd_left _ _)).coprime_two_right
  have h10639 := outer41Gcd_coprime_prime
    (by norm_num : Nat.Prime 10639) (outer41NoCommon23Quotient_10639 j)
  have h290737 := outer41Gcd_coprime_prime
    (by norm_num : Nat.Prime 290737) (outer41NoCommon23Quotient_290737 j)
  rw [show 306162648197817255968 =
    2 ^ 5 * 10639 ^ 2 * 290737 ^ 2 by norm_num]
  exact (((h2.pow_right 5).mul_right (h10639.pow_right 2)).mul_right
    (h290737.pow_right 2))

private def outer41ReducedP23 (j : Nat) : Nat :=
  if j % 13 = 12 then outer41P23Quotient (j / 13) else outer41P23 j

private def outer41ReducedQ23 (j : Nat) : Nat :=
  if j % 13 = 12 then outer41Q23Quotient (j / 13) else outer41Q23 j

private theorem outer41ReducedCoprime23 (j : Nat) :
    (outer41ReducedP23 j).Coprime (outer41ReducedQ23 j) := by
  by_cases hj : j % 13 = 12
  · simp only [outer41ReducedP23, outer41ReducedQ23, if_pos hj]
    exact outer41QuotientCoprime23 (j / 13)
  · simp only [outer41ReducedP23, outer41ReducedQ23, if_neg hj]
    exact outer41RawCoprime23_off j hj

private theorem outer41P1Cast (j : Nat) :
    (outer41P1 j : Int) = outer41P1Int j := by
  exact outer41HornerNat_cast j outer41P1Coeffs

private theorem outer41Q1Cast (j : Nat) :
    (outer41Q1 j : Int) = outer41Q1Int j := by
  exact outer41HornerNat_cast j outer41Q1Coeffs

private theorem outer41Q1Odd (j : Nat) : Odd (outer41Q1 j) := by
  simp [outer41Q1, outer41Q1Coeffs, outer41HornerNat]

private theorem outer41Q1Pos (j : Nat) : 0 < outer41Q1 j := by
  simp [outer41Q1, outer41Q1Coeffs, outer41HornerNat]

private theorem outer41Coprime1 (j : Nat) :
    (outer41P1 j).Coprime (outer41Q1 j) := by
  simp [outer41P1, outer41Q1, outer41P1Coeffs, outer41Q1Coeffs,
    outer41HornerNat]

/-- The complete kernel input for one specialization-safe directed link in
the fixed-`41` coefficient chain.  The record stores hypotheses, not the
resulting Jacobi-symbol equality; composition is deliberately left to the
consumer. -/
structure Ss41LocalLinkCertificate (P Q p q : Nat) where
  h : Nat
  h_eq_gcd : h = Q.gcd q
  Q0 : Nat
  q0 : Nat
  r : Int
  h_pos : 0 < h
  h_odd : Odd h
  Q0_pos : 0 < Q0
  q0_pos : 0 < q0
  Q0_odd : Odd Q0
  q0_odd : Odd q0
  Q_factor : Q = h * Q0
  q_factor : q = h * q0
  p_coprime_h : p.Coprime h
  Q0_coprime_q0 : Q0.Coprime q0
  r_coprime_q0 : Int.gcd r q0 = 1
  cross : (h : Int) * r = (p : Int) * Q - (q : Int) * P
  e : Nat
  h0 : Nat
  t : Int
  Delta : Int
  e_eq_gcd : e = Int.gcd Delta h
  t0 : Int
  Delta0 : Int
  e_pos : 0 < e
  e_odd : Odd e
  h0_pos : 0 < h0
  h_factor : h = e * h0
  t_factor : t = (e : Int) * t0
  Delta_factor : Delta = (e : Int) * Delta0
  p_coprime_h0 : Int.gcd (p : Int) h0 = 1
  Delta0_coprime_h0 : Int.gcd Delta0 h0 = 1
  endpoint : Int.ModEq h0 ((p : Int) * t0) (Delta0 * P)

private theorem outer41IntGcd_sub_mul_eq_one
    {P p Q0 q0 : Nat}
    (hpq0 : p.Coprime q0) (hQ0q0 : Q0.Coprime q0) :
    Int.gcd ((p : Int) * Q0 - (q0 : Int) * P) q0 = 1 := by
  have hprod : (p * Q0).Coprime q0 := hpq0.mul_left hQ0q0
  apply Nat.dvd_one.mp
  have hleft : (Int.gcd ((p : Int) * Q0 - (q0 : Int) * P) q0 : Int) ∣
      ((p : Int) * Q0 - (q0 : Int) * P) := Int.gcd_dvd_left _ _
  have hright : (Int.gcd ((p : Int) * Q0 - (q0 : Int) * P) q0 : Int) ∣
      (q0 : Int) := Int.gcd_dvd_right _ _
  have hproduct : (Int.gcd ((p : Int) * Q0 - (q0 : Int) * P) q0 : Int) ∣
      (p : Int) * Q0 := by
    (convert Int.dvd_add hleft
      (dvd_mul_of_dvd_left hright (P : Int)) using 1
    ; ring)
  rw [← Int.natCast_dvd_natCast]
  have hbezout := Nat.gcd_eq_gcd_ab (p * Q0) q0
  rw [hprod.gcd_eq_one] at hbezout
  rw [hbezout]
  exact Int.dvd_add
    (dvd_mul_of_dvd_left hproduct (Nat.gcdA (p * Q0) q0))
    (dvd_mul_of_dvd_left hright (Nat.gcdB (p * Q0) q0))

private theorem outer41CrossKernelData
    {P Q p q : Nat}
    (hQpos : 0 < Q) (hqpos : 0 < q)
    (hQodd : Odd Q) (hqodd : Odd q)
    (hpq : p.Coprime q) :
    let h := Q.gcd q
    let Q0 := Q / h
    let q0 := q / h
    let r : Int := (p : Int) * Q0 - (q0 : Int) * P
    0 < h ∧ 0 < Q0 ∧ 0 < q0 ∧ Odd Q0 ∧ Odd q0 ∧
      Q = h * Q0 ∧ q = h * q0 ∧ p.Coprime h ∧
      Q0.Coprime q0 ∧ Int.gcd r q0 = 1 ∧
      (h : Int) * r = (p : Int) * Q - (q : Int) * P := by
  dsimp only
  let h := Q.gcd q
  have hhpos : 0 < h := Nat.gcd_pos_of_pos_left q hQpos
  have hQfac : Q = h * (Q / h) := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left Q q)]
  have hqfac : q = h * (q / h) := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right Q q)]
  have hQ0pos : 0 < Q / h := Nat.div_pos (Nat.le_of_dvd hQpos
    (Nat.gcd_dvd_left Q q)) hhpos
  have hq0pos : 0 < q / h := Nat.div_pos (Nat.le_of_dvd hqpos
    (Nat.gcd_dvd_right Q q)) hhpos
  have hQ0odd : Odd (Q / h) := by
    have hproduct : Odd (h * (Q / h)) := by
      rw [← hQfac]
      exact hQodd
    exact Nat.Odd.of_mul_right hproduct
  have hq0odd : Odd (q / h) := by
    have hproduct : Odd (h * (q / h)) := by
      rw [← hqfac]
      exact hqodd
    exact Nat.Odd.of_mul_right hproduct
  have hph : p.Coprime h :=
    hpq.coprime_dvd_right (Nat.gcd_dvd_right Q q)
  have hreduced : (Q / h).Coprime (q / h) :=
    Nat.gcd_div_gcd_div_gcd_of_pos_left hQpos
  have hpq0 : p.Coprime (q / h) :=
    hpq.coprime_dvd_right (by
      use h
      simpa [mul_comm] using hqfac)
  refine ⟨hhpos, hQ0pos, hq0pos, hQ0odd, hq0odd,
    hQfac, hqfac, hph, hreduced,
    outer41IntGcd_sub_mul_eq_one hpq0 hreduced, ?_⟩
  have hQfacInt : (Q : Int) = (h : Int) * ((Q / h : Nat) : Int) := by
    exact_mod_cast hQfac
  have hqfacInt : (q : Int) = (h : Int) * ((q / h : Nat) : Int) := by
    exact_mod_cast hqfac
  rw [hQfacInt, hqfacInt]
  ring

private noncomputable def outer41LocalLinkCertificate_of_endpoint
    {P Q p q : Nat} (t Delta : Int)
    (hQpos : 0 < Q) (hqpos : 0 < q)
    (hQodd : Odd Q) (hqodd : Odd q)
    (hpq : p.Coprime q)
    (hendpoint : Int.ModEq (Q.gcd q)
      ((p : Int) * t) (Delta * P)) :
    Ss41LocalLinkCertificate P Q p q := by
  let h := Q.gcd q
  let Q0 := Q / h
  let q0 := q / h
  let r : Int := (p : Int) * Q0 - (q0 : Int) * P
  let e := Int.gcd Delta h
  let h0 := h / e
  let t0 := t / (e : Int)
  let Delta0 := Delta / (e : Int)
  have hendpoint' : Int.ModEq h ((p : Int) * t) (Delta * P) := by
    simpa [h] using hendpoint
  have hkernel : 0 < h ∧ 0 < Q0 ∧ 0 < q0 ∧ Odd Q0 ∧ Odd q0 ∧
      Q = h * Q0 ∧ q = h * q0 ∧ p.Coprime h ∧
      Q0.Coprime q0 ∧ Int.gcd r q0 = 1 ∧
      (h : Int) * r = (p : Int) * Q - (q : Int) * P := by
    simpa [h, Q0, q0, r] using outer41CrossKernelData (P := P)
      hQpos hqpos hQodd hqodd hpq
  have hhpos := hkernel.1
  have hkernel1 := hkernel.2
  have hQ0pos := hkernel1.1
  have hkernel2 := hkernel1.2
  have hq0pos := hkernel2.1
  have hkernel3 := hkernel2.2
  have hQ0odd := hkernel3.1
  have hkernel4 := hkernel3.2
  have hq0odd := hkernel4.1
  have hkernel5 := hkernel4.2
  have hQfac := hkernel5.1
  have hkernel6 := hkernel5.2
  have hqfac := hkernel6.1
  have hkernel7 := hkernel6.2
  have hph := hkernel7.1
  have hkernel8 := hkernel7.2
  have hQ0q0 := hkernel8.1
  have hkernel9 := hkernel8.2
  have hrq0 := hkernel9.1
  have hcross := hkernel9.2
  have hhodd : Odd h := hQodd.of_dvd_nat (Nat.gcd_dvd_left Q q)
  have hepos : 0 < e := by
    simpa [e, Int.gcd_def] using
      (Nat.gcd_pos_of_pos_right Delta.natAbs hhpos)
  have hehInt : (e : Int) ∣ (h : Int) := Int.gcd_dvd_right Delta h
  have heh : e ∣ h := by exact_mod_cast hehInt
  have heodd : Odd e := hhodd.of_dvd_nat heh
  have hhfac : h = e * h0 := by
    exact (Nat.mul_div_cancel' heh).symm
  have hh0pos : 0 < h0 := Nat.div_pos (Nat.le_of_dvd hhpos heh) hepos
  have hpe : p.Coprime e := hph.coprime_dvd_right heh
  have hpeInt : Int.gcd (e : Int) p = 1 := by
    rw [Int.gcd_comm, Int.gcd_natCast_natCast]
    exact hpe.gcd_eq_one
  have heDelta : (e : Int) ∣ Delta := Int.gcd_dvd_left Delta h
  have heDifference : (e : Int) ∣ Delta * P - (p : Int) * t := by
    rw [Int.modEq_iff_dvd] at hendpoint'
    exact hehInt.trans hendpoint'
  have hept : (e : Int) ∣ (p : Int) * t := by
    have hDeltaP : (e : Int) ∣ Delta * P :=
      dvd_mul_of_dvd_left heDelta (P : Int)
    (convert Int.dvd_sub hDeltaP heDifference using 1
    ; ring)
  have het : (e : Int) ∣ t :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hept hpeInt
  have htFac : t = (e : Int) * t0 := by
    rw [show t0 = t / (e : Int) by rfl, mul_comm]
    exact (Int.ediv_mul_cancel het).symm
  have hDeltaFac : Delta = (e : Int) * Delta0 := by
    rw [show Delta0 = Delta / (e : Int) by rfl, mul_comm]
    exact (Int.ediv_mul_cancel heDelta).symm
  have hhfacInt : (h : Int) = (e : Int) * h0 := by
    exact_mod_cast hhfac
  have hendpoint0 : Int.ModEq h0
      ((p : Int) * t0) (Delta0 * P) := by
    have hscaled : Int.ModEq ((e : Int) * h0)
        ((e : Int) * ((p : Int) * t0))
        ((e : Int) * (Delta0 * P)) := by
      simpa [hhfacInt, htFac, hDeltaFac, mul_assoc, mul_left_comm,
        mul_comm] using hendpoint'
    exact Int.ModEq.mul_left_cancel' (Int.ofNat_ne_zero.mpr hepos.ne') hscaled
  have hpH0Nat : p.Coprime h0 := hph.coprime_dvd_right (by
    use e
    simpa [mul_comm] using hhfac)
  have hpH0 : Int.gcd (p : Int) h0 = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hpH0Nat.gcd_eq_one
  have hDeltaH0 : Int.gcd Delta0 h0 = 1 := by
    have hcop := Int.gcd_div_gcd_div_gcd
      (i := Delta) (j := (h : Int)) hepos
    simpa [e, h0, Delta0] using hcop
  exact
    { h := h
      h_eq_gcd := rfl
      Q0 := Q0
      q0 := q0
      r := r
      h_pos := hhpos
      h_odd := hhodd
      Q0_pos := hQ0pos
      q0_pos := hq0pos
      Q0_odd := hQ0odd
      q0_odd := hq0odd
      Q_factor := hQfac
      q_factor := hqfac
      p_coprime_h := hph
      Q0_coprime_q0 := hQ0q0
      r_coprime_q0 := hrq0
      cross := hcross
      e := e
      e_eq_gcd := rfl
      h0 := h0
      t := t
      Delta := Delta
      t0 := t0
      Delta0 := Delta0
      e_pos := hepos
      e_odd := heodd
      h0_pos := hh0pos
      h_factor := hhfac
      t_factor := htFac
      Delta_factor := hDeltaFac
      p_coprime_h0 := hpH0
      Delta0_coprime_h0 := hDeltaH0
      endpoint := hendpoint0 }

set_option maxHeartbeats 2000000 in
private theorem outer41Delta37Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A36Coeffs
        (outer41NatCoeffs outer41Q35Coeffs))
      (outer41CoeffMul outer41B36Coeffs
        (outer41NatCoeffs outer41P35Coeffs)) =
      [7460787] ++ List.replicate 68 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta37 (j : Nat) :
    outer41A36 j * outer41Q35Int j +
      outer41B36 j * outer41P35Int j = 7460787 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A36Coeffs
            (outer41NatCoeffs outer41Q35Coeffs))
          (outer41CoeffMul outer41B36Coeffs
            (outer41NatCoeffs outer41P35Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([7460787] ++ List.replicate 68 0) := by
          rw [outer41Delta37Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta35Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A34Coeffs
        (outer41NatCoeffs outer41Q33Coeffs))
      (outer41CoeffMul outer41B34Coeffs
        (outer41NatCoeffs outer41P33Coeffs)) =
      [5663033888] ++ List.replicate 64 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta35 (j : Nat) :
    outer41A34 j * outer41Q33Int j +
      outer41B34 j * outer41P33Int j = 5663033888 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A34Coeffs
            (outer41NatCoeffs outer41Q33Coeffs))
          (outer41CoeffMul outer41B34Coeffs
            (outer41NatCoeffs outer41P33Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([5663033888] ++ List.replicate 64 0) := by
          rw [outer41Delta35Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta33Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A32Coeffs
        (outer41NatCoeffs outer41Q31Coeffs))
      (outer41CoeffMul outer41B32Coeffs
        (outer41NatCoeffs outer41P31Coeffs)) =
      [70190303138] ++ List.replicate 60 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta33 (j : Nat) :
    outer41A32 j * outer41Q31Int j +
      outer41B32 j * outer41P31Int j = 70190303138 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A32Coeffs
            (outer41NatCoeffs outer41Q31Coeffs))
          (outer41CoeffMul outer41B32Coeffs
            (outer41NatCoeffs outer41P31Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([70190303138] ++ List.replicate 60 0) := by
          rw [outer41Delta33Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta31Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A30Coeffs
        (outer41NatCoeffs outer41Q29Coeffs))
      (outer41CoeffMul outer41B30Coeffs
        (outer41NatCoeffs outer41P29Coeffs)) =
      [-76043699573192] ++ List.replicate 56 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta31 (j : Nat) :
    outer41A30 j * outer41Q29Int j +
      outer41B30 j * outer41P29Int j = -76043699573192 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A30Coeffs
            (outer41NatCoeffs outer41Q29Coeffs))
          (outer41CoeffMul outer41B30Coeffs
            (outer41NatCoeffs outer41P29Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-76043699573192] ++ List.replicate 56 0) := by
          rw [outer41Delta31Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta29Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A28Coeffs
        (outer41NatCoeffs outer41Q27Coeffs))
      (outer41CoeffMul outer41B28Coeffs
        (outer41NatCoeffs outer41P27Coeffs)) =
      [-130250792070340516] ++ List.replicate 52 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta29 (j : Nat) :
    outer41A28 j * outer41Q27Int j +
      outer41B28 j * outer41P27Int j = -130250792070340516 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A28Coeffs
            (outer41NatCoeffs outer41Q27Coeffs))
          (outer41CoeffMul outer41B28Coeffs
            (outer41NatCoeffs outer41P27Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-130250792070340516] ++ List.replicate 52 0) := by
          rw [outer41Delta29Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta27Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A26Coeffs
        (outer41NatCoeffs outer41Q25Coeffs))
      (outer41CoeffMul outer41B26Coeffs
        (outer41NatCoeffs outer41P25Coeffs)) =
      [-84184410193007063552] ++ List.replicate 48 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta27 (j : Nat) :
    outer41A26 j * outer41Q25Int j +
      outer41B26 j * outer41P25Int j = -84184410193007063552 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A26Coeffs
            (outer41NatCoeffs outer41Q25Coeffs))
          (outer41CoeffMul outer41B26Coeffs
            (outer41NatCoeffs outer41P25Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-84184410193007063552] ++ List.replicate 48 0) := by
          rw [outer41Delta27Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta25Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A24Coeffs
        (outer41NatCoeffs outer41Q23Coeffs))
      (outer41CoeffMul outer41B24Coeffs
        (outer41NatCoeffs outer41P23Coeffs)) =
      [416899238562200686968] ++ List.replicate 44 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta25 (j : Nat) :
    outer41A24 j * outer41Q23Int j +
      outer41B24 j * outer41P23Int j = 416899238562200686968 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A24Coeffs
            (outer41NatCoeffs outer41Q23Coeffs))
          (outer41CoeffMul outer41B24Coeffs
            (outer41NatCoeffs outer41P23Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([416899238562200686968] ++ List.replicate 44 0) := by
          rw [outer41Delta25Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta23Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A22Coeffs
        (outer41NatCoeffs outer41Q21Coeffs))
      (outer41CoeffMul outer41B22Coeffs
        (outer41NatCoeffs outer41P21Coeffs)) =
      [-1193619024076561249467528] ++ List.replicate 40 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta23 (j : Nat) :
    outer41A22 j * outer41Q21Int j +
      outer41B22 j * outer41P21Int j = -1193619024076561249467528 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A22Coeffs
            (outer41NatCoeffs outer41Q21Coeffs))
          (outer41CoeffMul outer41B22Coeffs
            (outer41NatCoeffs outer41P21Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-1193619024076561249467528] ++ List.replicate 40 0) := by
          rw [outer41Delta23Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta21Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A20Coeffs
        (outer41NatCoeffs outer41Q19Coeffs))
      (outer41CoeffMul outer41B20Coeffs
        (outer41NatCoeffs outer41P19Coeffs)) =
      [35550752715303478416] ++ List.replicate 36 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta21 (j : Nat) :
    outer41A20 j * outer41Q19Int j +
      outer41B20 j * outer41P19Int j = 35550752715303478416 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A20Coeffs
            (outer41NatCoeffs outer41Q19Coeffs))
          (outer41CoeffMul outer41B20Coeffs
            (outer41NatCoeffs outer41P19Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([35550752715303478416] ++ List.replicate 36 0) := by
          rw [outer41Delta21Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta19Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A18Coeffs
        (outer41NatCoeffs outer41Q17Coeffs))
      (outer41CoeffMul outer41B18Coeffs
        (outer41NatCoeffs outer41P17Coeffs)) =
      [5865233985562754888] ++ List.replicate 32 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta19 (j : Nat) :
    outer41A18 j * outer41Q17Int j +
      outer41B18 j * outer41P17Int j = 5865233985562754888 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A18Coeffs
            (outer41NatCoeffs outer41Q17Coeffs))
          (outer41CoeffMul outer41B18Coeffs
            (outer41NatCoeffs outer41P17Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([5865233985562754888] ++ List.replicate 32 0) := by
          rw [outer41Delta19Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta17Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A16Coeffs
        (outer41NatCoeffs outer41Q15Coeffs))
      (outer41CoeffMul outer41B16Coeffs
        (outer41NatCoeffs outer41P15Coeffs)) =
      [28908959694322500] ++ List.replicate 28 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta17 (j : Nat) :
    outer41A16 j * outer41Q15Int j +
      outer41B16 j * outer41P15Int j = 28908959694322500 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A16Coeffs
            (outer41NatCoeffs outer41Q15Coeffs))
          (outer41CoeffMul outer41B16Coeffs
            (outer41NatCoeffs outer41P15Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([28908959694322500] ++ List.replicate 28 0) := by
          rw [outer41Delta17Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta15Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A14Coeffs
        (outer41NatCoeffs outer41Q13Coeffs))
      (outer41CoeffMul outer41B14Coeffs
        (outer41NatCoeffs outer41P13Coeffs)) =
      [-305367476170019904] ++ List.replicate 24 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta15 (j : Nat) :
    outer41A14 j * outer41Q13Int j +
      outer41B14 j * outer41P13Int j = -305367476170019904 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A14Coeffs
            (outer41NatCoeffs outer41Q13Coeffs))
          (outer41CoeffMul outer41B14Coeffs
            (outer41NatCoeffs outer41P13Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-305367476170019904] ++ List.replicate 24 0) := by
          rw [outer41Delta15Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta13Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A12Coeffs
        (outer41NatCoeffs outer41Q11Coeffs))
      (outer41CoeffMul outer41B12Coeffs
        (outer41NatCoeffs outer41P11Coeffs)) =
      [40390792256855236] ++ List.replicate 20 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta13 (j : Nat) :
    outer41A12 j * outer41Q11Int j +
      outer41B12 j * outer41P11Int j = 40390792256855236 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A12Coeffs
            (outer41NatCoeffs outer41Q11Coeffs))
          (outer41CoeffMul outer41B12Coeffs
            (outer41NatCoeffs outer41P11Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([40390792256855236] ++ List.replicate 20 0) := by
          rw [outer41Delta13Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta11Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A10Coeffs
        (outer41NatCoeffs outer41Q9Coeffs))
      (outer41CoeffMul outer41B10Coeffs
        (outer41NatCoeffs outer41P9Coeffs)) =
      [-36236309341536] ++ List.replicate 16 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta11 (j : Nat) :
    outer41A10 j * outer41Q9Int j +
      outer41B10 j * outer41P9Int j = -36236309341536 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A10Coeffs
            (outer41NatCoeffs outer41Q9Coeffs))
          (outer41CoeffMul outer41B10Coeffs
            (outer41NatCoeffs outer41P9Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([-36236309341536] ++ List.replicate 16 0) := by
          rw [outer41Delta11Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta9Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A8Coeffs
        (outer41NatCoeffs outer41Q7Coeffs))
      (outer41CoeffMul outer41B8Coeffs
        (outer41NatCoeffs outer41P7Coeffs)) =
      [9990542851524] ++ List.replicate 12 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta9 (j : Nat) :
    outer41A8 j * outer41Q7Int j +
      outer41B8 j * outer41P7Int j = 9990542851524 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A8Coeffs
            (outer41NatCoeffs outer41Q7Coeffs))
          (outer41CoeffMul outer41B8Coeffs
            (outer41NatCoeffs outer41P7Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([9990542851524] ++ List.replicate 12 0) := by
          rw [outer41Delta9Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta7Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A6Coeffs
        (outer41NatCoeffs outer41Q5Coeffs))
      (outer41CoeffMul outer41B6Coeffs
        (outer41NatCoeffs outer41P5Coeffs)) =
      [607510599200] ++ List.replicate 8 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta7 (j : Nat) :
    outer41A6 j * outer41Q5Int j +
      outer41B6 j * outer41P5Int j = 607510599200 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A6Coeffs
            (outer41NatCoeffs outer41Q5Coeffs))
          (outer41CoeffMul outer41B6Coeffs
            (outer41NatCoeffs outer41P5Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([607510599200] ++ List.replicate 8 0) := by
          rw [outer41Delta7Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta5Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A4Coeffs
        (outer41NatCoeffs outer41Q3Coeffs))
      (outer41CoeffMul outer41B4Coeffs
        (outer41NatCoeffs outer41P3Coeffs)) =
      [983700496] ++ List.replicate 4 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta5 (j : Nat) :
    outer41A4 j * outer41Q3Int j +
      outer41B4 j * outer41P3Int j = 983700496 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A4Coeffs
            (outer41NatCoeffs outer41Q3Coeffs))
          (outer41CoeffMul outer41B4Coeffs
            (outer41NatCoeffs outer41P3Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([983700496] ++ List.replicate 4 0) := by
          rw [outer41Delta5Coeffs]
    _ = _ := by simp [outer41HornerInt]

set_option maxHeartbeats 2000000 in
private theorem outer41Delta3Coeffs :
    outer41CoeffAdd
      (outer41CoeffMul outer41A2Coeffs
        (outer41NatCoeffs outer41Q1Coeffs))
      (outer41CoeffMul outer41B2Coeffs
        (outer41NatCoeffs outer41P1Coeffs)) =
      [4563] ++ List.replicate 1 0 := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41Delta3 (j : Nat) :
    outer41A2 j * outer41Q1Int j +
      outer41B2 j * outer41P1Int j = 4563 := by
  calc
    _ = outer41HornerInt j
        (outer41CoeffAdd
          (outer41CoeffMul outer41A2Coeffs
            (outer41NatCoeffs outer41Q1Coeffs))
          (outer41CoeffMul outer41B2Coeffs
            (outer41NatCoeffs outer41P1Coeffs))) := by
          symm
          rw [outer41HornerInt_add, outer41HornerInt_mul,
            outer41HornerInt_mul]
          rfl
    _ = outer41HornerInt j
        ([4563] ++ List.replicate 1 0) := by
          rw [outer41Delta3Coeffs]
    _ = _ := by simp [outer41HornerInt]

private theorem outer41EndpointModEq
    {P Q p q : Nat} (A B t Delta : Int)
    (hsupport : A * Q + B * P = t)
    (hdeterminant : A * q + B * p = Delta) :
    Int.ModEq (Q.gcd q) ((p : Int) * t) (Delta * P) := by
  rw [Int.modEq_iff_dvd]
  have hQ : ((Q.gcd q : Nat) : Int) ∣ (Q : Int) := by
    exact_mod_cast Nat.gcd_dvd_left Q q
  have hq : ((Q.gcd q : Nat) : Int) ∣ (q : Int) := by
    exact_mod_cast Nat.gcd_dvd_right Q q
  rw [← hsupport, ← hdeterminant]
  have hinner : ((Q.gcd q : Nat) : Int) ∣
      (q : Int) * P - (p : Int) * Q :=
    dvd_sub (dvd_mul_of_dvd_left hq P)
      (dvd_mul_of_dvd_right hQ (p : Int))
  have heq : (A * (q : Int) + B * p) * P -
      (p : Int) * (A * Q + B * P) =
      ((q : Int) * P - (p : Int) * Q) * A := by ring
  rw [heq]
  simpa [mul_comm] using dvd_mul_of_dvd_right hinner A

set_option maxHeartbeats 500000 in
private noncomputable def outer41RootLocalLink (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41Alpha j) (outer41Gamma j)
      (outer41P37 j) (outer41Q37 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (5 : Int)) (Delta := (245 : Int))
    (outer41GammaPos j) (outer41Q37Pos j)
    (outer41GammaOdd j) (outer41Q37Odd j)
    (outer41RawCoprime37 j)
    (outer41EndpointModEq
      (outer41A38 j) (outer41B38 j)
      (5 : Int) (245 : Int)
      (by
        rw [outer41AlphaCast, outer41GammaCast]
        exact outer41RootEndpoint j)
      (by
        rw [outer41P37Cast, outer41Q37Cast]
        calc
          outer41A38 j * outer41Q37Int j +
              outer41B38 j * outer41P37Int j =
              outer41P37Int j * outer41B38 j +
                outer41Q37Int j * outer41A38 j := by ring
          _ = 245 := outer41RootDeterminant j))

private noncomputable def outer41LocalLink37 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P37 j) (outer41Q37 j)
      (outer41P35 j) (outer41Q35 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (43923 : Int)) (Delta := (7460787 : Int))
    (outer41Q37Pos j) (outer41Q35Pos j)
    (outer41Q37Odd j) (outer41Q35Odd j)
    (outer41RawCoprime35 j)
    (outer41EndpointModEq
      (outer41A36 j) (outer41B36 j)
      (43923 : Int) (7460787 : Int)
      (by
        rw [outer41P37Cast, outer41Q37Cast]
        exact outer41Endpoint37 j)
      (by
        rw [outer41P35Cast, outer41Q35Cast]
        exact outer41Delta37 j))

private noncomputable def outer41LocalLink35 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P35 j) (outer41Q35 j)
      (outer41P33 j) (outer41Q33 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (8428693448 : Int)) (Delta := (5663033888 : Int))
    (outer41Q35Pos j) (outer41Q33Pos j)
    (outer41Q35Odd j) (outer41Q33Odd j)
    (outer41RawCoprime33 j)
    (outer41EndpointModEq
      (outer41A34 j) (outer41B34 j)
      (8428693448 : Int) (5663033888 : Int)
      (by
        rw [outer41P35Cast, outer41Q35Cast]
        exact outer41PrototypeEndpoint35 j)
      (by
        rw [outer41P33Cast, outer41Q33Cast]
        exact outer41Delta35 j))

private noncomputable def outer41LocalLink33 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P33 j) (outer41Q33 j)
      (outer41P31 j) (outer41Q31 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (31451824818 : Int)) (Delta := (70190303138 : Int))
    (outer41Q33Pos j) (outer41Q31Pos j)
    (outer41Q33Odd j) (outer41Q31Odd j)
    (outer41RawCoprime31 j)
    (outer41EndpointModEq
      (outer41A32 j) (outer41B32 j)
      (31451824818 : Int) (70190303138 : Int)
      (by
        rw [outer41P33Cast, outer41Q33Cast]
        exact outer41Endpoint33 j)
      (by
        rw [outer41P31Cast, outer41Q31Cast]
        exact outer41Delta33 j))

private noncomputable def outer41LocalLink31 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P31 j) (outer41Q31 j)
      (outer41P29 j) (outer41Q29 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (1214679324800 : Int)) (Delta := (-76043699573192 : Int))
    (outer41Q31Pos j) (outer41Q29Pos j)
    (outer41Q31Odd j) (outer41Q29Odd j)
    (outer41RawCoprime29 j)
    (outer41EndpointModEq
      (outer41A30 j) (outer41B30 j)
      (1214679324800 : Int) (-76043699573192 : Int)
      (by
        rw [outer41P31Cast, outer41Q31Cast]
        exact outer41Endpoint31 j)
      (by
        rw [outer41P29Cast, outer41Q29Cast]
        exact outer41Delta31 j))

private noncomputable def outer41LocalLink29 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P29 j) (outer41Q29 j)
      (outer41P27 j) (outer41Q27 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (572738492625408 : Int)) (Delta := (-130250792070340516 : Int))
    (outer41Q29Pos j) (outer41Q27Pos j)
    (outer41Q29Odd j) (outer41Q27Odd j)
    (outer41RawCoprime27 j)
    (outer41EndpointModEq
      (outer41A28 j) (outer41B28 j)
      (572738492625408 : Int) (-130250792070340516 : Int)
      (by
        rw [outer41P29Cast, outer41Q29Cast]
        exact outer41Endpoint29 j)
      (by
        rw [outer41P27Cast, outer41Q27Cast]
        exact outer41Delta29 j))

private noncomputable def outer41LocalLink27 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P27 j) (outer41Q27 j)
      (outer41P25 j) (outer41Q25 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (44929151108448768 : Int)) (Delta := (-84184410193007063552 : Int))
    (outer41Q27Pos j) (outer41Q25Pos j)
    (outer41Q27Odd j) (outer41Q25Odd j)
    (outer41RawCoprime25 j)
    (outer41EndpointModEq
      (outer41A26 j) (outer41B26 j)
      (44929151108448768 : Int) (-84184410193007063552 : Int)
      (by
        rw [outer41P27Cast, outer41Q27Cast]
        exact outer41Endpoint27 j)
      (by
        rw [outer41P25Cast, outer41Q25Cast]
        exact outer41Delta27 j))

private noncomputable def outer41LocalLink21 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P21 j) (outer41Q21 j)
      (outer41P19 j) (outer41Q19 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (20310724547543276059208 : Int)) (Delta := (35550752715303478416 : Int))
    (outer41Q21Pos j) (outer41Q19Pos j)
    (outer41Q21Odd j) (outer41Q19Odd j)
    (outer41RawCoprime19 j)
    (outer41EndpointModEq
      (outer41A20 j) (outer41B20 j)
      (20310724547543276059208 : Int) (35550752715303478416 : Int)
      (by
        rw [outer41P21Cast, outer41Q21Cast]
        exact outer41Endpoint21 j)
      (by
        rw [outer41P19Cast, outer41Q19Cast]
        exact outer41Delta21 j))

private noncomputable def outer41LocalLink19 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P19 j) (outer41Q19 j)
      (outer41P17 j) (outer41Q17 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (829924053674808976 : Int)) (Delta := (5865233985562754888 : Int))
    (outer41Q19Pos j) (outer41Q17Pos j)
    (outer41Q19Odd j) (outer41Q17Odd j)
    (outer41RawCoprime17 j)
    (outer41EndpointModEq
      (outer41A18 j) (outer41B18 j)
      (829924053674808976 : Int) (5865233985562754888 : Int)
      (by
        rw [outer41P19Cast, outer41Q19Cast]
        exact outer41Endpoint19 j)
      (by
        rw [outer41P17Cast, outer41Q17Cast]
        exact outer41Delta19 j))

private noncomputable def outer41LocalLink17 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P17 j) (outer41Q17 j)
      (outer41P15 j) (outer41Q15 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (29853776087536915396 : Int)) (Delta := (28908959694322500 : Int))
    (outer41Q17Pos j) (outer41Q15Pos j)
    (outer41Q17Odd j) (outer41Q15Odd j)
    (outer41RawCoprime15 j)
    (outer41EndpointModEq
      (outer41A16 j) (outer41B16 j)
      (29853776087536915396 : Int) (28908959694322500 : Int)
      (by
        rw [outer41P17Cast, outer41Q17Cast]
        exact outer41Endpoint17 j)
      (by
        rw [outer41P15Cast, outer41Q15Cast]
        exact outer41Delta17 j))

private noncomputable def outer41LocalLink15 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P15 j) (outer41Q15 j)
      (outer41P13 j) (outer41Q13 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (46319273757209672 : Int)) (Delta := (-305367476170019904 : Int))
    (outer41Q15Pos j) (outer41Q13Pos j)
    (outer41Q15Odd j) (outer41Q13Odd j)
    (outer41RawCoprime13 j)
    (outer41EndpointModEq
      (outer41A14 j) (outer41B14 j)
      (46319273757209672 : Int) (-305367476170019904 : Int)
      (by
        rw [outer41P15Cast, outer41Q15Cast]
        exact outer41Endpoint15 j)
      (by
        rw [outer41P13Cast, outer41Q13Cast]
        exact outer41Delta15 j))

private noncomputable def outer41LocalLink13 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P13 j) (outer41Q13 j)
      (outer41P11 j) (outer41Q11 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (23776391613186304 : Int)) (Delta := (40390792256855236 : Int))
    (outer41Q13Pos j) (outer41Q11Pos j)
    (outer41Q13Odd j) (outer41Q11Odd j)
    (outer41RawCoprime11 j)
    (outer41EndpointModEq
      (outer41A12 j) (outer41B12 j)
      (23776391613186304 : Int) (40390792256855236 : Int)
      (by
        rw [outer41P13Cast, outer41Q13Cast]
        exact outer41Endpoint13 j)
      (by
        rw [outer41P11Cast, outer41Q11Cast]
        exact outer41Delta13 j))

private noncomputable def outer41LocalLink11 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P11 j) (outer41Q11 j)
      (outer41P9 j) (outer41Q9 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (21268539938988 : Int)) (Delta := (-36236309341536 : Int))
    (outer41Q11Pos j) (outer41Q9Pos j)
    (outer41Q11Odd j) (outer41Q9Odd j)
    (outer41RawCoprime9 j)
    (outer41EndpointModEq
      (outer41A10 j) (outer41B10 j)
      (21268539938988 : Int) (-36236309341536 : Int)
      (by
        rw [outer41P11Cast, outer41Q11Cast]
        exact outer41Endpoint11 j)
      (by
        rw [outer41P9Cast, outer41Q9Cast]
        exact outer41Delta11 j))

private noncomputable def outer41LocalLink9 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P9 j) (outer41Q9 j)
      (outer41P7 j) (outer41Q7 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (40985168665156 : Int)) (Delta := (9990542851524 : Int))
    (outer41Q9Pos j) (outer41Q7Pos j)
    (outer41Q9Odd j) (outer41Q7Odd j)
    (outer41RawCoprime7 j)
    (outer41EndpointModEq
      (outer41A8 j) (outer41B8 j)
      (40985168665156 : Int) (9990542851524 : Int)
      (by
        rw [outer41P9Cast, outer41Q9Cast]
        exact outer41Endpoint9 j)
      (by
        rw [outer41P7Cast, outer41Q7Cast]
        exact outer41Delta9 j))

private noncomputable def outer41LocalLink7 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P7 j) (outer41Q7 j)
      (outer41P5 j) (outer41Q5 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (25222271863684 : Int)) (Delta := (607510599200 : Int))
    (outer41Q7Pos j) (outer41Q5Pos j)
    (outer41Q7Odd j) (outer41Q5Odd j)
    (outer41RawCoprime5 j)
    (outer41EndpointModEq
      (outer41A6 j) (outer41B6 j)
      (25222271863684 : Int) (607510599200 : Int)
      (by
        rw [outer41P7Cast, outer41Q7Cast]
        exact outer41Endpoint7 j)
      (by
        rw [outer41P5Cast, outer41Q5Cast]
        exact outer41Delta7 j))

private noncomputable def outer41LocalLink5 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P5 j) (outer41Q5 j)
      (outer41P3 j) (outer41Q3 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (204790641444 : Int)) (Delta := (983700496 : Int))
    (outer41Q5Pos j) (outer41Q3Pos j)
    (outer41Q5Odd j) (outer41Q3Odd j)
    (outer41RawCoprime3 j)
    (outer41EndpointModEq
      (outer41A4 j) (outer41B4 j)
      (204790641444 : Int) (983700496 : Int)
      (by
        rw [outer41P5Cast, outer41Q5Cast]
        exact outer41Endpoint5 j)
      (by
        rw [outer41P3Cast, outer41Q3Cast]
        exact outer41Delta5 j))

private noncomputable def outer41LocalLink3 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P3 j) (outer41Q3 j)
      (outer41P1 j) (outer41Q1 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (4234032 : Int)) (Delta := (4563 : Int))
    (outer41Q3Pos j) (outer41Q1Pos j)
    (outer41Q3Odd j) (outer41Q1Odd j)
    (outer41Coprime1 j)
    (outer41EndpointModEq
      (outer41A2 j) (outer41B2 j)
      (4234032 : Int) (4563 : Int)
      (by
        rw [outer41P3Cast, outer41Q3Cast]
        exact outer41Endpoint3 j)
      (by
        rw [outer41P1Cast, outer41Q1Cast]
        exact outer41Delta3 j))

private theorem outer41_thirteen_mul_div_add_twelve
    (j : Nat) (hj : j % 13 = 12) :
    13 * (j / 13) + 12 = j := by
  have hdivision := Nat.mod_add_div j 13
  omega

private theorem outer41ReducedP23Cast (j : Nat) :
    (outer41ReducedP23 j : Int) =
      if j % 13 = 12 then outer41P23QuotientInt (j / 13)
      else outer41P23Int j := by
  by_cases hj : j % 13 = 12
  · rw [if_pos hj, outer41ReducedP23, if_pos hj]
    exact outer41P23QuotientCast (j / 13)
  · rw [if_neg hj, outer41ReducedP23, if_neg hj]
    exact outer41P23Cast j

private theorem outer41ReducedQ23Cast (j : Nat) :
    (outer41ReducedQ23 j : Int) =
      if j % 13 = 12 then outer41Q23QuotientInt (j / 13)
      else outer41Q23Int j := by
  by_cases hj : j % 13 = 12
  · rw [if_pos hj, outer41ReducedQ23, if_pos hj]
    exact outer41Q23QuotientCast (j / 13)
  · rw [if_neg hj, outer41ReducedQ23, if_neg hj]
    exact outer41Q23Cast j

private theorem outer41ReducedQ23Odd (j : Nat) :
    Odd (outer41ReducedQ23 j) := by
  by_cases hj : j % 13 = 12
  · simp only [outer41ReducedQ23, if_pos hj]
    exact outer41Q23QuotientOdd (j / 13)
  · simp only [outer41ReducedQ23, if_neg hj]
    exact outer41Q23Odd j

private theorem outer41ReducedQ23Pos (j : Nat) :
    0 < outer41ReducedQ23 j := by
  by_cases hj : j % 13 = 12
  · simp only [outer41ReducedQ23, if_pos hj]
    exact outer41Q23QuotientPos (j / 13)
  · simp only [outer41ReducedQ23, if_neg hj]
    exact outer41Q23Pos j

private theorem outer41Delta25Quotient (j : Nat) :
    outer41A24 (13 * j + 12) * (outer41Q23Quotient j : Int) +
      outer41B24 (13 * j + 12) * (outer41P23Quotient j : Int) =
      32069172197092360536 := by
  have h := outer41Delta25 (13 * j + 12)
  rw [show outer41P23Int (13 * j + 12) =
      13 * outer41P23QuotientInt j by
        exact outer41P23Quotient_exact j,
    show outer41Q23Int (13 * j + 12) =
      13 * outer41Q23QuotientInt j by
        exact outer41Q23Quotient_exact j] at h
  rw [outer41P23QuotientCast, outer41Q23QuotientCast]
  ring_nf at h ⊢
  omega

private theorem outer41Delta25QuotientInt (j : Nat) :
    outer41A24 (13 * j + 12) * outer41Q23QuotientInt j +
      outer41B24 (13 * j + 12) * outer41P23QuotientInt j =
      32069172197092360536 := by
  rw [← outer41P23QuotientCast, ← outer41Q23QuotientCast]
  exact outer41Delta25Quotient j

private theorem outer41Endpoint23QuotientInt (j : Nat) :
    outer41A22 (13 * j + 12) * outer41Q23QuotientInt j +
      outer41B22 (13 * j + 12) * outer41P23QuotientInt j =
      306162648197817255968 := by
  rw [← outer41P23QuotientCast, ← outer41Q23QuotientCast]
  exact outer41Quotient23Endpoint j

private theorem outer41P23Int_reconstruct_reduced
    (j : Nat) (hj : j % 13 = 12) :
    outer41P23Int j = 13 * (outer41ReducedP23 j : Int) := by
  calc
    outer41P23Int j = (outer41P23 j : Int) := (outer41P23Cast j).symm
    _ = (13 * outer41P23Quotient (j / 13) : Nat) := by
      exact_mod_cast outer41P23Quotient_reconstruct j hj
    _ = 13 * (outer41ReducedP23 j : Int) := by
      rw [Nat.cast_mul, outer41ReducedP23, if_pos hj]
      rfl

private theorem outer41Q23Int_reconstruct_reduced
    (j : Nat) (hj : j % 13 = 12) :
    outer41Q23Int j = 13 * (outer41ReducedQ23 j : Int) := by
  calc
    outer41Q23Int j = (outer41Q23 j : Int) := (outer41Q23Cast j).symm
    _ = (13 * outer41Q23Quotient (j / 13) : Nat) := by
      exact_mod_cast outer41Q23Quotient_reconstruct j hj
    _ = 13 * (outer41ReducedQ23 j : Int) := by
      rw [Nat.cast_mul, outer41ReducedQ23, if_pos hj]
      rfl

set_option maxHeartbeats 300000 in
private theorem outer41Delta25Reduced (j : Nat) :
    outer41A24 j * (outer41ReducedQ23 j : Int) +
      outer41B24 j * (outer41ReducedP23 j : Int) =
      if j % 13 = 12 then 32069172197092360536
      else 416899238562200686968 := by
  by_cases hj : j % 13 = 12
  · rw [if_pos hj]
    have h := outer41Delta25 j
    rw [outer41P23Int_reconstruct_reduced j hj,
      outer41Q23Int_reconstruct_reduced j hj] at h
    ring_nf at h ⊢
    omega
  · rw [outer41ReducedP23Cast, outer41ReducedQ23Cast]
    simp only [if_neg hj]
    exact outer41Delta25 j

set_option maxHeartbeats 300000 in
private theorem outer41Endpoint23Reduced (j : Nat) :
    outer41A22 j * (outer41ReducedQ23 j : Int) +
      outer41B22 j * (outer41ReducedP23 j : Int) =
      if j % 13 = 12 then 306162648197817255968
      else 3980114426571624327584 := by
  by_cases hj : j % 13 = 12
  · rw [if_pos hj]
    have h := outer41Endpoint23 j
    rw [outer41P23Int_reconstruct_reduced j hj,
      outer41Q23Int_reconstruct_reduced j hj] at h
    ring_nf at h ⊢
    omega
  · rw [outer41ReducedP23Cast, outer41ReducedQ23Cast]
    simp only [if_neg hj]
    exact outer41Endpoint23 j

private noncomputable def outer41LocalLink25 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41P25 j) (outer41Q25 j)
      (outer41ReducedP23 j) (outer41ReducedQ23 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := (1848164145209522451468 : Int))
    (Delta := if j % 13 = 12 then 32069172197092360536
      else 416899238562200686968)
    (outer41Q25Pos j) (outer41ReducedQ23Pos j)
    (outer41Q25Odd j) (outer41ReducedQ23Odd j)
    (outer41ReducedCoprime23 j)
    (outer41EndpointModEq
      (outer41A24 j) (outer41B24 j)
      (1848164145209522451468 : Int)
      (if j % 13 = 12 then 32069172197092360536
        else 416899238562200686968)
      (by
        rw [outer41P25Cast, outer41Q25Cast]
        exact outer41PrototypeEndpoint25 j)
      (outer41Delta25Reduced j))

private noncomputable def outer41LocalLink23 (j : Nat) :
    Ss41LocalLinkCertificate
      (outer41ReducedP23 j) (outer41ReducedQ23 j)
      (outer41P21 j) (outer41Q21 j) :=
  outer41LocalLinkCertificate_of_endpoint
    (t := if j % 13 = 12 then 306162648197817255968
      else 3980114426571624327584)
    (Delta := (-1193619024076561249467528 : Int))
    (outer41ReducedQ23Pos j) (outer41Q21Pos j)
    (outer41ReducedQ23Odd j) (outer41Q21Odd j)
    (outer41RawCoprime21 j)
    (outer41EndpointModEq
      (outer41A22 j) (outer41B22 j)
      (if j % 13 = 12 then 306162648197817255968
        else 3980114426571624327584)
      (-1193619024076561249467528 : Int)
      (outer41Endpoint23Reduced j)
      (by
        rw [outer41P21Cast, outer41Q21Cast]
        exact outer41Delta23 j))

private def outer41ChainP (j : Nat) (position : Fin 19) : Nat :=
  match position.1 with
  | 0 => outer41P37 j
  | 1 => outer41P35 j
  | 2 => outer41P33 j
  | 3 => outer41P31 j
  | 4 => outer41P29 j
  | 5 => outer41P27 j
  | 6 => outer41P25 j
  | 7 => outer41ReducedP23 j
  | 8 => outer41P21 j
  | 9 => outer41P19 j
  | 10 => outer41P17 j
  | 11 => outer41P15 j
  | 12 => outer41P13 j
  | 13 => outer41P11 j
  | 14 => outer41P9 j
  | 15 => outer41P7 j
  | 16 => outer41P5 j
  | 17 => outer41P3 j
  | _ => outer41P1 j

private def outer41ChainQ (j : Nat) (position : Fin 19) : Nat :=
  match position.1 with
  | 0 => outer41Q37 j
  | 1 => outer41Q35 j
  | 2 => outer41Q33 j
  | 3 => outer41Q31 j
  | 4 => outer41Q29 j
  | 5 => outer41Q27 j
  | 6 => outer41Q25 j
  | 7 => outer41ReducedQ23 j
  | 8 => outer41Q21 j
  | 9 => outer41Q19 j
  | 10 => outer41Q17 j
  | 11 => outer41Q15 j
  | 12 => outer41Q13 j
  | 13 => outer41Q11 j
  | 14 => outer41Q9 j
  | 15 => outer41Q7 j
  | 16 => outer41Q5 j
  | 17 => outer41Q3 j
  | _ => outer41Q1 j

private noncomputable def outer41LocalLinks (j : Nat) (position : Fin 18) :
    Ss41LocalLinkCertificate
      (outer41ChainP j ⟨position, by omega⟩)
      (outer41ChainQ j ⟨position, by omega⟩)
      (outer41ChainP j ⟨position + 1, by omega⟩)
      (outer41ChainQ j ⟨position + 1, by omega⟩) := by
  rcases position with ⟨position, hposition⟩
  interval_cases position
  · exact outer41LocalLink37 j
  · exact outer41LocalLink35 j
  · exact outer41LocalLink33 j
  · exact outer41LocalLink31 j
  · exact outer41LocalLink29 j
  · exact outer41LocalLink27 j
  · exact outer41LocalLink25 j
  · exact outer41LocalLink23 j
  · exact outer41LocalLink21 j
  · exact outer41LocalLink19 j
  · exact outer41LocalLink17 j
  · exact outer41LocalLink15 j
  · exact outer41LocalLink13 j
  · exact outer41LocalLink11 j
  · exact outer41LocalLink9 j
  · exact outer41LocalLink7 j
  · exact outer41LocalLink5 j
  · exact outer41LocalLink3 j

/-- The total fixed-`41` local certificate.  Its link field covers exactly the
18 directed links; it contains no directed Jacobi equality and performs no
telescope composition. -/
structure Ss41LocalCertificate (j : Nat) where
  P : Fin 19 → Nat
  Q : Fin 19 → Nat
  coefficientIndex : Fin 19 → Nat
  coefficientIndex_eq : ∀ position,
    coefficientIndex position = 37 - 2 * position.1
  links : ∀ position : Fin 18,
    Ss41LocalLinkCertificate
      (P ⟨position, by omega⟩) (Q ⟨position, by omega⟩)
      (P ⟨position + 1, by omega⟩) (Q ⟨position + 1, by omega⟩)
  terminal_P : P ⟨18, by decide⟩ = 0
  terminal_Q : Q ⟨18, by decide⟩ = 1
  rawP23 : Nat
  rawQ23 : Nat
  reductionFactor23 : Nat
  reductionFactor23_eq :
    reductionFactor23 = if j % 13 = 12 then 13 else 1
  rawP23_factor : rawP23 = reductionFactor23 * P ⟨7, by decide⟩
  rawQ23_factor : rawQ23 = reductionFactor23 * Q ⟨7, by decide⟩
  reduced23_coprime : (P ⟨7, by decide⟩).Coprime (Q ⟨7, by decide⟩)
  rootP : Nat
  rootQ : Nat
  rootLink : Ss41LocalLinkCertificate
    rootP rootQ (P ⟨0, by decide⟩) (Q ⟨0, by decide⟩)
  root_e_mod25 : rootLink.e =
    if j % 25 = 4 ∨ j % 25 = 9 ∨ j % 25 = 14 ∨
        j % 25 = 19 ∨ j % 25 = 24
    then 5 else 1
  root_correction :
    jacobiSym (rootP : Int) rootLink.e *
      jacobiSym (P ⟨0, by decide⟩ : Int) rootLink.e = 1
  link37_e : (links ⟨0, by decide⟩).e =
    if j % 3 = 0 then 3 else 1
  link37_correction :
    jacobiSym (P ⟨0, by decide⟩ : Int) (links ⟨0, by decide⟩).e *
      jacobiSym (P ⟨1, by decide⟩ : Int) (links ⟨0, by decide⟩).e = 1
  link25_e : (links ⟨6, by decide⟩).e =
    if j % 27 = 25 then 27
    else if j % 9 = 7 then 9
    else if j % 9 = 1 ∨ j % 9 = 4 then 3
    else 1
  link25_correction :
    jacobiSym (P ⟨6, by decide⟩ : Int) (links ⟨6, by decide⟩).e *
      jacobiSym (P ⟨7, by decide⟩ : Int) (links ⟨6, by decide⟩).e =
        if j % 27 = 25 then -1
        else if j % 9 = 1 ∨ j % 9 = 4 then -1
        else 1
  link11_e : (links ⟨13, by decide⟩).e =
    if j % 9 = 8 then 27
    else if j % 3 = 2 then 9
    else if j % 3 = 1 then 3
    else 1
  link11_correction :
    jacobiSym (P ⟨13, by decide⟩ : Int) (links ⟨13, by decide⟩).e *
      jacobiSym (P ⟨14, by decide⟩ : Int) (links ⟨13, by decide⟩).e = 1
  factor13_offClassSymbol : j % 13 ≠ 12 →
    jacobiSym (j + 1 : Nat) 13 =
      if j % 13 = 1 ∨ j % 13 = 4 ∨ j % 13 = 5 ∨
          j % 13 = 6 ∨ j % 13 = 7 ∨ j % 13 = 10
      then -1 else 1
  terminalLink_e : (links ⟨17, by decide⟩).e = 1
  ordinary_squareclassNeutral : ∀ position : Fin 18,
    position.1 ∈ [1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14, 15, 16] →
      ∃ u v a b : Nat,
        (links position).t.natAbs = 2 ^ u * a ^ 2 ∧
        (links position).Delta.natAbs = 2 ^ v * b ^ 2

set_option maxHeartbeats 300000 in
private theorem outer41P23_reduction (j : Nat) :
    outer41P23 j = (if j % 13 = 12 then 13 else 1) *
      outer41ReducedP23 j := by
  by_cases hj : j % 13 = 12
  · rw [if_pos hj, outer41ReducedP23, if_pos hj]
    exact outer41P23Quotient_reconstruct j hj
  · rw [if_neg hj, outer41ReducedP23, if_neg hj, one_mul]

set_option maxHeartbeats 300000 in
private theorem outer41Q23_reduction (j : Nat) :
    outer41Q23 j = (if j % 13 = 12 then 13 else 1) *
      outer41ReducedQ23 j := by
  by_cases hj : j % 13 = 12
  · rw [if_pos hj, outer41ReducedQ23, if_pos hj]
    exact outer41Q23Quotient_reconstruct j hj
  · rw [if_neg hj, outer41ReducedQ23, if_neg hj, one_mul]

private theorem outer41HornerNat_mod (j modulus : Nat)
    (coefficients : List Nat) :
    outer41HornerNat j coefficients % modulus =
      outer41HornerNat (j % modulus) coefficients % modulus := by
  induction coefficients with
  | nil => simp [outer41HornerNat]
  | cons a coefficients ih =>
      simp only [outer41HornerNat]
      simp [Nat.add_mod, Nat.mul_mod, ih]

set_option maxHeartbeats 1000000 in
private theorem outer41Primary37 (j : Nat) :
    Nat.gcd 9 (Nat.gcd (outer41Q37 j) (outer41Q35 j)) =
      if j % 3 = 0 then 3 else 1 := by
  have hQ37 := outer41HornerNat_mod j 9 outer41Q37Coeffs
  have hQ35 := outer41HornerNat_mod j 9 outer41Q35Coeffs
  change outer41Q37 j % 9 = _ at hQ37
  change outer41Q35 j % 9 = _ at hQ35
  have hQ35mod3 : outer41Q35 j % 3 = (outer41Q35 j % 9) % 3 :=
    (Nat.mod_mod_of_dvd (outer41Q35 j) (by decide : 3 ∣ 9)).symm
  have hjmod3 : j % 3 = (j % 9) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
  have hj : j % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 9 <;>
    norm_num [outer41Q37, outer41Q35, outer41Q37Coeffs,
      outer41Q35Coeffs, outer41HornerNat] at hQ37 hQ35
  all_goals change outer41Q37 j % 9 = _ at hQ37
  all_goals change outer41Q35 j % 9 = _ at hQ35
  all_goals rw [hQ35] at hQ35mod3
  all_goals norm_num at hQ35mod3
  all_goals norm_num at hjmod3
  all_goals rw [← Nat.gcd_assoc]
  all_goals rw [show Nat.gcd 9 (outer41Q37 j) =
    Nat.gcd (outer41Q37 j % 9) 9 by exact Nat.gcd_rec 9 (outer41Q37 j)]
  all_goals rw [hQ37]
  all_goals norm_num [hjmod3]
  all_goals rw [Nat.gcd_rec, hQ35mod3]
  all_goals norm_num [hjmod3]

set_option maxHeartbeats 2000000 in
private theorem outer41RootPrimary (j : Nat) :
    Nat.gcd 25 (Nat.gcd (outer41Gamma j) (outer41Q37 j)) =
      if j % 5 = 4 then 5 else 1 := by
  have hGamma := outer41HornerNat_mod j 25 outer41GammaCoeffs
  have hQ37 := outer41HornerNat_mod j 25 outer41Q37Coeffs
  change outer41Gamma j % 25 = _ at hGamma
  change outer41Q37 j % 25 = _ at hQ37
  have hQ37mod5 : outer41Q37 j % 5 = (outer41Q37 j % 25) % 5 :=
    (Nat.mod_mod_of_dvd (outer41Q37 j) (by decide : 5 ∣ 25)).symm
  have hjmod5 : j % 5 = (j % 25) % 5 :=
    (Nat.mod_mod_of_dvd j (by decide : 5 ∣ 25)).symm
  have hj : j % 25 < 25 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 25 <;>
    norm_num [outer41Gamma, outer41Q37, outer41GammaCoeffs,
      outer41Q37Coeffs, outer41HornerNat] at hGamma hQ37
  all_goals change outer41Gamma j % 25 = _ at hGamma
  all_goals change outer41Q37 j % 25 = _ at hQ37
  all_goals rw [hQ37] at hQ37mod5
  all_goals norm_num at hQ37mod5
  all_goals norm_num at hjmod5
  all_goals rw [← Nat.gcd_assoc]
  all_goals rw [show Nat.gcd 25 (outer41Gamma j) =
    Nat.gcd (outer41Gamma j % 25) 25 by
      exact Nat.gcd_rec 25 (outer41Gamma j)]
  all_goals rw [hGamma]
  all_goals norm_num [hjmod5]
  all_goals rw [Nat.gcd_rec]
  all_goals simp only [hQ37mod5]
  all_goals norm_num [hjmod5]

set_option maxHeartbeats 4000000 in
private theorem outer41Primary25Raw (j : Nat) :
    Nat.gcd 81 (Nat.gcd (outer41Q25 j) (outer41Q23 j)) =
      if j % 27 = 25 then 27
      else if j % 9 = 7 then 9
      else if j % 9 = 1 ∨ j % 9 = 4 then 3
      else 1 := by
  have hQ25 := outer41HornerNat_mod j 81 outer41Q25Coeffs
  have hQ23 := outer41HornerNat_mod j 81 outer41Q23Coeffs
  change outer41Q25 j % 81 = _ at hQ25
  change outer41Q23 j % 81 = _ at hQ23
  have hQ23mod3 : outer41Q23 j % 3 = (outer41Q23 j % 81) % 3 :=
    (Nat.mod_mod_of_dvd (outer41Q23 j) (by decide : 3 ∣ 81)).symm
  have hQ23mod9 : outer41Q23 j % 9 = (outer41Q23 j % 81) % 9 :=
    (Nat.mod_mod_of_dvd (outer41Q23 j) (by decide : 9 ∣ 81)).symm
  have hQ23mod27 : outer41Q23 j % 27 = (outer41Q23 j % 81) % 27 :=
    (Nat.mod_mod_of_dvd (outer41Q23 j) (by decide : 27 ∣ 81)).symm
  have hjmod27 : j % 27 = (j % 81) % 27 :=
    (Nat.mod_mod_of_dvd j (by decide : 27 ∣ 81)).symm
  have hjmod9 : j % 9 = (j % 81) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 81)).symm
  have hj : j % 81 < 81 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 81 <;>
    norm_num [outer41Q25, outer41Q23, outer41Q25Coeffs,
      outer41Q23Coeffs, outer41HornerNat] at hQ25 hQ23
  all_goals change outer41Q25 j % 81 = _ at hQ25
  all_goals change outer41Q23 j % 81 = _ at hQ23
  all_goals rw [hQ23] at hQ23mod3 hQ23mod9 hQ23mod27
  all_goals norm_num at hQ23mod3 hQ23mod9 hQ23mod27
  all_goals norm_num at hjmod27 hjmod9
  all_goals rw [← Nat.gcd_assoc]
  all_goals rw [show Nat.gcd 81 (outer41Q25 j) =
    Nat.gcd (outer41Q25 j % 81) 81 by
      exact Nat.gcd_rec 81 (outer41Q25 j)]
  all_goals rw [hQ25]
  all_goals norm_num [hjmod27, hjmod9]
  all_goals rw [Nat.gcd_rec]
  all_goals simp only [hQ23, hQ23mod3, hQ23mod9, hQ23mod27]
  all_goals norm_num [hjmod27, hjmod9]

set_option maxHeartbeats 4000000 in
private theorem outer41Primary11 (j : Nat) :
    Nat.gcd 81 (Nat.gcd (outer41Q11 j) (outer41Q9 j)) =
      if j % 9 = 8 then 27
      else if j % 3 = 2 then 9
      else if j % 3 = 1 then 3
      else 1 := by
  have hQ11 := outer41HornerNat_mod j 81 outer41Q11Coeffs
  have hQ9 := outer41HornerNat_mod j 81 outer41Q9Coeffs
  change outer41Q11 j % 81 = _ at hQ11
  change outer41Q9 j % 81 = _ at hQ9
  have hQ9mod3 : outer41Q9 j % 3 = (outer41Q9 j % 81) % 3 :=
    (Nat.mod_mod_of_dvd (outer41Q9 j) (by decide : 3 ∣ 81)).symm
  have hQ9mod9 : outer41Q9 j % 9 = (outer41Q9 j % 81) % 9 :=
    (Nat.mod_mod_of_dvd (outer41Q9 j) (by decide : 9 ∣ 81)).symm
  have hQ9mod27 : outer41Q9 j % 27 = (outer41Q9 j % 81) % 27 :=
    (Nat.mod_mod_of_dvd (outer41Q9 j) (by decide : 27 ∣ 81)).symm
  have hjmod9 : j % 9 = (j % 81) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 81)).symm
  have hjmod3 : j % 3 = (j % 81) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 81)).symm
  have hj : j % 81 < 81 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 81 <;>
    norm_num [outer41Q11, outer41Q9, outer41Q11Coeffs,
      outer41Q9Coeffs, outer41HornerNat] at hQ11 hQ9
  all_goals change outer41Q11 j % 81 = _ at hQ11
  all_goals change outer41Q9 j % 81 = _ at hQ9
  all_goals rw [hQ9] at hQ9mod3 hQ9mod9 hQ9mod27
  all_goals norm_num at hQ9mod3 hQ9mod9 hQ9mod27
  all_goals norm_num at hjmod9 hjmod3
  all_goals rw [← Nat.gcd_assoc]
  all_goals rw [show Nat.gcd 81 (outer41Q11 j) =
    Nat.gcd (outer41Q11 j % 81) 81 by
      exact Nat.gcd_rec 81 (outer41Q11 j)]
  all_goals rw [hQ11]
  all_goals norm_num [hjmod9, hjmod3]
  all_goals rw [Nat.gcd_rec]
  all_goals simp only [hQ9mod3, hQ9mod9, hQ9mod27]
  all_goals norm_num [hjmod9, hjmod3]

private theorem outer41_gcd_gcd_mul_of_coprime
    (m a c b : Nat) (hcm : c.Coprime m) :
    Nat.gcd m (Nat.gcd a (c * b)) = Nat.gcd m (Nat.gcd a b) := by
  have hsmall : c.Coprime (Nat.gcd m a) :=
    hcm.coprime_dvd_right (Nat.gcd_dvd_left m a)
  calc
    Nat.gcd m (Nat.gcd a (c * b)) =
        Nat.gcd (Nat.gcd m a) (c * b) :=
      (Nat.gcd_assoc m a (c * b)).symm
    _ = Nat.gcd (Nat.gcd m a) b := by
      simpa [Nat.gcd_comm] using hsmall.gcd_mul_left_cancel b
    _ = Nat.gcd m (Nat.gcd a b) := Nat.gcd_assoc m a b

private theorem outer41Primary25 (j : Nat) :
    Nat.gcd 81
        (Nat.gcd (outer41Q25 j) (outer41ReducedQ23 j)) =
      if j % 27 = 25 then 27
      else if j % 9 = 7 then 9
      else if j % 9 = 1 ∨ j % 9 = 4 then 3
      else 1 := by
  let factor := if j % 13 = 12 then 13 else 1
  have hfactor : factor.Coprime 81 := by
    dsimp [factor]
    split <;> norm_num
  calc
    Nat.gcd 81 (Nat.gcd (outer41Q25 j) (outer41ReducedQ23 j)) =
        Nat.gcd 81
          (Nat.gcd (outer41Q25 j) (factor * outer41ReducedQ23 j)) :=
      (outer41_gcd_gcd_mul_of_coprime 81 (outer41Q25 j) factor
        (outer41ReducedQ23 j) hfactor).symm
    _ = Nat.gcd 81 (Nat.gcd (outer41Q25 j) (outer41Q23 j)) := by
      rw [outer41Q23_reduction]
    _ = _ := outer41Primary25Raw j

private theorem outer41_gcd_of_gcd_multiple
    (a m h : Nat) (ham : a ∣ m) :
    Nat.gcd a h = Nat.gcd a (Nat.gcd m h) := by
  calc
    Nat.gcd a h = Nat.gcd (Nat.gcd a m) h := by
      rw [Nat.gcd_eq_left_iff_dvd.mpr ham]
    _ = Nat.gcd a (Nat.gcd m h) := Nat.gcd_assoc a m h

private theorem outer41RootCap (j : Nat) :
    Nat.gcd 5 (outer41RootLocalLink j).h =
      if j % 5 = 4 then 5 else 1 := by
  rw [(outer41RootLocalLink j).h_eq_gcd]
  rw [outer41_gcd_of_gcd_multiple 5 25 _ (by decide), outer41RootPrimary]
  split <;> norm_num

private theorem outer41Cap37 (j : Nat) :
    Nat.gcd 3 (outer41LocalLink37 j).h =
      if j % 3 = 0 then 3 else 1 := by
  rw [(outer41LocalLink37 j).h_eq_gcd]
  rw [outer41_gcd_of_gcd_multiple 3 9 _ (by decide), outer41Primary37]
  split <;> norm_num

private theorem outer41Cap25 (j : Nat) :
    Nat.gcd 27 (outer41LocalLink25 j).h =
      if j % 27 = 25 then 27
      else if j % 9 = 7 then 9
      else if j % 9 = 1 ∨ j % 9 = 4 then 3
      else 1 := by
  rw [(outer41LocalLink25 j).h_eq_gcd]
  rw [outer41_gcd_of_gcd_multiple 27 81 _ (by decide), outer41Primary25]
  repeat' first | split <;> norm_num

private theorem outer41Cap11 (j : Nat) :
    Nat.gcd 27 (outer41LocalLink11 j).h =
      if j % 9 = 8 then 27
      else if j % 3 = 2 then 9
      else if j % 3 = 1 then 3
      else 1 := by
  rw [(outer41LocalLink11 j).h_eq_gcd]
  rw [outer41_gcd_of_gcd_multiple 27 81 _ (by decide), outer41Primary11]
  repeat' first | split <;> norm_num

private theorem outer41LocalLink_e_eq_capped
    {P Q p q : Nat} (certificate : Ss41LocalLinkCertificate P Q p q)
    (cap expected : Nat)
    (hconstant : Nat.gcd certificate.t.natAbs
      certificate.Delta.natAbs = cap)
    (hcap : Nat.gcd cap certificate.h = expected) :
    certificate.e = expected := by
  have hetInt : (certificate.e : Int) ∣ certificate.t := by
    exact ⟨certificate.t0, certificate.t_factor⟩
  have heDeltaInt : (certificate.e : Int) ∣ certificate.Delta := by
    exact ⟨certificate.Delta0, certificate.Delta_factor⟩
  have het : certificate.e ∣ certificate.t.natAbs :=
    Int.natCast_dvd.mp hetInt
  have heDelta : certificate.e ∣ certificate.Delta.natAbs :=
    Int.natCast_dvd.mp heDeltaInt
  have hecap : certificate.e ∣ cap := by
    rw [← hconstant]
    exact Nat.dvd_gcd het heDelta
  have heh : certificate.e ∣ certificate.h := by
    use certificate.h0
    exact certificate.h_factor
  apply Nat.dvd_antisymm
  · rw [← hcap]
    exact Nat.dvd_gcd hecap heh
  · have hexpectedCap : expected ∣ cap := by
      rw [← hcap]
      exact Nat.gcd_dvd_left cap certificate.h
    have hexpectedDeltaNat : expected ∣ certificate.Delta.natAbs :=
      hexpectedCap.trans (by
        rw [← hconstant]
        exact Nat.gcd_dvd_right _ _)
    have hexpectedDeltaInt : (expected : Int) ∣ certificate.Delta :=
      Int.natCast_dvd.mpr hexpectedDeltaNat
    have hexpectedHNat : expected ∣ certificate.h := by
      rw [← hcap]
      exact Nat.gcd_dvd_right cap certificate.h
    have hexpectedHInt : (expected : Int) ∣ (certificate.h : Int) := by
      exact_mod_cast hexpectedHNat
    have hexpectedGcd : expected ∣
        Int.gcd certificate.Delta certificate.h := by
      exact Int.dvd_gcd hexpectedDeltaInt hexpectedHInt
    rwa [← certificate.e_eq_gcd] at hexpectedGcd

set_option maxHeartbeats 2000000 in
private theorem outer41RootConstants (j : Nat) :
    (outer41RootLocalLink j).t = 5 ∧
      (outer41RootLocalLink j).Delta = 245 := by
  simp only [outer41RootLocalLink,
    outer41LocalLinkCertificate_of_endpoint]
  simp

set_option maxHeartbeats 2000000 in
private theorem outer41Constants37 (j : Nat) :
    (outer41LocalLink37 j).t = 43923 ∧
      (outer41LocalLink37 j).Delta = 7460787 := by
  simp only [outer41LocalLink37,
    outer41LocalLinkCertificate_of_endpoint]
  simp

set_option maxHeartbeats 2000000 in
private theorem outer41Constants25 (j : Nat) :
    (outer41LocalLink25 j).t = 1848164145209522451468 ∧
      (outer41LocalLink25 j).Delta =
        if j % 13 = 12 then 32069172197092360536
        else 416899238562200686968 := by
  simp only [outer41LocalLink25,
    outer41LocalLinkCertificate_of_endpoint]
  simp

set_option maxHeartbeats 2000000 in
private theorem outer41Constants11 (j : Nat) :
    (outer41LocalLink11 j).t = 21268539938988 ∧
      (outer41LocalLink11 j).Delta = -36236309341536 := by
  simp only [outer41LocalLink11,
    outer41LocalLinkCertificate_of_endpoint]
  simp

private theorem outer41Gcd108_eq_gcd27
    {P Q p q : Nat} (certificate : Ss41LocalLinkCertificate P Q p q) :
    Nat.gcd 108 certificate.h = Nat.gcd 27 certificate.h := by
  have h4 : Nat.Coprime 4 certificate.h := by
    simpa [show (4 : Nat) = 2 ^ 2 by decide] using
      certificate.h_odd.coprime_two_left.pow_left 2
  calc
    Nat.gcd 108 certificate.h = Nat.gcd (4 * 27) certificate.h := by
      norm_num
    _ = Nat.gcd 27 certificate.h := h4.gcd_mul_left_cancel 27

private theorem outer41RootE (j : Nat) :
    (outer41RootLocalLink j).e = if j % 5 = 4 then 5 else 1 := by
  apply outer41LocalLink_e_eq_capped _ 5 _ (by
    rw [(outer41RootConstants j).1, (outer41RootConstants j).2]
    norm_num)
  exact outer41RootCap j

private theorem outer41E37 (j : Nat) :
    (outer41LocalLink37 j).e = if j % 3 = 0 then 3 else 1 := by
  apply outer41LocalLink_e_eq_capped _ 3 _ (by
    rw [(outer41Constants37 j).1, (outer41Constants37 j).2]
    norm_num)
  exact outer41Cap37 j

private theorem outer41E25 (j : Nat) :
    (outer41LocalLink25 j).e =
      if j % 27 = 25 then 27
      else if j % 9 = 7 then 9
      else if j % 9 = 1 ∨ j % 9 = 4 then 3
      else 1 := by
  apply outer41LocalLink_e_eq_capped _ 108 _ (by
    rw [(outer41Constants25 j).1, (outer41Constants25 j).2]
    split <;> norm_num)
  rw [outer41Gcd108_eq_gcd27]
  exact outer41Cap25 j

private theorem outer41E11 (j : Nat) :
    (outer41LocalLink11 j).e =
      if j % 9 = 8 then 27
      else if j % 3 = 2 then 9
      else if j % 3 = 1 then 3
      else 1 := by
  apply outer41LocalLink_e_eq_capped _ 108 _ (by
    rw [(outer41Constants11 j).1, (outer41Constants11 j).2]
    norm_num
  )
  rw [outer41Gcd108_eq_gcd27]
  exact outer41Cap11 j

private theorem outer41JacobiNat_mod (a modulus : Nat) :
    jacobiSym (a : Int) modulus =
      jacobiSym (a % modulus : Nat) modulus := by
  rw [jacobiSym.mod_left]
  norm_num

private theorem outer41JacobiNat_mod_of_dvd
    (a modulus precision : Nat) (hmodulus : modulus ∣ precision) :
    jacobiSym (a : Int) modulus =
      jacobiSym (a % precision : Nat) modulus := by
  apply jacobiSym.mod_left'
  norm_num
  exact_mod_cast
    (Nat.mod_mod_of_dvd a hmodulus).symm

set_option maxHeartbeats 1000000 in
private theorem outer41RootCorrection (j : Nat) :
    jacobiSym (outer41Alpha j : Int) (outer41RootLocalLink j).e *
      jacobiSym (outer41P37 j : Int) (outer41RootLocalLink j).e = 1 := by
  by_cases hj : j % 5 = 4
  · have hAlpha := outer41HornerNat_mod j 5 outer41AlphaCoeffs
    have hP37 := outer41HornerNat_mod j 5 outer41P37Coeffs
    change outer41Alpha j % 5 = _ at hAlpha
    change outer41P37 j % 5 = _ at hP37
    norm_num [outer41AlphaCoeffs,
      outer41P37Coeffs, outer41HornerNat, hj] at hAlpha hP37
    rw [outer41RootE, if_pos hj,
      outer41JacobiNat_mod (outer41Alpha j) 5,
      outer41JacobiNat_mod (outer41P37 j) 5, hAlpha, hP37]
    norm_num
  · rw [outer41RootE, if_neg hj]
    simp only [jacobiSym.one_right, mul_one]

set_option maxHeartbeats 1000000 in
private theorem outer41Correction37 (j : Nat) :
    jacobiSym (outer41P37 j : Int) (outer41LocalLink37 j).e *
      jacobiSym (outer41P35 j : Int) (outer41LocalLink37 j).e = 1 := by
  by_cases hj : j % 3 = 0
  · have hP37 := outer41HornerNat_mod j 3 outer41P37Coeffs
    have hP35 := outer41HornerNat_mod j 3 outer41P35Coeffs
    change outer41P37 j % 3 = _ at hP37
    change outer41P35 j % 3 = _ at hP35
    norm_num [outer41P37Coeffs,
      outer41P35Coeffs, outer41HornerNat, hj] at hP37 hP35
    rw [outer41E37, if_pos hj,
      outer41JacobiNat_mod (outer41P37 j) 3,
      outer41JacobiNat_mod (outer41P35 j) 3, hP37, hP35]
    norm_num
  · rw [outer41E37, if_neg hj]
    simp only [jacobiSym.one_right, mul_one]

set_option maxHeartbeats 3000000 in
private theorem outer41Correction11 (j : Nat) :
    jacobiSym (outer41P11 j : Int) (outer41LocalLink11 j).e *
      jacobiSym (outer41P9 j : Int) (outer41LocalLink11 j).e = 1 := by
  have hP11 := outer41HornerNat_mod j 27 outer41P11Coeffs
  have hP9 := outer41HornerNat_mod j 27 outer41P9Coeffs
  change outer41P11 j % 27 = _ at hP11
  change outer41P9 j % 27 = _ at hP9
  have hjmod9 : j % 9 = (j % 27) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 27)).symm
  have hjmod3 : j % 3 = (j % 27) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 27)).symm
  have he : (outer41LocalLink11 j).e ∣ 27 := by
    rw [outer41E11]
    by_cases h9 : j % 9 = 8
    · simp [h9]
    · rw [if_neg h9]
      by_cases h2 : j % 3 = 2
      · simp [h2]
      · rw [if_neg h2]
        by_cases h1 : j % 3 = 1 <;> simp [h1]
  have hj : j % 27 < 27 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 27 <;>
    norm_num [outer41P11Coeffs, outer41P9Coeffs,
      outer41HornerNat] at hP11 hP9
  all_goals change outer41P11 j % 27 = _ at hP11
  all_goals change outer41P9 j % 27 = _ at hP9
  all_goals norm_num at hjmod9 hjmod3
  all_goals rw [
    outer41JacobiNat_mod_of_dvd (outer41P11 j)
      (outer41LocalLink11 j).e 27 he,
    outer41JacobiNat_mod_of_dvd (outer41P9 j)
      (outer41LocalLink11 j).e 27 he,
    hP11, hP9, outer41E11 j]
  all_goals norm_num [hjmod9, hjmod3]

set_option maxHeartbeats 3000000 in
private theorem outer41RawCorrection25 (j : Nat) :
    jacobiSym (outer41P25 j : Int) (outer41LocalLink25 j).e *
      jacobiSym (outer41P23 j : Int) (outer41LocalLink25 j).e =
        if j % 27 = 25 then -1
        else if j % 9 = 1 ∨ j % 9 = 4 then -1
        else 1 := by
  have hP25 := outer41HornerNat_mod j 27 outer41P25Coeffs
  have hP23 := outer41HornerNat_mod j 27 outer41P23Coeffs
  change outer41P25 j % 27 = _ at hP25
  change outer41P23 j % 27 = _ at hP23
  have hjmod9 : j % 9 = (j % 27) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 27)).symm
  have he : (outer41LocalLink25 j).e ∣ 27 := by
    rw [outer41E25]
    by_cases h27 : j % 27 = 25
    · simp [h27]
    · rw [if_neg h27]
      by_cases h9 : j % 9 = 7
      · simp [h9]
      · rw [if_neg h9]
        by_cases h3 : j % 9 = 1 ∨ j % 9 = 4 <;> simp [h3]
  have hj : j % 27 < 27 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 27 <;>
    norm_num [outer41P25Coeffs, outer41P23Coeffs,
      outer41HornerNat] at hP25 hP23
  all_goals change outer41P25 j % 27 = _ at hP25
  all_goals change outer41P23 j % 27 = _ at hP23
  all_goals norm_num at hjmod9
  all_goals rw [
    outer41JacobiNat_mod_of_dvd (outer41P25 j)
      (outer41LocalLink25 j).e 27 he,
    outer41JacobiNat_mod_of_dvd (outer41P23 j)
      (outer41LocalLink25 j).e 27 he,
    hP25, hP23, outer41E25 j]
  all_goals norm_num [hcase, hjmod9]

private theorem outer41Factor13PrimaryNeutral (j : Nat) :
    jacobiSym (outer41P23 j : Int) (outer41LocalLink25 j).e =
      jacobiSym (outer41ReducedP23 j : Int) (outer41LocalLink25 j).e := by
  let factor := if j % 13 = 12 then 13 else 1
  have hfactor : outer41P23 j = factor * outer41ReducedP23 j := by
    exact outer41P23_reduction j
  have hfactorSymbol :
      jacobiSym (factor : Int) (outer41LocalLink25 j).e = 1 := by
    by_cases h13 : j % 13 = 12
    · simp only [factor, if_pos h13, Nat.cast_ofNat]
      rw [outer41E25]
      by_cases h27 : j % 27 = 25
      · norm_num [h27]
      · rw [if_neg h27]
        by_cases h9 : j % 9 = 7
        · norm_num [h9]
        · rw [if_neg h9]
          by_cases h3 : j % 9 = 1 ∨ j % 9 = 4 <;> norm_num [h3]
    · simp [factor, h13]
  calc
    jacobiSym (outer41P23 j : Int) (outer41LocalLink25 j).e =
        jacobiSym ((factor * outer41ReducedP23 j : Nat) : Int)
          (outer41LocalLink25 j).e := by rw [hfactor]
    _ = jacobiSym (factor : Int) (outer41LocalLink25 j).e *
        jacobiSym (outer41ReducedP23 j : Int)
          (outer41LocalLink25 j).e := by
      rw [Nat.cast_mul, jacobiSym.mul_left]
    _ = _ := by rw [hfactorSymbol, one_mul]

private theorem outer41Correction25 (j : Nat) :
    jacobiSym (outer41P25 j : Int) (outer41LocalLink25 j).e *
      jacobiSym (outer41ReducedP23 j : Int) (outer41LocalLink25 j).e =
        if j % 27 = 25 then -1
        else if j % 9 = 1 ∨ j % 9 = 4 then -1
        else 1 := by
  rw [← outer41Factor13PrimaryNeutral j]
  exact outer41RawCorrection25 j

set_option maxHeartbeats 1000000 in
private theorem outer41Factor13OffClassSymbol
    (j : Nat) (hoff : j % 13 ≠ 12) :
    jacobiSym (j + 1 : Nat) 13 =
      if j % 13 = 1 ∨ j % 13 = 4 ∨ j % 13 = 5 ∨
          j % 13 = 6 ∨ j % 13 = 7 ∨ j % 13 = 10
      then -1 else 1 := by
  rw [outer41JacobiNat_mod]
  have hj : j % 13 < 13 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 13 <;>
    rw [Nat.add_mod, hcase] <;>
    all_goals norm_num at *

private theorem outer41E3 (j : Nat) :
    (outer41LocalLink3 j).e = 1 := by
  have hh : (outer41LocalLink3 j).h = 1 := by
    rw [(outer41LocalLink3 j).h_eq_gcd]
    simp [outer41Q1, outer41Q1Coeffs, outer41HornerNat]
  have heh : (outer41LocalLink3 j).e ∣ (outer41LocalLink3 j).h := by
    use (outer41LocalLink3 j).h0
    exact (outer41LocalLink3 j).h_factor
  rw [hh] at heh
  exact Nat.eq_one_of_dvd_one heh

private theorem outer41RootE_mod25 (j : Nat) :
    (outer41RootLocalLink j).e =
      if j % 25 = 4 ∨ j % 25 = 9 ∨ j % 25 = 14 ∨
          j % 25 = 19 ∨ j % 25 = 24
      then 5 else 1 := by
  rw [outer41RootE]
  have hmod : j % 5 = (j % 25) % 5 :=
    (Nat.mod_mod_of_dvd j (by decide : 5 ∣ 25)).symm
  rw [hmod]
  have hj : j % 25 < 25 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 25 <;> norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass35 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink35 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink35 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨3, 5, 32459, 13303, ?_, ?_⟩ <;>
    simp only [outer41LocalLink35,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass33 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink33 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink33 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨1, 1, 125403, 187337, ?_, ?_⟩ <;>
    simp only [outer41LocalLink33,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass31 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink31 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink31 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨7, 3, 97415, 3083093, ?_, ?_⟩ <;>
    simp only [outer41LocalLink31,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass29 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink29 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink29 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨9, 2, 1057653, 180451373, ?_, ?_⟩ <;>
    simp only [outer41LocalLink29,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass27 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink27 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink27 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨9, 9, 9367617, 405490661, ?_, ?_⟩ <;>
    simp only [outer41LocalLink27,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass21 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink21 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink21 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨3, 4, 50386908701, 1490611299, ?_, ?_⟩ <;>
    simp only [outer41LocalLink21,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass19 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink19 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink19 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨4, 3, 227750419, 856244269, ?_, ?_⟩ <;>
    simp only [outer41LocalLink19,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass17 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink17 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink17 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨2, 2, 2731930457, 85013175, ?_, ?_⟩ <;>
    simp only [outer41LocalLink17,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass15 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink15 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink15 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨3, 6, 76091453, 69075081, ?_, ?_⟩ <;>
    simp only [outer41LocalLink15,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass13 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink13 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink13 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨8, 2, 9637247, 100487303, ?_, ?_⟩ <;>
    simp only [outer41LocalLink13,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass9 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink9 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink9 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨2, 2, 3200983, 1580391, ?_, ?_⟩ <;>
    simp only [outer41LocalLink9,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass7 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink7 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink7 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨2, 5, 2511089, 137785, ?_, ?_⟩ <;>
    simp only [outer41LocalLink7,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 2000000 in
private theorem outer41Squareclass5 (j : Nat) :
    ∃ u v a b : Nat,
      (outer41LocalLink5 j).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLink5 j).Delta.natAbs = 2 ^ v * b ^ 2 := by
  refine ⟨2, 4, 226269, 7841, ?_, ?_⟩ <;>
    simp only [outer41LocalLink5,
      outer41LocalLinkCertificate_of_endpoint] <;>
    norm_num

set_option maxHeartbeats 4000000 in
private theorem outer41OrdinarySquareclassNeutral
    (j : Nat) (position : Fin 18)
    (hposition : position.1 ∈ [1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 14, 15, 16]) :
    ∃ u v a b : Nat,
      (outer41LocalLinks j position).t.natAbs = 2 ^ u * a ^ 2 ∧
      (outer41LocalLinks j position).Delta.natAbs = 2 ^ v * b ^ 2 := by
  rcases position with ⟨position, hpositionBound⟩
  interval_cases position
  · simp at hposition
  · simpa [outer41LocalLinks] using outer41Squareclass35 j
  · simpa [outer41LocalLinks] using outer41Squareclass33 j
  · simpa [outer41LocalLinks] using outer41Squareclass31 j
  · simpa [outer41LocalLinks] using outer41Squareclass29 j
  · simpa [outer41LocalLinks] using outer41Squareclass27 j
  · simp at hposition
  · simp at hposition
  · simpa [outer41LocalLinks] using outer41Squareclass21 j
  · simpa [outer41LocalLinks] using outer41Squareclass19 j
  · simpa [outer41LocalLinks] using outer41Squareclass17 j
  · simpa [outer41LocalLinks] using outer41Squareclass15 j
  · simpa [outer41LocalLinks] using outer41Squareclass13 j
  · simp at hposition
  · simpa [outer41LocalLinks] using outer41Squareclass9 j
  · simpa [outer41LocalLinks] using outer41Squareclass7 j
  · simpa [outer41LocalLinks] using outer41Squareclass5 j
  · simp at hposition

set_option maxHeartbeats 500000 in
/-- The specialization-safe local certificate for every nonnegative fixed-41
parameter.  Issue #81 is responsible for consuming these data to prove link
equalities and compose the telescope. -/
noncomputable def ss41_localCertificate (j : Nat) : Ss41LocalCertificate j := by
  refine
    { P := outer41ChainP j
      Q := outer41ChainQ j
      coefficientIndex := fun position => 37 - 2 * position.1
      coefficientIndex_eq := fun _ => rfl
      links := outer41LocalLinks j
      terminal_P := ?_
      terminal_Q := ?_
      rawP23 := outer41P23 j
      rawQ23 := outer41Q23 j
      reductionFactor23 := if j % 13 = 12 then 13 else 1
      reductionFactor23_eq := rfl
      rawP23_factor := ?_
      rawQ23_factor := ?_
      reduced23_coprime := outer41ReducedCoprime23 j
      rootP := outer41Alpha j
      rootQ := outer41Gamma j
      rootLink := outer41RootLocalLink j
      root_e_mod25 := outer41RootE_mod25 j
      root_correction := outer41RootCorrection j
      link37_e := outer41E37 j
      link37_correction := outer41Correction37 j
      link25_e := outer41E25 j
      link25_correction := outer41Correction25 j
      link11_e := outer41E11 j
      link11_correction := outer41Correction11 j
      factor13_offClassSymbol := outer41Factor13OffClassSymbol j
      terminalLink_e := outer41E3 j
      ordinary_squareclassNeutral := outer41OrdinarySquareclassNeutral j }
  · rfl
  · rfl
  · exact outer41P23_reduction j
  · exact outer41Q23_reduction j

/-! ## Private fixed-41 directed-transfer layer -/

private theorem outer41ExtractOddCross
    {h L : Nat} {r : Int} (w : Nat) (s : Int)
    (hhpos : 0 < h) (hhodd : Odd h) (hLodd : Odd L)
    (hs : s = 1 ∨ s = -1)
    (hcross : (h : Int) * r = s * ((2 ^ w : Nat) : Int) * L) :
    ∃ R : Nat, L = h * R ∧ Odd R ∧
      r = s * ((2 ^ w : Nat) : Int) * R := by
  have hdvdInt : (h : Int) ∣ (((2 ^ w : Nat) * L : Nat) : Int) := by
    rcases hs with rfl | rfl
    · refine ⟨r, ?_⟩
      push_cast
      simpa [mul_assoc] using hcross.symm
    · refine ⟨-r, ?_⟩
      push_cast
      have hpow : (((2 ^ w : Nat) : Int)) = (2 : Int) ^ w := by norm_num
      calc
        ((2 : Int) ^ w) * L = -((h : Int) * r) := by
          rw [hcross, hpow]
          ring
        _ = (h : Int) * -r := by ring
  have hdvd : h ∣ (2 ^ w) * L := by exact_mod_cast hdvdInt
  have hcop : h.Coprime (2 ^ w) := hhodd.coprime_two_right.pow_right w
  have hhL : h ∣ L := hcop.dvd_of_dvd_mul_left hdvd
  refine ⟨L / h, (Nat.mul_div_cancel' hhL).symm, ?_, ?_⟩
  · have hoddProduct : Odd (h * (L / h)) := by
      simpa only [Nat.mul_div_cancel' hhL] using hLodd
    exact Nat.Odd.of_mul_right hoddProduct
  · apply mul_left_cancel₀ (show (h : Int) ≠ 0 by exact_mod_cast hhpos.ne')
    rw [hcross]
    have hfactorInt : (L : Int) = h * (L / h : Nat) := by
      exact_mod_cast (Nat.mul_div_cancel' hhL).symm
    rw [hfactorInt]
    push_cast
    ring

private theorem outer41ExtractOddPrimeCross
    {h L z : Nat} {r : Int} (w c : Nat) (s : Int)
    (hhpos : 0 < h) (hhodd : Odd h) (hLodd : Odd L)
    (hs : s = 1 ∨ s = -1) (hzH : z.Coprime h)
    (hcross : (h : Int) * r =
      s * ((2 ^ w : Nat) : Int) * z ^ c * L) :
    ∃ R : Nat, L = h * R ∧ Odd R ∧
      r = s * ((2 ^ w : Nat) : Int) * z ^ c * R := by
  have hdvdInt :
      (h : Int) ∣ (((2 ^ w * z ^ c) * L : Nat) : Int) := by
    rcases hs with rfl | rfl
    · refine ⟨r, ?_⟩
      push_cast
      simpa [mul_assoc] using hcross.symm
    · refine ⟨-r, ?_⟩
      push_cast
      calc
        (((2 ^ w * z ^ c : Nat) : Int)) * L =
            -((h : Int) * r) := by
              push_cast
              rw [hcross]
              norm_num
        _ = (h : Int) * -r := by ring
  have hdvd : h ∣ (2 ^ w * z ^ c) * L := by exact_mod_cast hdvdInt
  have hcopTwo : h.Coprime (2 ^ w) :=
    hhodd.coprime_two_right.pow_right w
  have hcopPrime : h.Coprime (z ^ c) := hzH.symm.pow_right c
  have hcop : h.Coprime (2 ^ w * z ^ c) :=
    hcopTwo.mul_right hcopPrime
  have hhL : h ∣ L := hcop.dvd_of_dvd_mul_left hdvd
  refine ⟨L / h, (Nat.mul_div_cancel' hhL).symm, ?_, ?_⟩
  · have hoddProduct : Odd (h * (L / h)) := by
      simpa only [Nat.mul_div_cancel' hhL] using hLodd
    exact Nat.Odd.of_mul_right hoddProduct
  · apply mul_left_cancel₀ (show (h : Int) ≠ 0 by exact_mod_cast hhpos.ne')
    rw [hcross]
    have hfactorInt : (L : Int) = h * (L / h : Nat) := by
      exact_mod_cast (Nat.mul_div_cancel' hhL).symm
    rw [hfactorInt]
    push_cast
    ring

private theorem outer41PrimeCoprimeAfterExactExtraction
    {z h h0 : Nat} (hz : z.Prime)
    (hprimary : Nat.gcd (z * z) h = z)
    (hfactor : h = z * h0) : z.Coprime h0 := by
  rw [hz.coprime_iff_not_dvd]
  intro hzH0
  have hzzH : z * z ∣ h := by
    obtain ⟨a, rfl⟩ := hzH0
    rw [hfactor]
    exact ⟨a, by ring⟩
  have hgcd : Nat.gcd (z * z) h = z * z :=
    Nat.gcd_eq_left_iff_dvd.mpr hzzH
  rw [hprimary] at hgcd
  have hzTwo := hz.two_le
  nlinarith

private theorem outer41OrdinaryCrossProduct
    {Q0 q0 h R L a b : Nat} {r t Delta : Int}
    (w u v : Nat) (s sigma : Int)
    (hhpos : 0 < h) (hRpos : 0 < R)
    (hQ0odd : Odd Q0) (hq0odd : Odd q0) (hRodd : Odd R)
    (hLfactor : L = h * R)
    (hrfactor : r = s * (2 : Int) ^ w * R)
    (htfactor : t = ((2 ^ u * a ^ 2 : Nat) : Int))
    (hDeltafactor : Delta = sigma * (2 : Int) ^ v * b ^ 2)
    (haL : a.Coprime L) (hbL : b.Coprime L)
    (hQ0R : Q0.Coprime R)
    (hendpoint : Int.ModEq R
      ((q0 : Int) * t) ((Q0 : Int) * Delta)) :
    jacobiSym t h * jacobiSym Delta h *
        jacobiSym (-r) Q0 * jacobiSym r q0 =
      jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        qrSign Q0 R * qrSign q0 R *
        jacobiSym 2 L ^ (u + v) * jacobiSym sigma L := by
  have hhne : h ≠ 0 := hhpos.ne'
  have hRne : R ≠ 0 := hRpos.ne'
  have hRdvdL : R ∣ L := by
    use h
    rw [hLfactor]
    ring
  have haR : a.Coprime R := haL.of_dvd_right hRdvdL
  have htwoR : (2 : Nat).Coprime R := hRodd.coprime_two_right.symm
  have htRnat : (2 ^ u * a ^ 2).Coprime R :=
    (htwoR.pow_left u).mul_left (haR.pow_left 2)
  have htR : Int.gcd t R = 1 := by
    rw [htfactor, Int.gcd_natCast_natCast]
    exact htRnat.gcd_eq_one
  have hQ0RInt : Int.gcd (Q0 : Int) R = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hQ0R.gcd_eq_one
  have hendpointSymbols :
      jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R =
        jacobiSym t R * jacobiSym Delta R := by
    have hmod := jacobiSym.mod_left' hendpoint.eq
    rw [jacobiSym.mul_left, jacobiSym.mul_left] at hmod
    have htSquare := jacobiSym.sq_one htR
    have hQSquare := jacobiSym.sq_one hQ0RInt
    calc
      jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R =
          jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R *
            jacobiSym t R ^ 2 := by rw [htSquare, mul_one]
      _ = jacobiSym (Q0 : Int) R * jacobiSym t R *
          (jacobiSym (q0 : Int) R * jacobiSym t R) := by ring
      _ = jacobiSym (Q0 : Int) R * jacobiSym t R *
          (jacobiSym (Q0 : Int) R * jacobiSym Delta R) := by rw [hmod]
      _ = jacobiSym (Q0 : Int) R ^ 2 *
          (jacobiSym t R * jacobiSym Delta R) := by ring
      _ = _ := by rw [hQSquare, one_mul]
  have hminusR :
      jacobiSym (-r) Q0 =
        jacobiSym (-s) Q0 * jacobiSym 2 Q0 ^ w *
          jacobiSym (R : Int) Q0 := by
    calc
      jacobiSym (-r) Q0 =
          jacobiSym ((-s) * (2 : Int) ^ w * R) Q0 := by
            congr 1
            rw [hrfactor]
            ring
      _ = jacobiSym (-s) Q0 * jacobiSym ((2 : Int) ^ w) Q0 *
          jacobiSym (R : Int) Q0 := by
            rw [jacobiSym.mul_left, jacobiSym.mul_left]
      _ = _ := by rw [jacobiSym.pow_left]
  have hplusR :
      jacobiSym r q0 =
        jacobiSym s q0 * jacobiSym 2 q0 ^ w *
          jacobiSym (R : Int) q0 := by
    calc
      jacobiSym r q0 =
          jacobiSym (s * (2 : Int) ^ w * R) q0 := by rw [hrfactor]
      _ = jacobiSym s q0 * jacobiSym ((2 : Int) ^ w) q0 *
          jacobiSym (R : Int) q0 := by
            rw [jacobiSym.mul_left, jacobiSym.mul_left]
      _ = _ := by rw [jacobiSym.pow_left]
  have htCombine :
      jacobiSym t h * jacobiSym t R = jacobiSym t L := by
    rw [hLfactor, jacobiSym.mul_right' t hhne hRne]
  have hDeltaCombine :
      jacobiSym Delta h * jacobiSym Delta R = jacobiSym Delta L := by
    rw [hLfactor, jacobiSym.mul_right' Delta hhne hRne]
  have haLInt : Int.gcd (a : Int) L = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact haL.gcd_eq_one
  have hbLInt : Int.gcd (b : Int) L = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hbL.gcd_eq_one
  have htSymbol : jacobiSym t L = jacobiSym 2 L ^ u := by
    rw [htfactor]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left,
      jacobiSym.sq_one' haLInt, mul_one]
  have hDeltaSymbol :
      jacobiSym Delta L = jacobiSym sigma L * jacobiSym 2 L ^ v := by
    rw [hDeltafactor, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.pow_left, jacobiSym.sq_one' hbLInt, mul_one]
  rw [hminusR, hplusR,
    jacobiSym.quadratic_reciprocity' hRodd hQ0odd,
    jacobiSym.quadratic_reciprocity' hRodd hq0odd]
  calc
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        qrSign Q0 R * qrSign q0 R *
        (jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R) *
        (jacobiSym t h * jacobiSym Delta h) := by ring
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        qrSign Q0 R * qrSign q0 R *
        (jacobiSym t R * jacobiSym Delta R) *
        (jacobiSym t h * jacobiSym Delta h) := by
          rw [hendpointSymbols]
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        qrSign Q0 R * qrSign q0 R *
        ((jacobiSym t h * jacobiSym t R) *
          (jacobiSym Delta h * jacobiSym Delta R)) := by ring
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        qrSign Q0 R * qrSign q0 R *
        (jacobiSym t L * jacobiSym Delta L) := by
          rw [htCombine, hDeltaCombine]
    _ = _ := by
      rw [htSymbol, hDeltaSymbol, pow_add]
      ring

private theorem outer41PrimeExceptionalCrossProduct
    {Q0 q0 h R L a b z : Nat} {r t Delta : Int}
    (w u v zt zd c : Nat) (s sigma : Int)
    (hhpos : 0 < h) (hRpos : 0 < R)
    (hQ0odd : Odd Q0) (hq0odd : Odd q0) (hRodd : Odd R)
    (hLfactor : L = h * R)
    (hrfactor : r = s * (2 : Int) ^ w * z ^ c * R)
    (htfactor : t = (((2 ^ u * z ^ zt * a ^ 2 : Nat)) : Int))
    (hDeltafactor : Delta = sigma * (2 : Int) ^ v * z ^ zd * b ^ 2)
    (haL : a.Coprime L) (hbL : b.Coprime L)
    (htR : Int.gcd t R = 1) (hQ0R : Q0.Coprime R)
    (hendpoint : Int.ModEq R ((q0 : Int) * t) ((Q0 : Int) * Delta)) :
    jacobiSym t h * jacobiSym Delta h *
        jacobiSym (-r) Q0 * jacobiSym r q0 =
      jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        jacobiSym (z : Int) Q0 ^ c * jacobiSym (z : Int) q0 ^ c *
        qrSign Q0 R * qrSign q0 R *
        jacobiSym 2 L ^ (u + v) * jacobiSym (z : Int) L ^ (zt + zd) *
        jacobiSym sigma L := by
  have hhne : h ≠ 0 := hhpos.ne'
  have hRne : R ≠ 0 := hRpos.ne'
  have hRdvdL : R ∣ L := by
    use h
    rw [hLfactor]
    ring
  have haR : a.Coprime R := haL.of_dvd_right hRdvdL
  have hQ0RInt : Int.gcd (Q0 : Int) R = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hQ0R.gcd_eq_one
  have hendpointSymbols :
      jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R =
        jacobiSym t R * jacobiSym Delta R := by
    have hmod := jacobiSym.mod_left' hendpoint.eq
    rw [jacobiSym.mul_left, jacobiSym.mul_left] at hmod
    have htSquare := jacobiSym.sq_one htR
    have hQSquare := jacobiSym.sq_one hQ0RInt
    calc
      jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R =
          jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R *
            jacobiSym t R ^ 2 := by rw [htSquare, mul_one]
      _ = jacobiSym (Q0 : Int) R * jacobiSym t R *
          (jacobiSym (q0 : Int) R * jacobiSym t R) := by ring
      _ = jacobiSym (Q0 : Int) R * jacobiSym t R *
          (jacobiSym (Q0 : Int) R * jacobiSym Delta R) := by rw [hmod]
      _ = jacobiSym (Q0 : Int) R ^ 2 *
          (jacobiSym t R * jacobiSym Delta R) := by ring
      _ = _ := by rw [hQSquare, one_mul]
  have hminusR :
      jacobiSym (-r) Q0 =
        jacobiSym (-s) Q0 * jacobiSym 2 Q0 ^ w *
          jacobiSym (z : Int) Q0 ^ c * jacobiSym (R : Int) Q0 := by
    calc
      jacobiSym (-r) Q0 =
          jacobiSym ((-s) * (2 : Int) ^ w * z ^ c * R) Q0 := by
            congr 1
            rw [hrfactor]
            ring
      _ = jacobiSym (-s) Q0 * jacobiSym ((2 : Int) ^ w) Q0 *
          jacobiSym ((z : Int) ^ c) Q0 * jacobiSym (R : Int) Q0 := by
            repeat' rw [jacobiSym.mul_left]
      _ = _ := by rw [jacobiSym.pow_left, jacobiSym.pow_left]
  have hplusR :
      jacobiSym r q0 =
        jacobiSym s q0 * jacobiSym 2 q0 ^ w *
          jacobiSym (z : Int) q0 ^ c * jacobiSym (R : Int) q0 := by
    calc
      jacobiSym r q0 =
          jacobiSym (s * (2 : Int) ^ w * z ^ c * R) q0 := by rw [hrfactor]
      _ = jacobiSym s q0 * jacobiSym ((2 : Int) ^ w) q0 *
          jacobiSym ((z : Int) ^ c) q0 * jacobiSym (R : Int) q0 := by
            repeat' rw [jacobiSym.mul_left]
      _ = _ := by rw [jacobiSym.pow_left, jacobiSym.pow_left]
  have htCombine : jacobiSym t h * jacobiSym t R = jacobiSym t L := by
    rw [hLfactor, jacobiSym.mul_right' t hhne hRne]
  have hDeltaCombine :
      jacobiSym Delta h * jacobiSym Delta R = jacobiSym Delta L := by
    rw [hLfactor, jacobiSym.mul_right' Delta hhne hRne]
  have haLInt : Int.gcd (a : Int) L = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact haL.gcd_eq_one
  have hbLInt : Int.gcd (b : Int) L = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hbL.gcd_eq_one
  have htSymbol :
      jacobiSym t L = jacobiSym 2 L ^ u * jacobiSym (z : Int) L ^ zt := by
    rw [htfactor]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.pow_left, jacobiSym.pow_left,
      jacobiSym.sq_one' haLInt, mul_one]
  have hDeltaSymbol :
      jacobiSym Delta L = jacobiSym sigma L * jacobiSym 2 L ^ v *
        jacobiSym (z : Int) L ^ zd := by
    rw [hDeltafactor]
    repeat' rw [jacobiSym.mul_left]
    rw [jacobiSym.pow_left, jacobiSym.pow_left,
      jacobiSym.sq_one' hbLInt, mul_one]
  rw [hminusR, hplusR,
    jacobiSym.quadratic_reciprocity' hRodd hQ0odd,
    jacobiSym.quadratic_reciprocity' hRodd hq0odd]
  calc
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        jacobiSym (z : Int) Q0 ^ c * jacobiSym (z : Int) q0 ^ c *
        qrSign Q0 R * qrSign q0 R *
        (jacobiSym (Q0 : Int) R * jacobiSym (q0 : Int) R) *
        (jacobiSym t h * jacobiSym Delta h) := by ring
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        jacobiSym (z : Int) Q0 ^ c * jacobiSym (z : Int) q0 ^ c *
        qrSign Q0 R * qrSign q0 R *
        (jacobiSym t R * jacobiSym Delta R) *
        (jacobiSym t h * jacobiSym Delta h) := by rw [hendpointSymbols]
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        jacobiSym (z : Int) Q0 ^ c * jacobiSym (z : Int) q0 ^ c *
        qrSign Q0 R * qrSign q0 R *
        ((jacobiSym t h * jacobiSym t R) *
          (jacobiSym Delta h * jacobiSym Delta R)) := by ring
    _ = jacobiSym (-s) Q0 * jacobiSym s q0 *
        jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
        jacobiSym (z : Int) Q0 ^ c * jacobiSym (z : Int) q0 ^ c *
        qrSign Q0 R * qrSign q0 R *
        (jacobiSym t L * jacobiSym Delta L) := by
          rw [htCombine, hDeltaCombine]
    _ = _ := by
      rw [htSymbol, hDeltaSymbol, pow_add, pow_add]
      ring

private theorem outer41LocalLinkDualEndpoint
    {P Q p q : Nat} (certificate : Ss41LocalLinkCertificate P Q p q)
    (A B : Int)
    (hsupport : A * Q + B * P = certificate.t)
    (hdeterminant : A * q + B * p = certificate.Delta) :
    Int.ModEq certificate.r
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta) := by
  have hhne : (certificate.h : Int) ≠ 0 := by
    exact_mod_cast certificate.h_pos.ne'
  have hQfac : (Q : Int) = certificate.h * certificate.Q0 := by
    exact_mod_cast certificate.Q_factor
  have hqfac : (q : Int) = certificate.h * certificate.q0 := by
    exact_mod_cast certificate.q_factor
  have hcrossRed : certificate.r =
      (p : Int) * certificate.Q0 - certificate.q0 * P := by
    apply mul_left_cancel₀ hhne
    calc
      (certificate.h : Int) * certificate.r =
          (p : Int) * Q - (q : Int) * P := certificate.cross
      _ = (certificate.h : Int) *
          ((p : Int) * certificate.Q0 - certificate.q0 * P) := by
            rw [hQfac, hqfac]
            ring
  rw [Int.modEq_iff_dvd]
  use B
  calc
    (certificate.Q0 : Int) * certificate.Delta -
        certificate.q0 * certificate.t =
        certificate.Q0 * (A * q + B * p) -
          certificate.q0 * (A * Q + B * P) := by
            rw [hsupport, hdeterminant]
    _ = B * certificate.r := by
      rw [hQfac, hqfac, hcrossRed]
      ring
    _ = certificate.r * B := by ring

private theorem outer41LocalLinkCrossReduced
    {P Q p q : Nat} (certificate : Ss41LocalLinkCertificate P Q p q) :
    certificate.r =
      (p : Int) * certificate.Q0 - certificate.q0 * P := by
  have hhne : (certificate.h : Int) ≠ 0 := by
    exact_mod_cast certificate.h_pos.ne'
  have hQfac : (Q : Int) = certificate.h * certificate.Q0 := by
    exact_mod_cast certificate.Q_factor
  have hqfac : (q : Int) = certificate.h * certificate.q0 := by
    exact_mod_cast certificate.q_factor
  apply mul_left_cancel₀ hhne
  calc
    (certificate.h : Int) * certificate.r =
        (p : Int) * Q - (q : Int) * P := certificate.cross
    _ = (certificate.h : Int) *
        ((p : Int) * certificate.Q0 - certificate.q0 * P) := by
          rw [hQfac, hqfac]
          ring

private theorem outer41LocalLink_r_coprime_Q0
    {P Q p q : Nat} (certificate : Ss41LocalLinkCertificate P Q p q)
    (hPQ : P.Coprime Q) :
    Int.gcd certificate.r certificate.Q0 = 1 := by
  have hQ0dvdQ : certificate.Q0 ∣ Q := by
    use certificate.h
    simpa [mul_comm] using certificate.Q_factor
  have hPQ0 : P.Coprime certificate.Q0 :=
    hPQ.of_dvd_right hQ0dvdQ
  have hnegative := outer41IntGcd_sub_mul_eq_one
    (P := p) (p := certificate.q0) (Q0 := P)
    (q0 := certificate.Q0)
    certificate.Q0_coprime_q0.symm hPQ0
  rw [show (certificate.q0 : Int) * P -
      (certificate.Q0 : Int) * p = -certificate.r by
        rw [outer41LocalLinkCrossReduced certificate]
        ring] at hnegative
  simpa [Int.gcd_def] using hnegative

private theorem outer41FactorCoprime
    {r : Int} {R n w : Nat} {s : Int}
    (hs : s = 1 ∨ s = -1)
    (hrfactor : r = s * (2 : Int) ^ w * R)
    (hrn : Int.gcd r n = 1) : R.Coprime n := by
  have hRdvd : R ∣ r.natAbs := by
    rcases hs with rfl | rfl
    · rw [hrfactor]
      simp only [one_mul, Int.natAbs_mul, Int.natAbs_pow,
        Int.natAbs_natCast]
      exact dvd_mul_left R (2 ^ w)
    · rw [hrfactor]
      simp only [neg_mul, one_mul, Int.natAbs_neg, Int.natAbs_mul,
        Int.natAbs_pow, Int.natAbs_natCast]
      exact dvd_mul_left R (2 ^ w)
  apply Nat.Coprime.of_dvd_left hRdvd
  rw [Nat.coprime_iff_gcd_eq_one]
  simpa [Int.gcd_def] using hrn

private theorem outer41ReducedFactorsModEq
    {Q q h Q0 q0 modulus : Nat}
    (hQfactor : Q = h * Q0) (hqfactor : q = h * q0)
    (hcoprime : Nat.gcd modulus h = 1)
    (hmod : Q % modulus = q % modulus) :
    Q0 % modulus = q0 % modulus := by
  have hmodEq : Nat.ModEq modulus Q q := hmod
  rw [hQfactor, hqfactor] at hmodEq
  exact hmodEq.cancel_left_of_coprime hcoprime

private theorem outer41JacobiTwoOfModEight
    {n : Nat} (hn : Odd n) :
    jacobiSym 2 n =
      if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  rw [jacobiSym.at_two hn, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [Nat.odd_iff.mp hn]

private theorem outer41JacobiNegOneOfModFour
    {n : Nat} (hn : Odd n) :
    jacobiSym (-1 : Int) n = if n % 4 = 1 then 1 else -1 := by
  rw [jacobiSym.at_neg_one hn, ZMod.χ₄_nat_eq_if_mod_four]
  simp [Nat.odd_iff.mp hn]

private theorem outer41QrSignOfModFour
    {m n : Nat} (hm : Odd m) (hn : Odd n) :
    qrSign m n = if m % 4 = 3 ∧ n % 4 = 3 then -1 else 1 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm1 | hm3
  · rw [outer41_qrSign_left_one hm1]
    simp [hm1]
  · rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with hn1 | hn3
    · rw [outer41_qrSign_right_one hm hn hn1]
      simp [hm3, hn1]
    · rw [outer41_qrSign_both_three hm3 hn3]
      simp [hm3, hn3]

private theorem outer41JacobiThreeOfModTwelve
    {n : Nat} (hn : Odd n) (hthree : (3 : Nat).Coprime n) :
    jacobiSym (3 : Int) n =
      if n % 12 = 1 ∨ n % 12 = 11 then 1 else -1 := by
  have hnmod3 : n % 3 = (n % 12) % 3 :=
    (Nat.mod_mod_of_dvd n (by decide : 3 ∣ 12)).symm
  have hnmod4 : n % 4 = (n % 12) % 4 :=
    (Nat.mod_mod_of_dvd n (by decide : 4 ∣ 12)).symm
  have hnmod2 : n % 2 = (n % 12) % 2 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 12)).symm
  have hnoddmod : n % 2 = 1 := Nat.odd_iff.mp hn
  have hnnot3 : n % 3 ≠ 0 := by
    intro hnzero
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hthree)
      (Nat.dvd_iff_mod_eq_zero.mpr hnzero)
  have hn12 : n % 12 < 12 := Nat.mod_lt _ (by decide)
  change jacobiSym (((3 : Nat) : Int)) n = _
  rw [jacobiSym.quadratic_reciprocity' (by decide : Odd 3) hn,
    outer41QrSignOfModFour hn (by decide : Odd 3),
    outer41JacobiNat_mod n 3]
  interval_cases hcase : n % 12
  all_goals
    norm_num [hcase] at hnmod2 hnmod3 hnmod4
  all_goals try omega
  all_goals rw [hnmod3, hnmod4]
  all_goals norm_num

private theorem outer41HornerNat_map_mod
    (j modulus : Nat) (coefficients : List Nat) :
    outer41HornerNat j coefficients % modulus =
      outer41HornerNat (j % modulus)
        (coefficients.map (· % modulus)) % modulus := by
  induction coefficients with
  | nil => simp [outer41HornerNat]
  | cons a coefficients ih =>
      simp only [outer41HornerNat, List.map_cons]
      simp [Nat.add_mod, Nat.mul_mod, ih]

private theorem outer41HornerNat_append_zeros
    (j : Nat) (coefficients : List Nat) (count : Nat) :
    outer41HornerNat j (coefficients ++ List.replicate count 0) =
      outer41HornerNat j coefficients := by
  induction coefficients with
  | nil =>
      induction count with
      | zero => simp [outer41HornerNat]
      | succ count ih =>
          rw [List.replicate_succ]
          have hzero :
              outer41HornerNat j (List.replicate count 0) = 0 := by
            simpa [outer41HornerNat] using ih
          simp [outer41HornerNat, hzero]
  | cons coefficient coefficients ih =>
      simp [outer41HornerNat, ih]

private theorem outer41Q37Q35ModTwentyFourCoeffs :
    outer41Q37Coeffs.map (· % 24) =
      outer41Q35Coeffs.map (· % 24) ++ List.replicate 2 0 := by
  decide

private theorem outer41Q37Q35ModTwentyFour (j : Nat) :
    outer41Q37 j % 24 = outer41Q35 j % 24 := by
  have h37 := outer41HornerNat_map_mod j 24 outer41Q37Coeffs
  have h35 := outer41HornerNat_map_mod j 24 outer41Q35Coeffs
  rw [outer41Q37Q35ModTwentyFourCoeffs,
    outer41HornerNat_append_zeros] at h37
  simpa [outer41Q37, outer41Q35] using h37.trans h35.symm

private theorem outer41Q37Q35ModNine_of_mod_three_zero
    (j : Nat) (hj : j % 3 = 0) :
    outer41Q37 j % 9 = 6 ∧ outer41Q35 j % 9 = 6 := by
  have h37 := outer41HornerNat_mod j 9 outer41Q37Coeffs
  have h35 := outer41HornerNat_mod j 9 outer41Q35Coeffs
  change outer41Q37 j % 9 = _ at h37
  change outer41Q35 j % 9 = _ at h35
  have hjmod3 : j % 3 = (j % 9) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
  have hjbound : j % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 9 <;>
    norm_num [outer41Q37Coeffs, outer41Q35Coeffs,
      outer41HornerNat] at h37 h35 hjmod3
  all_goals omega

private theorem outer41Q35ModEightCoeffs :
    outer41Q35Coeffs.map (· % 8) =
      [7] ++ List.replicate 34 0 := by
  decide

private theorem outer41Q33ModEightCoeffs :
    outer41Q33Coeffs.map (· % 8) =
      [5] ++ List.replicate 32 0 := by
  decide

private theorem outer41Q31ModEightCoeffs :
    outer41Q31Coeffs.map (· % 8) =
      [5] ++ List.replicate 30 0 := by
  decide

private theorem outer41Q29ModEightCoeffs :
    outer41Q29Coeffs.map (· % 8) =
      [5] ++ List.replicate 28 0 := by
  decide

private theorem outer41Q27ModEightCoeffs :
    outer41Q27Coeffs.map (· % 8) =
      [3] ++ List.replicate 26 0 := by
  decide

private theorem outer41Q25ModEightCoeffs :
    outer41Q25Coeffs.map (· % 8) =
      [5] ++ List.replicate 24 0 := by
  decide

private theorem outer41Q23ModEightCoeffs :
    outer41Q23Coeffs.map (· % 8) =
      [7] ++ List.replicate 22 0 := by
  decide

private theorem outer41Q23QuotientModEightCoeffs :
    outer41Q23QuotientCoeffs.map (· % 8) =
      [3] ++ List.replicate 22 0 := by
  decide

private theorem outer41Q21ModEightCoeffs :
    outer41Q21Coeffs.map (· % 8) =
      [3] ++ List.replicate 20 0 := by
  decide

private theorem outer41Q19ModEightCoeffs :
    outer41Q19Coeffs.map (· % 8) =
      [5, 4] ++ List.replicate 17 0 := by
  decide

private theorem outer41Q17ModEightCoeffs :
    outer41Q17Coeffs.map (· % 8) =
      [7] ++ List.replicate 16 0 := by
  decide

private theorem outer41Q15ModEightCoeffs :
    outer41Q15Coeffs.map (· % 8) =
      [5] ++ List.replicate 14 0 := by
  decide

private theorem outer41Q13ModEightCoeffs :
    outer41Q13Coeffs.map (· % 8) =
      [3] ++ List.replicate 12 0 := by
  decide

private theorem outer41Q11ModEightCoeffs :
    outer41Q11Coeffs.map (· % 8) =
      [3] ++ List.replicate 10 0 := by
  decide

private theorem outer41Q9ModEightCoeffs :
    outer41Q9Coeffs.map (· % 8) =
      [3] ++ List.replicate 8 0 := by
  decide

private theorem outer41Q7ModEightCoeffs :
    outer41Q7Coeffs.map (· % 8) =
      [7] ++ List.replicate 6 0 := by
  decide

private theorem outer41Q5ModEightCoeffs :
    outer41Q5Coeffs.map (· % 8) =
      [7] ++ List.replicate 4 0 := by
  decide

private theorem outer41Q3ModEightCoeffs :
    outer41Q3Coeffs.map (· % 8) =
      [7] ++ List.replicate 2 0 := by
  decide

private theorem outer41OrdinaryLinkTransfer
    {P Q p q R L a b : Nat}
    (certificate : Ss41LocalLinkCertificate P Q p q)
    (w u v : Nat) (s sigma : Int)
    (he : certificate.e = 1)
    (hRpos : 0 < R) (hRodd : Odd R)
    (hLfactor : L = certificate.h * R)
    (hrfactor : certificate.r = s * (2 : Int) ^ w * R)
    (htfactor : certificate.t = ((2 ^ u * a ^ 2 : Nat) : Int))
    (hDeltafactor : certificate.Delta = sigma * (2 : Int) ^ v * b ^ 2)
    (haL : a.Coprime L) (hbL : b.Coprime L)
    (hQ0R : certificate.Q0.Coprime R)
    (hendpoint : Int.ModEq R
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta)) :
    jacobiSym (P : Int) Q =
      qrSign certificate.Q0 certificate.q0 *
        (jacobiSym (-s) certificate.Q0 * jacobiSym s certificate.q0 *
          jacobiSym 2 certificate.Q0 ^ w *
          jacobiSym 2 certificate.q0 ^ w *
          qrSign certificate.Q0 R * qrSign certificate.q0 R *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) *
        jacobiSym (p : Int) q := by
  have hh0 : certificate.h0 = certificate.h := by
    rw [certificate.h_factor, he]
    simp
  have ht0 : certificate.t0 = certificate.t := by
    rw [certificate.t_factor, he]
    simp
  have hDelta0 : certificate.Delta0 = certificate.Delta := by
    rw [certificate.Delta_factor, he]
    simp
  have hcorrection := ss41_endpointFactorCorrection
    certificate.t0 certificate.Delta0
    certificate.e_pos certificate.h0_pos certificate.h_factor
    certificate.p_coprime_h0 certificate.Delta0_coprime_h0
    certificate.endpoint
  have hcorrection' :
      jacobiSym (P : Int) certificate.h *
          jacobiSym (p : Int) certificate.h =
        jacobiSym certificate.t certificate.h *
          jacobiSym certificate.Delta certificate.h := by
    simpa [he, hh0, ht0, hDelta0] using hcorrection
  have hcross := ss41_crossJacobiTransfer certificate.r
    certificate.h_pos certificate.Q0_pos certificate.q0_pos
    certificate.Q0_odd certificate.q0_odd certificate.Q_factor
    certificate.q_factor certificate.p_coprime_h
    certificate.Q0_coprime_q0 certificate.r_coprime_q0 certificate.cross
  have hcrossProduct := outer41OrdinaryCrossProduct w u v s sigma
    certificate.h_pos hRpos certificate.Q0_odd certificate.q0_odd hRodd
    hLfactor hrfactor htfactor hDeltafactor haL hbL hQ0R hendpoint
  rw [hcross]
  calc
    _ = qrSign certificate.Q0 certificate.q0 *
        ((jacobiSym (P : Int) certificate.h *
            jacobiSym (p : Int) certificate.h) *
          jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0) *
        jacobiSym (p : Int) q := by ring
    _ = qrSign certificate.Q0 certificate.q0 *
        ((jacobiSym certificate.t certificate.h *
            jacobiSym certificate.Delta certificate.h) *
          jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0) *
        jacobiSym (p : Int) q := by rw [hcorrection']
    _ = _ := by rw [hcrossProduct]

private theorem outer41FactoredLinkTransfer
    {P Q p q : Nat} (certificate : Ss41LocalLinkCertificate P Q p q) :
    jacobiSym (P : Int) Q =
      qrSign certificate.Q0 certificate.q0 *
        (jacobiSym (P : Int) certificate.e *
          jacobiSym (p : Int) certificate.e) *
        (jacobiSym certificate.t0 certificate.h0 *
          jacobiSym certificate.Delta0 certificate.h0) *
        jacobiSym (-certificate.r) certificate.Q0 *
        jacobiSym certificate.r certificate.q0 *
        jacobiSym (p : Int) q := by
  have hcross := ss41_crossJacobiTransfer certificate.r
    certificate.h_pos certificate.Q0_pos certificate.q0_pos
    certificate.Q0_odd certificate.q0_odd certificate.Q_factor
    certificate.q_factor certificate.p_coprime_h
    certificate.Q0_coprime_q0 certificate.r_coprime_q0 certificate.cross
  have hcorrection := ss41_endpointFactorCorrection
    certificate.t0 certificate.Delta0
    certificate.e_pos certificate.h0_pos certificate.h_factor
    certificate.p_coprime_h0 certificate.Delta0_coprime_h0
    certificate.endpoint
  rw [hcross]
  calc
    _ = qrSign certificate.Q0 certificate.q0 *
        ((jacobiSym (P : Int) certificate.h *
          jacobiSym (p : Int) certificate.h) *
        jacobiSym (-certificate.r) certificate.Q0 *
        jacobiSym certificate.r certificate.q0) *
        jacobiSym (p : Int) q := by ring
    _ = qrSign certificate.Q0 certificate.q0 *
        ((jacobiSym (P : Int) certificate.e *
            jacobiSym (p : Int) certificate.e *
          (jacobiSym certificate.t0 certificate.h0 *
            jacobiSym certificate.Delta0 certificate.h0)) *
        jacobiSym (-certificate.r) certificate.Q0 *
        jacobiSym certificate.r certificate.q0) *
        jacobiSym (p : Int) q := by rw [hcorrection]; ring
    _ = _ := by ring

private def outer41TwoResidueCharacter (n : Nat) : Int :=
  if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1

private def outer41NegOneResidueCharacter (n : Nat) : Int :=
  if n % 4 = 1 then 1 else -1

private def outer41UnitResidueCharacter (s : Int) (n : Nat) : Int :=
  if s = 1 then 1 else outer41NegOneResidueCharacter n

private def outer41QrResidueCharacter (m n : Nat) : Int :=
  if m % 4 = 3 ∧ n % 4 = 3 then -1 else 1

private def outer41OrdinaryActualResidueSign
    (w u v : Nat) (s sigma : Int) (Q0 q0 R L : Nat) : Int :=
  outer41QrResidueCharacter Q0 q0 *
    (outer41UnitResidueCharacter (-s) Q0 *
      outer41UnitResidueCharacter s q0 *
      outer41TwoResidueCharacter Q0 ^ w *
      outer41TwoResidueCharacter q0 ^ w *
      outer41QrResidueCharacter Q0 R *
      outer41QrResidueCharacter q0 R *
      outer41TwoResidueCharacter L ^ (u + v) *
      outer41UnitResidueCharacter sigma L)

private theorem outer41OrdinaryActualResidueSign_modEight
    (w u v : Nat) (s sigma : Int) (Q q R L : Nat) :
    outer41OrdinaryActualResidueSign w u v s sigma Q q R L =
      outer41OrdinaryActualResidueSign w u v s sigma
        (Q % 8) (q % 8) (R % 8) (L % 8) := by
  simp [outer41OrdinaryActualResidueSign,
    outer41QrResidueCharacter, outer41UnitResidueCharacter,
    outer41NegOneResidueCharacter, outer41TwoResidueCharacter,
    Nat.mod_mod_of_dvd]

private theorem outer41JacobiUnitOfModFour
    {s : Int} {n : Nat} (hs : s = 1 ∨ s = -1) (hn : Odd n) :
    jacobiSym s n = outer41UnitResidueCharacter s n := by
  rcases hs with rfl | rfl
  · simp [outer41UnitResidueCharacter]
  · rw [outer41JacobiNegOneOfModFour hn]
    simp [outer41UnitResidueCharacter, outer41NegOneResidueCharacter]

private theorem outer41OrdinaryCharacterAsResidues
    {Q0 q0 R L : Nat} (w u v : Nat) (s sigma : Int)
    (hs : s = 1 ∨ s = -1) (hsigma : sigma = 1 ∨ sigma = -1)
    (hQ0odd : Odd Q0) (hq0odd : Odd q0) (hRodd : Odd R) (hLodd : Odd L) :
    qrSign Q0 q0 *
        (jacobiSym (-s) Q0 * jacobiSym s q0 *
          jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
          qrSign Q0 R * qrSign q0 R *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) =
      outer41OrdinaryActualResidueSign w u v s sigma Q0 q0 R L := by
  have hminusS : -s = 1 ∨ -s = -1 := by
    rcases hs with rfl | rfl <;> simp
  rw [outer41QrSignOfModFour hQ0odd hq0odd,
    outer41JacobiUnitOfModFour hminusS hQ0odd,
    outer41JacobiUnitOfModFour hs hq0odd,
    outer41JacobiTwoOfModEight hQ0odd,
    outer41JacobiTwoOfModEight hq0odd,
    outer41QrSignOfModFour hQ0odd hRodd,
    outer41QrSignOfModFour hq0odd hRodd,
    outer41JacobiTwoOfModEight hLodd,
    outer41JacobiUnitOfModFour hsigma hLodd]
  rfl

private theorem outer41OrdinaryRawCharacter
    {Q q L : Nat} (w u v : Nat) (s sigma : Int)
    (hs : s = 1 ∨ s = -1) (hsigma : sigma = 1 ∨ sigma = -1)
    (hQodd : Odd Q) (hqodd : Odd q) (hLodd : Odd L) :
    qrSign Q q *
        (jacobiSym (-s) Q * jacobiSym s q *
          jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
          qrSign Q L * qrSign q L *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) =
      outer41OrdinaryActualResidueSign w u v s sigma
        (Q % 8) (q % 8) (L % 8) (L % 8) := by
  rw [outer41OrdinaryCharacterAsResidues w u v s sigma hs hsigma
    hQodd hqodd hLodd hLodd]
  exact outer41OrdinaryActualResidueSign_modEight w u v s sigma Q q L L

private def outer41PrimeRawCharacter
    (w u v zt zd c : Nat) (s sigma : Int) (z Q q L : Nat) : Int :=
  qrSign Q q *
    (jacobiSym (-s) Q * jacobiSym s q *
      jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
      jacobiSym (z : Int) Q ^ c * jacobiSym (z : Int) q ^ c *
      qrSign Q L * qrSign q L *
      jacobiSym 2 L ^ (u + v) *
      jacobiSym (z : Int) L ^ (zt + zd) *
      jacobiSym sigma L)

private theorem outer41PrimeRawCharacter_one_zero_zero
    (w u v : Nat) (s sigma : Int) (z Q q L : Nat) :
    outer41PrimeRawCharacter w u v 1 0 0 s sigma z Q q L =
      (qrSign Q q *
        (jacobiSym (-s) Q * jacobiSym s q *
          jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
          qrSign Q L * qrSign q L *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L)) *
        jacobiSym (z : Int) L := by
  simp only [outer41PrimeRawCharacter, pow_zero, pow_one,
    Nat.add_zero, mul_one]
  ring

private theorem outer41QrTripleCommonFactor
    {h a b c : Nat}
    (hh : Odd h) (ha : Odd a) (hb : Odd b) (hc : Odd c) :
    qrSign (h * a) (h * b) *
        qrSign (h * a) (h * c) *
        qrSign (h * b) (h * c) =
      qrSign h h *
        (qrSign a b * qrSign a c * qrSign b c) := by
  letI : NeZero h := ⟨hh.pos.ne'⟩
  letI : NeZero a := ⟨ha.pos.ne'⟩
  letI : NeZero b := ⟨hb.pos.ne'⟩
  letI : NeZero c := ⟨hc.pos.ne'⟩
  rw [qrSign.mul_left h a (h * b),
    qrSign.mul_right h h b, qrSign.mul_right a h b,
    qrSign.mul_left h a (h * c),
    qrSign.mul_right h h c, qrSign.mul_right a h c,
    qrSign.mul_left h b (h * c),
    qrSign.mul_right h h c, qrSign.mul_right b h c,
    qrSign.symm ha hh, qrSign.symm hb hh]
  have hhh := qrSign.sq_eq_one hh hh
  have hha := qrSign.sq_eq_one hh ha
  have hhb := qrSign.sq_eq_one hh hb
  have hhc := qrSign.sq_eq_one hh hc
  calc
    _ = qrSign h h * (qrSign h h ^ 2) *
        (qrSign h a ^ 2) * (qrSign h b ^ 2) *
        (qrSign h c ^ 2) *
        (qrSign a b * qrSign a c * qrSign b c) := by ring
    _ = _ := by rw [hhh, hha, hhb, hhc]; ring

private theorem outer41QrSignSelf
    {h : Nat} (hh : Odd h) :
    qrSign h h = jacobiSym (-1 : Int) h := by
  rw [outer41QrSignOfModFour hh hh,
    outer41JacobiNegOneOfModFour hh]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hh) with h1 | h3
  · simp [h1]
  · simp [h3]

private theorem outer41JacobiUnitPairCommonFactor
    {h : Nat} {s : Int} (hh : Odd h) (hs : s = 1 ∨ s = -1) :
    jacobiSym (-s) h * jacobiSym s h = qrSign h h := by
  calc
    jacobiSym (-s) h * jacobiSym s h =
        jacobiSym ((-s) * s) h := by rw [jacobiSym.mul_left]
    _ = jacobiSym (-1 : Int) h := by
      rcases hs with rfl | rfl <;> norm_num
    _ = qrSign h h := (outer41QrSignSelf hh).symm

private theorem outer41JacobiUnitPairRestore
    {h a b : Nat} {s : Int}
    (hh : Odd h) (ha : Odd a) (hb : Odd b)
    (hs : s = 1 ∨ s = -1) :
    jacobiSym (-s) (h * a) * jacobiSym s (h * b) =
      qrSign h h * (jacobiSym (-s) a * jacobiSym s b) := by
  rw [jacobiSym.mul_right' (-s) hh.pos.ne' ha.pos.ne',
    jacobiSym.mul_right' s hh.pos.ne' hb.pos.ne']
  calc
    (jacobiSym (-s) h * jacobiSym (-s) a) *
        (jacobiSym s h * jacobiSym s b) =
      (jacobiSym (-s) h * jacobiSym s h) *
        (jacobiSym (-s) a * jacobiSym s b) := by ring
    _ = _ := by rw [outer41JacobiUnitPairCommonFactor hh hs]

private theorem outer41JacobiTwoPairRestore
    {h a b : Nat} (w : Nat)
    (hh : Odd h) (ha : Odd a) (hb : Odd b) :
    jacobiSym 2 (h * a) ^ w * jacobiSym 2 (h * b) ^ w =
      jacobiSym 2 a ^ w * jacobiSym 2 b ^ w := by
  rw [jacobiSym.mul_right' 2 hh.pos.ne' ha.pos.ne',
    jacobiSym.mul_right' 2 hh.pos.ne' hb.pos.ne']
  have htwo : Int.gcd (2 : Int) h = 1 := by
    change Int.gcd ((2 : Nat) : Int) (h : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact hh.coprime_two_right.symm.gcd_eq_one
  have hsquare := jacobiSym.sq_one htwo
  calc
    (jacobiSym 2 h * jacobiSym 2 a) ^ w *
        (jacobiSym 2 h * jacobiSym 2 b) ^ w =
      (jacobiSym 2 h * jacobiSym 2 h) ^ w *
        (jacobiSym 2 a ^ w * jacobiSym 2 b ^ w) := by
          rw [mul_pow, mul_pow, mul_pow]
          ring
    _ = _ := by rw [← pow_two, hsquare, one_pow, one_mul]

private theorem outer41JacobiPrimePairRestore
    {h a b z : Nat} (c : Nat)
    (hh : Odd h) (ha : Odd a) (hb : Odd b)
    (hzH : z.Coprime h) :
    jacobiSym (z : Int) (h * a) ^ c *
        jacobiSym (z : Int) (h * b) ^ c =
      jacobiSym (z : Int) a ^ c * jacobiSym (z : Int) b ^ c := by
  rw [jacobiSym.mul_right' (z : Int) hh.pos.ne' ha.pos.ne',
    jacobiSym.mul_right' (z : Int) hh.pos.ne' hb.pos.ne']
  have hzHInt : Int.gcd (z : Int) h = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hzH.gcd_eq_one
  have hsquare := jacobiSym.sq_one hzHInt
  calc
    (jacobiSym (z : Int) h * jacobiSym (z : Int) a) ^ c *
        (jacobiSym (z : Int) h * jacobiSym (z : Int) b) ^ c =
      (jacobiSym (z : Int) h * jacobiSym (z : Int) h) ^ c *
        (jacobiSym (z : Int) a ^ c * jacobiSym (z : Int) b ^ c) := by
          rw [mul_pow, mul_pow, mul_pow]
          ring
    _ = _ := by rw [← pow_two, hsquare, one_pow, one_mul]

private theorem outer41OrdinaryCharacterRestore
    {h Q0 q0 R Q q L w u v : Nat} {s sigma : Int}
    (hh : Odd h) (hQ0 : Odd Q0) (hq0 : Odd q0) (hR : Odd R)
    (hQ : Q = h * Q0) (hq : q = h * q0) (hL : L = h * R)
    (hs : s = 1 ∨ s = -1) :
    qrSign Q0 q0 *
        (jacobiSym (-s) Q0 * jacobiSym s q0 *
          jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
          qrSign Q0 R * qrSign q0 R *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) =
      qrSign Q q *
        (jacobiSym (-s) Q * jacobiSym s q *
          jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
          qrSign Q L * qrSign q L *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) := by
  subst Q
  subst q
  subst L
  have hqr := outer41QrTripleCommonFactor hh hQ0 hq0 hR
  have hunit := outer41JacobiUnitPairRestore hh hQ0 hq0 hs
  have htwo := outer41JacobiTwoPairRestore w hh hQ0 hq0
  have hself := qrSign.sq_eq_one hh hh
  have hfour : qrSign h h ^ 4 = 1 := by
    calc
      qrSign h h ^ 4 = (qrSign h h ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hself]; norm_num
  calc
    qrSign Q0 q0 *
        (jacobiSym (-s) Q0 * jacobiSym s q0 *
          jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
          qrSign Q0 R * qrSign q0 R *
          jacobiSym 2 (h * R) ^ (u + v) *
          jacobiSym sigma (h * R)) =
      (qrSign Q0 q0 * qrSign Q0 R * qrSign q0 R) *
        (jacobiSym (-s) Q0 * jacobiSym s q0) *
        (jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w) *
        (jacobiSym 2 (h * R) ^ (u + v) *
          jacobiSym sigma (h * R)) := by ring
    _ = (qrSign h h * qrSign h h) *
        (qrSign (h * Q0) (h * q0) *
          qrSign (h * Q0) (h * R) *
          qrSign (h * q0) (h * R)) *
        (jacobiSym (-s) (h * Q0) * jacobiSym s (h * q0)) *
        (jacobiSym 2 (h * Q0) ^ w * jacobiSym 2 (h * q0) ^ w) *
        (jacobiSym 2 (h * R) ^ (u + v) *
          jacobiSym sigma (h * R)) := by
            rw [hqr, hunit, htwo]
            ring_nf
            rw [hfour]
            ring
    _ = _ := by rw [← pow_two, hself, one_mul]; ring

private theorem outer41PrimeCharacterRestore
    {h Q0 q0 R Q q L z w u v zt zd c : Nat} {s sigma : Int}
    (hh : Odd h) (hQ0 : Odd Q0) (hq0 : Odd q0) (hR : Odd R)
    (hQ : Q = h * Q0) (hq : q = h * q0) (hL : L = h * R)
    (hs : s = 1 ∨ s = -1) (hzH : z.Coprime h) :
    qrSign Q0 q0 *
        (jacobiSym (-s) Q0 * jacobiSym s q0 *
          jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
          jacobiSym (z : Int) Q0 ^ c * jacobiSym (z : Int) q0 ^ c *
          qrSign Q0 R * qrSign q0 R *
          jacobiSym 2 L ^ (u + v) *
          jacobiSym (z : Int) L ^ (zt + zd) *
          jacobiSym sigma L) =
      outer41PrimeRawCharacter w u v zt zd c s sigma z Q q L := by
  subst Q
  subst q
  have hbase := outer41OrdinaryCharacterRestore
    (w := w) (u := u) (v := v) (s := s) (sigma := sigma)
    hh hQ0 hq0 hR rfl rfl hL hs
  have hprime := outer41JacobiPrimePairRestore c hh hQ0 hq0 hzH
  calc
    qrSign Q0 q0 *
        (jacobiSym (-s) Q0 * jacobiSym s q0 *
          jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
          jacobiSym (z : Int) Q0 ^ c * jacobiSym (z : Int) q0 ^ c *
          qrSign Q0 R * qrSign q0 R *
          jacobiSym 2 L ^ (u + v) *
          jacobiSym (z : Int) L ^ (zt + zd) *
          jacobiSym sigma L) =
      (qrSign Q0 q0 *
        (jacobiSym (-s) Q0 * jacobiSym s q0 *
          jacobiSym 2 Q0 ^ w * jacobiSym 2 q0 ^ w *
          qrSign Q0 R * qrSign q0 R *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L)) *
        (jacobiSym (z : Int) Q0 ^ c *
          jacobiSym (z : Int) q0 ^ c) *
        jacobiSym (z : Int) L ^ (zt + zd) := by ring
    _ = (qrSign (h * Q0) (h * q0) *
        (jacobiSym (-s) (h * Q0) * jacobiSym s (h * q0) *
          jacobiSym 2 (h * Q0) ^ w * jacobiSym 2 (h * q0) ^ w *
          qrSign (h * Q0) L * qrSign (h * q0) L *
          jacobiSym 2 L ^ (u + v) * jacobiSym sigma L)) *
        (jacobiSym (z : Int) (h * Q0) ^ c *
          jacobiSym (z : Int) (h * q0) ^ c) *
        jacobiSym (z : Int) L ^ (zt + zd) := by
      rw [hbase, ← hprime]
    _ = _ := by
      simp only [outer41PrimeRawCharacter]
      ring

private theorem outer41ThreePrimePairCharacter
    {Q0 q0 R : Nat}
    (hQ0odd : Odd Q0) (hq0odd : Odd q0) (hRodd : Odd R)
    (hthreeQ0 : (3 : Nat).Coprime Q0)
    (hthreeq0 : (3 : Nat).Coprime q0)
    (hmodEight : Q0 % 8 = q0 % 8)
    (hmodThree : Q0 % 3 = q0 % 3) :
    qrSign Q0 q0 *
        (jacobiSym (-1 : Int) Q0 * jacobiSym (1 : Int) q0 *
          jacobiSym 2 Q0 ^ 3 * jacobiSym 2 q0 ^ 3 *
          jacobiSym (3 : Int) Q0 * jacobiSym (3 : Int) q0 *
          qrSign Q0 R * qrSign q0 R) = 1 := by
  have hmodFour : Q0 % 4 = q0 % 4 := by
    calc
      Q0 % 4 = (Q0 % 8) % 4 :=
        (Nat.mod_mod_of_dvd Q0 (by decide : 4 ∣ 8)).symm
      _ = (q0 % 8) % 4 := by rw [hmodEight]
      _ = q0 % 4 := Nat.mod_mod_of_dvd q0 (by decide : 4 ∣ 8)
  have hmodTwelve : Q0 % 12 = q0 % 12 := by
    have hQ3 : Q0 % 3 = (Q0 % 12) % 3 :=
      (Nat.mod_mod_of_dvd Q0 (by decide : 3 ∣ 12)).symm
    have hq3 : q0 % 3 = (q0 % 12) % 3 :=
      (Nat.mod_mod_of_dvd q0 (by decide : 3 ∣ 12)).symm
    have hQ4 : Q0 % 4 = (Q0 % 12) % 4 :=
      (Nat.mod_mod_of_dvd Q0 (by decide : 4 ∣ 12)).symm
    have hq4 : q0 % 4 = (q0 % 12) % 4 :=
      (Nat.mod_mod_of_dvd q0 (by decide : 4 ∣ 12)).symm
    have hQbound : Q0 % 12 < 12 := Nat.mod_lt _ (by decide)
    have hqbound : q0 % 12 < 12 := Nat.mod_lt _ (by decide)
    omega
  have hqmodTwo : q0 % 2 = 1 := Nat.odd_iff.mp hq0odd
  have hqmodFourModTwo : q0 % 2 = (q0 % 4) % 2 :=
    (Nat.mod_mod_of_dvd q0 (by decide : 2 ∣ 4)).symm
  have hqmodFourBound : q0 % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [outer41QrSignOfModFour hQ0odd hq0odd,
    outer41JacobiNegOneOfModFour hQ0odd, jacobiSym.one_left,
    outer41JacobiTwoOfModEight hQ0odd,
    outer41JacobiTwoOfModEight hq0odd,
    outer41JacobiThreeOfModTwelve hQ0odd hthreeQ0,
    outer41JacobiThreeOfModTwelve hq0odd hthreeq0,
    outer41QrSignOfModFour hQ0odd hRodd,
    outer41QrSignOfModFour hq0odd hRodd,
    hmodEight, hmodFour, hmodTwelve]
  repeat' first | split <;> norm_num
  all_goals omega

private theorem outer41OrdinaryLinkFromRaw
    {P Q p q L a b : Nat}
    (certificate : Ss41LocalLinkCertificate P Q p q)
    (w u v : Nat) (s sigma epsilon : Int)
    (hs : s = 1 ∨ s = -1)
    (he : certificate.e = 1)
    (hLpos : 0 < L) (hLodd : Odd L)
    (hcrossRaw : (certificate.h : Int) * certificate.r =
      s * (2 : Int) ^ w * L)
    (htfactor : certificate.t = ((2 ^ u * a ^ 2 : Nat) : Int))
    (hDeltafactor : certificate.Delta = sigma * (2 : Int) ^ v * b ^ 2)
    (haL : a.Coprime L) (hbL : b.Coprime L)
    (hPQ : P.Coprime Q)
    (hdualRaw : Int.ModEq certificate.r
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta))
    (hcharacter :
      qrSign Q q *
          (jacobiSym (-s) Q * jacobiSym s q *
            jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
            qrSign Q L * qrSign q L *
            jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) = epsilon) :
    jacobiSym (P : Int) Q = epsilon * jacobiSym (p : Int) q := by
  obtain ⟨R, hLfactor, hRodd, hrfactor⟩ :=
    outer41ExtractOddCross w s certificate.h_pos certificate.h_odd
      hLodd hs hcrossRaw
  have hRpos : 0 < R := by
    by_contra hR
    have : R = 0 := Nat.eq_zero_of_not_pos hR
    rw [this, mul_zero] at hLfactor
    omega
  have hQ0R : certificate.Q0.Coprime R :=
    (outer41FactorCoprime (R := R) (n := certificate.Q0)
      (w := w) (s := s) hs hrfactor
      (outer41LocalLink_r_coprime_Q0 certificate hPQ)).symm
  have hRdvdR : (R : Int) ∣ certificate.r := by
    use s * (2 : Int) ^ w
    rw [hrfactor]
    norm_num
    ring
  have hdual : Int.ModEq R
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta) :=
    hdualRaw.of_dvd hRdvdR
  have htransfer := outer41OrdinaryLinkTransfer certificate
    w u v s sigma he hRpos hRodd hLfactor hrfactor
    htfactor hDeltafactor haL hbL hQ0R hdual
  have hcharacter' :
      qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-s) certificate.Q0 * jacobiSym s certificate.q0 *
            jacobiSym 2 certificate.Q0 ^ w *
            jacobiSym 2 certificate.q0 ^ w *
            qrSign certificate.Q0 R * qrSign certificate.q0 R *
            jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) = epsilon :=
    (outer41OrdinaryCharacterRestore certificate.h_odd
      certificate.Q0_odd certificate.q0_odd hRodd
      certificate.Q_factor certificate.q_factor hLfactor hs).trans hcharacter
  calc
    jacobiSym (P : Int) Q =
        qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-s) certificate.Q0 * jacobiSym s certificate.q0 *
            jacobiSym 2 certificate.Q0 ^ w *
            jacobiSym 2 certificate.q0 ^ w *
            qrSign certificate.Q0 R * qrSign certificate.q0 R *
            jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) *
          jacobiSym (p : Int) q := htransfer
    _ = epsilon * jacobiSym (p : Int) q := by rw [hcharacter']

private theorem outer41PrimeLinkTransfer
    {P Q p q R L a b z : Nat}
    (certificate : Ss41LocalLinkCertificate P Q p q)
    (w u v zt zd c : Nat) (s sigma primary epsilon : Int)
    (hs : s = 1 ∨ s = -1)
    (hRpos : 0 < R) (hRodd : Odd R)
    (hLfactor : L = certificate.h0 * R)
    (hrfactor : certificate.r =
      s * (2 : Int) ^ w * z ^ c * R)
    (htfactor : certificate.t0 =
      (((2 ^ u * z ^ zt * a ^ 2 : Nat)) : Int))
    (hDeltafactor : certificate.Delta0 =
      sigma * (2 : Int) ^ v * z ^ zd * b ^ 2)
    (haL : a.Coprime L) (hbL : b.Coprime L)
    (htR : Int.gcd certificate.t0 R = 1)
    (hQ0R : certificate.Q0.Coprime R)
    (hendpoint : Int.ModEq R
      ((certificate.q0 : Int) * certificate.t0)
      ((certificate.Q0 : Int) * certificate.Delta0))
    (hzH0 : z.Coprime certificate.h0)
    (hprimary :
      jacobiSym (P : Int) certificate.e *
        jacobiSym (p : Int) certificate.e = primary)
    (hcharacter :
      primary *
        outer41PrimeRawCharacter w u v zt zd c s sigma z
          (certificate.h0 * certificate.Q0)
          (certificate.h0 * certificate.q0) L = epsilon) :
    jacobiSym (P : Int) Q = epsilon * jacobiSym (p : Int) q := by
  have hcrossProduct := outer41PrimeExceptionalCrossProduct
    (Q0 := certificate.Q0) (q0 := certificate.q0)
    (h := certificate.h0) (R := R) (L := L)
    (a := a) (b := b) (z := z)
    (r := certificate.r) (t := certificate.t0)
    (Delta := certificate.Delta0)
    w u v zt zd c s sigma certificate.h0_pos hRpos
    certificate.Q0_odd certificate.q0_odd hRodd hLfactor
    hrfactor htfactor hDeltafactor haL hbL htR hQ0R hendpoint
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  have hrestore := outer41PrimeCharacterRestore
    (h := certificate.h0) (Q0 := certificate.Q0)
    (q0 := certificate.q0) (R := R)
    (Q := certificate.h0 * certificate.Q0)
    (q := certificate.h0 * certificate.q0) (L := L)
    (z := z) (w := w) (u := u) (v := v)
    (zt := zt) (zd := zd) (c := c) (s := s) (sigma := sigma)
    hh0odd certificate.Q0_odd certificate.q0_odd hRodd
    rfl rfl hLfactor hs hzH0
  have hfactored := outer41FactoredLinkTransfer certificate
  calc
    jacobiSym (P : Int) Q =
        qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (P : Int) certificate.e *
            jacobiSym (p : Int) certificate.e) *
          (jacobiSym certificate.t0 certificate.h0 *
            jacobiSym certificate.Delta0 certificate.h0) *
          jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 *
          jacobiSym (p : Int) q := hfactored
    _ = primary *
        (qrSign certificate.Q0 certificate.q0 *
          ((jacobiSym certificate.t0 certificate.h0 *
              jacobiSym certificate.Delta0 certificate.h0) *
            jacobiSym (-certificate.r) certificate.Q0 *
            jacobiSym certificate.r certificate.q0)) *
        jacobiSym (p : Int) q := by
      rw [hprimary]
      ring
    _ = primary *
        (qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-s) certificate.Q0 *
            jacobiSym s certificate.q0 *
            jacobiSym 2 certificate.Q0 ^ w *
            jacobiSym 2 certificate.q0 ^ w *
            jacobiSym (z : Int) certificate.Q0 ^ c *
            jacobiSym (z : Int) certificate.q0 ^ c *
            qrSign certificate.Q0 R * qrSign certificate.q0 R *
            jacobiSym 2 L ^ (u + v) *
            jacobiSym (z : Int) L ^ (zt + zd) *
            jacobiSym sigma L)) *
        jacobiSym (p : Int) q := by
      rw [hcrossProduct]
    _ = primary *
        outer41PrimeRawCharacter w u v zt zd c s sigma z
          (certificate.h0 * certificate.Q0)
          (certificate.h0 * certificate.q0) L *
        jacobiSym (p : Int) q := by rw [hrestore]
    _ = epsilon * jacobiSym (p : Int) q := by rw [hcharacter]

private theorem outer41PrimeRawCharacter_of_neutral
    {Q q L z : Nat} (w u v zt zd c : Nat) (s sigma epsilon : Int)
    (hbase :
      qrSign Q q *
          (jacobiSym (-s) Q * jacobiSym s q *
            jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
            qrSign Q L * qrSign q L *
            jacobiSym 2 L ^ (u + v) * jacobiSym sigma L) = epsilon)
    (hneutral :
      (jacobiSym (z : Int) Q ^ c * jacobiSym (z : Int) q ^ c) *
        jacobiSym (z : Int) L ^ (zt + zd) = 1) :
    outer41PrimeRawCharacter w u v zt zd c s sigma z Q q L = epsilon := by
  simp only [outer41PrimeRawCharacter]
  calc
    qrSign Q q *
        (jacobiSym (-s) Q * jacobiSym s q *
          jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
          jacobiSym (z : Int) Q ^ c * jacobiSym (z : Int) q ^ c *
          qrSign Q L * qrSign q L *
          jacobiSym 2 L ^ (u + v) *
          jacobiSym (z : Int) L ^ (zt + zd) *
          jacobiSym sigma L) =
      (qrSign Q q *
          (jacobiSym (-s) Q * jacobiSym s q *
            jacobiSym 2 Q ^ w * jacobiSym 2 q ^ w *
            qrSign Q L * qrSign q L *
            jacobiSym 2 L ^ (u + v) * jacobiSym sigma L)) *
        ((jacobiSym (z : Int) Q ^ c * jacobiSym (z : Int) q ^ c) *
          jacobiSym (z : Int) L ^ (zt + zd)) := by ring
    _ = epsilon := by rw [hbase, hneutral, mul_one]

private theorem outer41PrimeCoprimeAfterExactPrimary
    {z cap h h0 e : Nat} (hz : z.Prime) (hepos : 0 < e)
    (hfactor : h = e * h0) (hprimary : Nat.gcd cap h = e)
    (hnext : z * e ∣ cap) : z.Coprime h0 := by
  rw [hz.coprime_iff_not_dvd]
  intro hzH0
  have hnextH : z * e ∣ h := by
    obtain ⟨a, ha⟩ := hzH0
    refine ⟨a, ?_⟩
    rw [hfactor, ha]
    ring
  have hnextGcd : z * e ∣ Nat.gcd cap h :=
    Nat.dvd_gcd hnext hnextH
  rw [hprimary] at hnextGcd
  have hle : z * e ≤ e := Nat.le_of_dvd hepos hnextGcd
  have hzTwo := hz.two_le
  nlinarith

private theorem outer41ReducedFactorMod
    {Q e Q0 modulus residue : Nat}
    (hfactor : Q = e * Q0) (hecop : e.Coprime modulus)
    (hQmod : Q % modulus = (e * residue) % modulus) :
    Q0 % modulus = residue % modulus := by
  have hmod : Nat.ModEq modulus Q (e * residue) := hQmod
  rw [hfactor] at hmod
  exact hmod.cancel_left_of_coprime hecop.symm.gcd_eq_one

private theorem outer41ReducedPairModAfterFactor
    {Q q e Q0 q0 modulus : Nat} (hmoduluspos : 0 < modulus) (hepos : 0 < e)
    (hQfactor : Q = e * Q0) (hqfactor : q = e * q0)
    (hmod : Nat.ModEq (modulus * e) Q q) :
    Nat.ModEq modulus Q0 q0 := by
  rw [hQfactor, hqfactor] at hmod
  have hcancel := hmod.cancel_left_div_gcd (mul_pos hmoduluspos hepos)
  have hgcd : Nat.gcd (modulus * e) e = e :=
    Nat.gcd_eq_right_iff_dvd.mpr (dvd_mul_left e modulus)
  simpa [hgcd, Nat.mul_comm, Nat.mul_div_right modulus hepos] using hcancel

private theorem outer41PrimeCoprimePairOfCommonCoprimeAndModEq
    {z h Q0 q0 : Nat} (hz : z.Prime) (hzH : z.Coprime h)
    (hQ0q0 : Q0.Coprime q0)
    (hmod : Nat.ModEq z (h * Q0) (h * q0)) :
    z.Coprime (h * Q0) ∧ z.Coprime (h * q0) := by
  have hnotH : ¬z ∣ h := hz.coprime_iff_not_dvd.mp hzH
  have hmodEq : (h * Q0) % z = (h * q0) % z := hmod
  have hnotBoth : ¬(z ∣ Q0 ∧ z ∣ q0) := by
    intro hboth
    have hzGcd : z ∣ Nat.gcd Q0 q0 := Nat.dvd_gcd hboth.1 hboth.2
    rw [hQ0q0.gcd_eq_one] at hzGcd
    exact hz.ne_one (Nat.eq_one_of_dvd_one hzGcd)
  constructor
  · rw [hz.coprime_iff_not_dvd]
    intro hzQ
    rcases hz.dvd_mul.mp hzQ with hzH' | hzQ0
    · exact hnotH hzH'
    · have hleft : (h * Q0) % z = 0 := Nat.dvd_iff_mod_eq_zero.mp hzQ
      have hzq : z ∣ h * q0 := Nat.dvd_iff_mod_eq_zero.mpr (hmodEq.symm.trans hleft)
      rcases hz.dvd_mul.mp hzq with hzH' | hzq0
      · exact hnotH hzH'
      · exact hnotBoth ⟨hzQ0, hzq0⟩
  · rw [hz.coprime_iff_not_dvd]
    intro hzq
    rcases hz.dvd_mul.mp hzq with hzH' | hzq0
    · exact hnotH hzH'
    · have hright : (h * q0) % z = 0 := Nat.dvd_iff_mod_eq_zero.mp hzq
      have hzQ : z ∣ h * Q0 := Nat.dvd_iff_mod_eq_zero.mpr (hmodEq.trans hright)
      rcases hz.dvd_mul.mp hzQ with hzH' | hzQ0
      · exact hnotH hzH'
      · exact hnotBoth ⟨hzQ0, hzq0⟩

private theorem outer41JacobiThreePairOfModTwelve
    {Q q : Nat} (hQodd : Odd Q) (hqodd : Odd q)
    (hthreeQ : (3 : Nat).Coprime Q) (hthreeq : (3 : Nat).Coprime q)
    (hmod : Nat.ModEq 12 Q q) :
    jacobiSym (3 : Int) Q = jacobiSym (3 : Int) q := by
  rw [outer41JacobiThreeOfModTwelve hQodd hthreeQ,
    outer41JacobiThreeOfModTwelve hqodd hthreeq, hmod]

private theorem outer41PrimeNeutralOfSameSymbol
    {Q q L z c exponent : Nat}
    (hQ : Int.gcd (z : Int) Q = 1)
    (hq : Int.gcd (z : Int) q = 1)
    (hL : Int.gcd (z : Int) L = 1)
    (hsame : jacobiSym (z : Int) Q = jacobiSym (z : Int) q)
    (heven : Even exponent) :
    (jacobiSym (z : Int) Q ^ c * jacobiSym (z : Int) q ^ c) *
        jacobiSym (z : Int) L ^ exponent = 1 := by
  have hQsq := jacobiSym.sq_one hQ
  have hqsq := jacobiSym.sq_one hq
  have hLsq := jacobiSym.sq_one hL
  obtain ⟨k, rfl⟩ := heven
  rw [hsame, ← mul_pow, ← pow_two, hqsq, one_pow,
    show k + k = 2 * k by omega, pow_mul, hLsq, one_pow, one_mul]

private theorem outer41PrimeCoprimeReducedDenominators
    {P Q p q z L : Nat}
    (certificate : Ss41LocalLinkCertificate P Q p q)
    (w c : Nat) (s : Int) (hz : z.Prime) (hc : 0 < c)
    (hzH0 : z.Coprime certificate.h0) (hPQ : P.Coprime Q)
    (hcross : (certificate.h0 : Int) * certificate.r =
      s * (2 : Int) ^ w * z ^ c * L) :
    z.Coprime (certificate.h0 * certificate.Q0) ∧
      z.Coprime (certificate.h0 * certificate.q0) := by
  have hzpow : (z : Int) ∣ (z : Int) ^ c := dvd_pow_self _ hc.ne'
  have hzproduct : (z : Int) ∣ (certificate.h0 : Int) * certificate.r := by
    rw [hcross]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right hzpow (s * (2 : Int) ^ w)) L
  have hzR : (z : Int) ∣ certificate.r := by
    have hzproduct' : (z : Int) ∣ certificate.r * certificate.h0 := by
      simpa [mul_comm] using hzproduct
    have hcop : Int.gcd (z : Int) certificate.h0 = 1 := by
      exact_mod_cast hzH0.gcd_eq_one
    exact Int.dvd_of_dvd_mul_left_of_gcd_one hzproduct' hcop
  have hzRnat : z ∣ certificate.r.natAbs := Int.natCast_dvd.mp hzR
  have hcoprimeOfGcd {n : Nat} (hrn : Int.gcd certificate.r n = 1) :
      z.Coprime n := by
    rw [hz.coprime_iff_not_dvd]
    intro hzn
    have hzGcd : z ∣ Nat.gcd certificate.r.natAbs n :=
      Nat.dvd_gcd hzRnat hzn
    have hgcd : Nat.gcd certificate.r.natAbs n = 1 := by
      simpa [Int.gcd_def] using hrn
    rw [hgcd] at hzGcd
    exact hz.ne_one (Nat.eq_one_of_dvd_one hzGcd)
  have hzQ0 := hcoprimeOfGcd
    (outer41LocalLink_r_coprime_Q0 certificate hPQ)
  have hzq0 := hcoprimeOfGcd certificate.r_coprime_q0
  exact ⟨hzH0.mul_right hzQ0, hzH0.mul_right hzq0⟩

private theorem outer41PrimeNeutralOfEvenPowers
    {Q q L z c exponent : Nat}
    (hQ : Int.gcd (z : Int) Q = 1)
    (hq : Int.gcd (z : Int) q = 1)
    (hL : Int.gcd (z : Int) L = 1)
    (hc : Even c) (heven : Even exponent) :
    (jacobiSym (z : Int) Q ^ c * jacobiSym (z : Int) q ^ c) *
        jacobiSym (z : Int) L ^ exponent = 1 := by
  have hQsq := jacobiSym.sq_one hQ
  have hqsq := jacobiSym.sq_one hq
  have hLsq := jacobiSym.sq_one hL
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := heven
  rw [show a + a = 2 * a by omega, show b + b = 2 * b by omega,
    pow_mul, pow_mul, pow_mul, hQsq, hqsq, hLsq]
  norm_num

private theorem outer41PrimeLinkFromReducedRaw
    {P Q p q L a b z e : Nat}
    (certificate : Ss41LocalLinkCertificate P Q p q)
    (w u v zt zd c d : Nat) (s sigma primary epsilon : Int)
    (hs : s = 1 ∨ s = -1)
    (he : certificate.e = e) (hefactor : e = z ^ d)
    (hLpos : 0 < L) (hLodd : Odd L)
    (hzH0 : z.Coprime certificate.h0) (hzL : z.Coprime L)
    (hcrossReduced : (certificate.h0 : Int) * certificate.r =
      s * (2 : Int) ^ w * z ^ c * L)
    (htfactor : certificate.t0 =
      (((2 ^ u * z ^ zt * a ^ 2 : Nat)) : Int))
    (hDeltafactor : certificate.Delta0 =
      sigma * (2 : Int) ^ v * z ^ zd * b ^ 2)
    (haL : a.Coprime L) (hbL : b.Coprime L)
    (hPQ : P.Coprime Q)
    (hdualRaw : Int.ModEq certificate.r
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta))
    (hprimary :
      jacobiSym (P : Int) certificate.e *
        jacobiSym (p : Int) certificate.e = primary)
    (hcharacter :
      primary *
        outer41PrimeRawCharacter w u v zt zd c s sigma z
          (certificate.h0 * certificate.Q0)
          (certificate.h0 * certificate.q0) L = epsilon) :
    jacobiSym (P : Int) Q = epsilon * jacobiSym (p : Int) q := by
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  obtain ⟨R, hLfactor, hRodd, hrfactor⟩ :=
    outer41ExtractOddPrimeCross w c s certificate.h0_pos hh0odd
      hLodd hs hzH0 hcrossReduced
  have hRpos : 0 < R := by
    by_contra hR
    have : R = 0 := Nat.eq_zero_of_not_pos hR
    rw [this, mul_zero] at hLfactor
    omega
  have hRdvdL : R ∣ L := ⟨certificate.h0, by rw [hLfactor]; ring⟩
  have hzR : z.Coprime R := hzL.of_dvd_right hRdvdL
  have haR : a.Coprime R := haL.of_dvd_right hRdvdL
  have htwoR : (2 : Nat).Coprime R := hRodd.coprime_two_right.symm
  have htRnat : (2 ^ u * z ^ zt * a ^ 2).Coprime R :=
    ((htwoR.pow_left u).mul_left (hzR.pow_left zt)).mul_left
      (haR.pow_left 2)
  have htR : Int.gcd certificate.t0 R = 1 := by
    rw [htfactor, Int.gcd_natCast_natCast]
    exact htRnat.gcd_eq_one
  have hrfactorTotal : certificate.r =
      s * (2 : Int) ^ w * (z ^ c * R : Nat) := by
    rw [hrfactor]
    push_cast
    ring
  have hQ0total : certificate.Q0.Coprime (z ^ c * R) :=
    (outer41FactorCoprime (R := z ^ c * R) (n := certificate.Q0)
      (w := w) (s := s) hs hrfactorTotal
      (outer41LocalLink_r_coprime_Q0 certificate hPQ)).symm
  have hQ0R : certificate.Q0.Coprime R :=
    hQ0total.of_dvd_right ⟨z ^ c, by ring⟩
  have hRdvdR : (R : Int) ∣ certificate.r := by
    refine ⟨s * (2 : Int) ^ w * z ^ c, ?_⟩
    rw [hrfactor]
    push_cast
    ring
  have hdualR := hdualRaw.of_dvd hRdvdR
  have hscaled : Int.ModEq R
      ((e : Int) * ((certificate.q0 : Int) * certificate.t0))
      ((e : Int) * ((certificate.Q0 : Int) * certificate.Delta0)) := by
    rw [certificate.t_factor, certificate.Delta_factor, he] at hdualR
    convert hdualR using 1 <;> ring
  have heR : e.Coprime R := by
    rw [hefactor]
    exact hzR.pow_left d
  have heRInt : Int.gcd (R : Int) e = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact heR.symm.gcd_eq_one
  have hendpoint : Int.ModEq R
      ((certificate.q0 : Int) * certificate.t0)
      ((certificate.Q0 : Int) * certificate.Delta0) := by
    rw [Int.modEq_iff_dvd] at hscaled ⊢
    apply Int.dvd_of_dvd_mul_right_of_gcd_one (b := (e : Int))
    · convert hscaled using 1
      ring
    · exact heRInt
  exact outer41PrimeLinkTransfer certificate
    w u v zt zd c s sigma primary epsilon hs hRpos hRodd
    hLfactor hrfactor htfactor hDeltafactor haL hbL htR hQ0R
    hendpoint hzH0 hprimary hcharacter

private theorem outer41Q11Q9ModTwentyFourCoeffs :
    outer41Q11Coeffs.map (· % 24) =
      outer41Q9Coeffs.map (· % 24) ++ List.replicate 2 0 := by
  decide

private theorem outer41Q11Q9ModTwentyFour (j : Nat) :
    Nat.ModEq 24 (outer41Q11 j) (outer41Q9 j) := by
  change outer41Q11 j % 24 = outer41Q9 j % 24
  have h11 := outer41HornerNat_map_mod j 24 outer41Q11Coeffs
  have h9 := outer41HornerNat_map_mod j 24 outer41Q9Coeffs
  rw [outer41Q11Q9ModTwentyFourCoeffs,
    outer41HornerNat_append_zeros] at h11
  simpa [outer41Q11, outer41Q9] using h11.trans h9.symm

private theorem outer41Q11Q9ModTwelve (j : Nat) :
    Nat.ModEq 12 (outer41Q11 j) (outer41Q9 j) :=
  (outer41Q11Q9ModTwentyFour j).of_dvd (by decide)

private theorem outer41Q11Q9ModEight (j : Nat) :
    Nat.ModEq 8 (outer41Q11 j) (outer41Q9 j) :=
  (outer41Q11Q9ModTwentyFour j).of_dvd (by decide)

set_option maxHeartbeats 2000000 in
private theorem outer41Q11Q9ModThirtySix_of_mod_three_one
    (j : Nat) (hj : j % 3 = 1) :
    Nat.ModEq 36 (outer41Q11 j) (outer41Q9 j) := by
  change outer41Q11 j % 36 = outer41Q9 j % 36
  have h11 := outer41HornerNat_mod j 36 outer41Q11Coeffs
  have h9 := outer41HornerNat_mod j 36 outer41Q9Coeffs
  change outer41Q11 j % 36 = _ at h11
  change outer41Q9 j % 36 = _ at h9
  have hjmod3 : j % 3 = (j % 36) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 36)).symm
  have hjbound : j % 36 < 36 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 36 <;>
    norm_num [outer41Q11Coeffs, outer41Q9Coeffs,
      outer41HornerNat] at h11 h9 hjmod3
  all_goals omega

set_option maxHeartbeats 5000000 in
private theorem outer41Q11Q9ModOneHundredEight_of_mod_nine_two_or_five
    (j : Nat) (hj : j % 9 = 2 ∨ j % 9 = 5) :
    Nat.ModEq 108 (outer41Q11 j) (outer41Q9 j) := by
  change outer41Q11 j % 108 = outer41Q9 j % 108
  have h11 := outer41HornerNat_mod j 108 outer41Q11Coeffs
  have h9 := outer41HornerNat_mod j 108 outer41Q9Coeffs
  change outer41Q11 j % 108 = _ at h11
  change outer41Q9 j % 108 = _ at h9
  have hjmod9 : j % 9 = (j % 108) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 108)).symm
  have hjbound : j % 108 < 108 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 108 <;>
    norm_num [outer41Q11Coeffs, outer41Q9Coeffs,
      outer41HornerNat] at h11 h9 hjmod9
  all_goals omega

private theorem outer41Link11BaseCharacter
    {Q q L : Nat} (hQodd : Odd Q) (hqodd : Odd q) (hLodd : Odd L)
    (hmodEight : Nat.ModEq 8 Q q) (hLmod : L % 8 = 5) :
    qrSign Q q *
        (jacobiSym (-1 : Int) Q * jacobiSym (1 : Int) q *
          jacobiSym 2 Q ^ 2 * jacobiSym 2 q ^ 2 *
          qrSign Q L * qrSign q L *
          jacobiSym 2 L ^ (2 + 5) * jacobiSym (-1 : Int) L) = -1 := by
  have hbase := outer41OrdinaryRawCharacter 2 2 5 1 (-1)
    (Or.inl rfl) (Or.inr rfl) hQodd hqodd hLodd
  change Q % 8 = q % 8 at hmodEight
  have hqmodTwo : q % 2 = 1 := Nat.odd_iff.mp hqodd
  have hqmodEightModTwo : q % 2 = (q % 8) % 2 :=
    (Nat.mod_mod_of_dvd q (by decide : 2 ∣ 8)).symm
  have hqbound : q % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [hbase, hmodEight, hLmod]
  interval_cases hcase : q % 8
  all_goals norm_num [hcase] at hqmodEightModTwo
  all_goals try omega
  all_goals norm_num [hcase, outer41OrdinaryActualResidueSign,
    outer41QrResidueCharacter, outer41UnitResidueCharacter,
    outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private def outer41Link11L (j : Nat) : Nat :=
  16641927165277 + 17449110684864 * j

private theorem outer41Link11L_pos (j : Nat) : 0 < outer41Link11L j := by
  simp [outer41Link11L]

private theorem outer41Link11L_odd (j : Nat) : Odd (outer41Link11L j) := by
  rw [Nat.odd_iff]
  norm_num [outer41Link11L, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link11L_coprime_three (j : Nat) :
    (3 : Nat).Coprime (outer41Link11L j) := by
  rw [Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
  norm_num [outer41Link11L, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link11L_coprime_a (j : Nat) :
    (147923 : Nat).Coprime (outer41Link11L j) := by
  simpa [outer41Link11L,
    show 17449110684864 = 117960768 * 147923 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 147923 16641927165277
      (117960768 * j)).mpr (by norm_num)

private theorem outer41Link11L_coprime_b (j : Nat) :
    (204793 : Nat).Coprime (outer41Link11L j) := by
  simpa [outer41Link11L,
    show 17449110684864 = 85203648 * 204793 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 204793 16641927165277
      (85203648 * j)).mpr (by norm_num)

set_option maxHeartbeats 700000 in
private theorem outer41Link11Branch
    (j e d c zt zd : Nat)
    (he : (outer41LocalLink11 j).e = e)
    (hefactor : e = 3 ^ d)
    (hprimary81 : Nat.gcd 81 (outer41LocalLink11 j).h = e)
    (hcrossPower : e * 3 ^ c = 3 ^ 3)
    (htPower : e * 3 ^ zt = 3 ^ 5)
    (hDeltaPower : e * 3 ^ zd = 3 ^ 3)
    (hneutral :
      (jacobiSym (3 : Int)
            ((outer41LocalLink11 j).h0 * (outer41LocalLink11 j).Q0) ^ c *
          jacobiSym (3 : Int)
            ((outer41LocalLink11 j).h0 * (outer41LocalLink11 j).q0) ^ c) *
        jacobiSym (3 : Int) (outer41Link11L j) ^ (zt + zd) = 1) :
    jacobiSym (outer41P11 j : Int) (outer41Q11 j) =
      -jacobiSym (outer41P9 j : Int) (outer41Q9 j) := by
  let certificate := outer41LocalLink11 j
  have hepos : 0 < e := by simpa [← he] using certificate.e_pos
  have hzH0 : (3 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactPrimary Nat.prime_three hepos
      (by simpa [certificate, he] using certificate.h_factor)
      (by simpa [certificate] using hprimary81)
      (by
        refine ⟨3 ^ c, ?_⟩
        calc
          81 = 3 * (3 ^ 3) := by norm_num
          _ = 3 * (e * 3 ^ c) := by rw [hcrossPower]
          _ = (3 * e) * 3 ^ c := by ring)
  have hQfactor : outer41Q11 j = e * (certificate.h0 * certificate.Q0) := by
    calc
      outer41Q11 j = certificate.h * certificate.Q0 := certificate.Q_factor
      _ = (certificate.e * certificate.h0) * certificate.Q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.Q0) := by rw [he]; ring
  have hqfactor : outer41Q9 j = e * (certificate.h0 * certificate.q0) := by
    calc
      outer41Q9 j = certificate.h * certificate.q0 := certificate.q_factor
      _ = (certificate.e * certificate.h0) * certificate.q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.q0) := by rw [he]; ring
  have heodd : Odd e := by simpa [← he] using certificate.e_odd
  have hecopEight : Nat.gcd 8 e = 1 := by
    have hcop : (8 : Nat).Coprime e := by
      simpa [show (8 : Nat) = 2 ^ 3 by decide] using
        heodd.coprime_two_right.symm.pow_left 3
    exact hcop.gcd_eq_one
  have hmodEight : Nat.ModEq 8
      (certificate.h0 * certificate.Q0)
      (certificate.h0 * certificate.q0) := by
    apply outer41ReducedFactorsModEq hQfactor hqfactor hecopEight
    exact outer41Q11Q9ModEight j
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  have hQodd : Odd (certificate.h0 * certificate.Q0) :=
    hh0odd.mul certificate.Q0_odd
  have hqodd : Odd (certificate.h0 * certificate.q0) :=
    hh0odd.mul certificate.q0_odd
  have hbase := outer41Link11BaseCharacter hQodd hqodd
    (outer41Link11L_odd j) hmodEight (by
      norm_num [outer41Link11L, Nat.add_mod, Nat.mul_mod])
  have hcharacter :
      (1 : Int) * outer41PrimeRawCharacter 2 2 5 zt zd c 1 (-1) 3
          (certificate.h0 * certificate.Q0)
          (certificate.h0 * certificate.q0) (outer41Link11L j) = -1 := by
    rw [one_mul]
    exact outer41PrimeRawCharacter_of_neutral
      2 2 5 zt zd c 1 (-1) (-1) hbase hneutral
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 * outer41Link11L j := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P9 j : Int) * outer41Q11 j -
            (outer41Q9 j : Int) * outer41P11 j := certificate.cross
      _ = outer41P9Int j * outer41Q11Int j -
          outer41Q9Int j * outer41P11Int j := by
            rw [outer41P9Cast, outer41Q11Cast,
              outer41Q9Cast, outer41P11Cast]
      _ = 108 * (16641927165277 + 17449110684864 * (j : Int)) :=
        outer41Cross11 j
      _ = (1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 *
          outer41Link11L j := by simp [outer41Link11L]
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ c * outer41Link11L j := by
    apply mul_left_cancel₀ (show (e : Int) ≠ 0 by exact_mod_cast hepos.ne')
    calc
      (e : Int) * ((certificate.h0 : Int) * certificate.r) =
          (certificate.h : Int) * certificate.r := by
            rw [certificate.h_factor, he]
            push_cast
            ring
      _ = (1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 *
          outer41Link11L j := hcrossRaw
      _ = (e : Int) *
          ((1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ c *
            outer41Link11L j) := by
              have hpower : (e : Int) * (3 : Int) ^ c = (3 : Int) ^ 3 := by
                exact_mod_cast hcrossPower
              rw [show (1 : Int) * 2 ^ 2 * 3 ^ 3 * outer41Link11L j =
                4 * ((3 : Int) ^ 3) * outer41Link11L j by ring,
                ← hpower]
              push_cast
              ring
  have htfactor : certificate.t0 =
      (((2 ^ 2 * 3 ^ zt * 147923 ^ 2 : Nat)) : Int) := by
    apply mul_left_cancel₀ (show (e : Int) ≠ 0 by exact_mod_cast hepos.ne')
    calc
      (e : Int) * certificate.t0 = certificate.t := by
        rw [certificate.t_factor, he]
      _ = 21268539938988 := (outer41Constants11 j).1
      _ = (e : Int) * (((2 ^ 2 * 3 ^ zt * 147923 ^ 2 : Nat)) : Int) := by
        have hpower : (e : Int) * (3 : Int) ^ zt = (3 : Int) ^ 5 := by
          exact_mod_cast htPower
        push_cast
        rw [show (21268539938988 : Int) =
          4 * (3 : Int) ^ 5 * 147923 ^ 2 by norm_num, ← hpower]
        ring
  have hDeltafactor : certificate.Delta0 =
      (-1 : Int) * (2 : Int) ^ 5 * (3 : Int) ^ zd * 204793 ^ 2 := by
    apply mul_left_cancel₀ (show (e : Int) ≠ 0 by exact_mod_cast hepos.ne')
    calc
      (e : Int) * certificate.Delta0 = certificate.Delta := by
        rw [certificate.Delta_factor, he]
      _ = -36236309341536 := (outer41Constants11 j).2
      _ = (e : Int) *
          ((-1 : Int) * (2 : Int) ^ 5 * (3 : Int) ^ zd * 204793 ^ 2) := by
        have hpower : (e : Int) * (3 : Int) ^ zd = (3 : Int) ^ 3 := by
          exact_mod_cast hDeltaPower
        rw [show (-36236309341536 : Int) =
          -32 * (3 : Int) ^ 3 * 204793 ^ 2 by norm_num, ← hpower]
        ring
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A10 j) (outer41B10 j)
    (by
      rw [outer41P11Cast, outer41Q11Cast]
      exact outer41Endpoint11 j)
    (by
      rw [outer41P9Cast, outer41Q9Cast]
      exact outer41Delta11 j)
  simpa only [Int.reduceNeg, neg_mul, one_mul] using
    outer41PrimeLinkFromReducedRaw certificate
      2 2 5 zt zd c d 1 (-1) 1 (-1) (Or.inl rfl)
      he hefactor (outer41Link11L_pos j) (outer41Link11L_odd j)
      hzH0 (outer41Link11L_coprime_three j) hcrossReduced
      htfactor hDeltafactor (outer41Link11L_coprime_a j)
      (outer41Link11L_coprime_b j) (outer41RawCoprime11 j)
      hdualRaw (outer41Correction11 j) hcharacter

private theorem outer41Link11NeutralOfReducedMod
    (j e c zt zd : Nat)
    (he : (outer41LocalLink11 j).e = e)
    (hzH0 : (3 : Nat).Coprime (outer41LocalLink11 j).h0)
    (hmodRaw : Nat.ModEq (12 * e) (outer41Q11 j) (outer41Q9 j))
    (heven : Even (zt + zd)) :
    (jacobiSym (3 : Int)
          ((outer41LocalLink11 j).h0 * (outer41LocalLink11 j).Q0) ^ c *
        jacobiSym (3 : Int)
          ((outer41LocalLink11 j).h0 * (outer41LocalLink11 j).q0) ^ c) *
      jacobiSym (3 : Int) (outer41Link11L j) ^ (zt + zd) = 1 := by
  let certificate := outer41LocalLink11 j
  have hepos : 0 < e := by simpa [← he] using certificate.e_pos
  have hQfactor : outer41Q11 j = e * (certificate.h0 * certificate.Q0) := by
    calc
      outer41Q11 j = certificate.h * certificate.Q0 := certificate.Q_factor
      _ = (certificate.e * certificate.h0) * certificate.Q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.Q0) := by rw [he]; ring
  have hqfactor : outer41Q9 j = e * (certificate.h0 * certificate.q0) := by
    calc
      outer41Q9 j = certificate.h * certificate.q0 := certificate.q_factor
      _ = (certificate.e * certificate.h0) * certificate.q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.q0) := by rw [he]; ring
  have hmodTwelve : Nat.ModEq 12
      (certificate.h0 * certificate.Q0)
      (certificate.h0 * certificate.q0) :=
    outer41ReducedPairModAfterFactor (by norm_num) hepos
      hQfactor hqfactor hmodRaw
  have hmodThree : Nat.ModEq 3
      (certificate.h0 * certificate.Q0)
      (certificate.h0 * certificate.q0) :=
    hmodTwelve.of_dvd (by decide)
  have hthree := outer41PrimeCoprimePairOfCommonCoprimeAndModEq
    Nat.prime_three (by simpa [certificate] using hzH0)
    certificate.Q0_coprime_q0 hmodThree
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  have hQodd : Odd (certificate.h0 * certificate.Q0) :=
    hh0odd.mul certificate.Q0_odd
  have hqodd : Odd (certificate.h0 * certificate.q0) :=
    hh0odd.mul certificate.q0_odd
  have hsame := outer41JacobiThreePairOfModTwelve hQodd hqodd
    hthree.1 hthree.2 hmodTwelve
  have hQint : Int.gcd (3 : Int)
      (certificate.h0 * certificate.Q0) = 1 := by
    exact_mod_cast hthree.1.gcd_eq_one
  have hqint : Int.gcd (3 : Int)
      (certificate.h0 * certificate.q0) = 1 := by
    exact_mod_cast hthree.2.gcd_eq_one
  have hLint : Int.gcd (3 : Int) (outer41Link11L j) = 1 := by
    exact_mod_cast (outer41Link11L_coprime_three j).gcd_eq_one
  exact outer41PrimeNeutralOfSameSymbol hQint hqint hLint hsame heven

private theorem outer41Link11H0CoprimeThree
    (j e c : Nat) (he : (outer41LocalLink11 j).e = e)
    (hprimary : Nat.gcd 81 (outer41LocalLink11 j).h = e)
    (hpower : e * 3 ^ c = 3 ^ 3) :
    (3 : Nat).Coprime (outer41LocalLink11 j).h0 := by
  have hepos : 0 < e := by
    simpa [← he] using (outer41LocalLink11 j).e_pos
  apply outer41PrimeCoprimeAfterExactPrimary Nat.prime_three hepos
    (by simpa [he] using (outer41LocalLink11 j).h_factor) hprimary
  refine ⟨3 ^ c, ?_⟩
  calc
    81 = 3 * (3 ^ 3) := by norm_num
    _ = 3 * (e * 3 ^ c) := by rw [hpower]
    _ = (3 * e) * 3 ^ c := by ring

private theorem outer41Link11_9_e_one
    (j : Nat) (hj : j % 3 = 0) :
    jacobiSym (outer41P11 j : Int) (outer41Q11 j) =
      -jacobiSym (outer41P9 j : Int) (outer41Q9 j) := by
  have hjmod : j % 3 = (j % 9) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
  have h8 : j % 9 ≠ 8 := by omega
  have he : (outer41LocalLink11 j).e = 1 := by
    rw [outer41E11, if_neg h8]
    simp [hj]
  have hprimary : Nat.gcd 81 (outer41LocalLink11 j).h = 1 := by
    rw [(outer41LocalLink11 j).h_eq_gcd]
    simpa [h8, hj] using outer41Primary11 j
  have hzH0 := outer41Link11H0CoprimeThree j 1 3 he hprimary (by norm_num)
  have hneutral := outer41Link11NeutralOfReducedMod j 1 3 5 3 he hzH0
    (by simpa using outer41Q11Q9ModTwelve j) (by decide)
  exact outer41Link11Branch j 1 0 3 5 3 he (by norm_num) hprimary
    (by norm_num) (by norm_num) (by norm_num) hneutral

private theorem outer41Link11_9_e_three
    (j : Nat) (hj : j % 3 = 1) :
    jacobiSym (outer41P11 j : Int) (outer41Q11 j) =
      -jacobiSym (outer41P9 j : Int) (outer41Q9 j) := by
  have hjmod : j % 3 = (j % 9) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
  have h8 : j % 9 ≠ 8 := by omega
  have he : (outer41LocalLink11 j).e = 3 := by
    rw [outer41E11, if_neg h8]
    simp [hj]
  have hprimary : Nat.gcd 81 (outer41LocalLink11 j).h = 3 := by
    rw [(outer41LocalLink11 j).h_eq_gcd]
    simpa [h8, hj] using outer41Primary11 j
  have hzH0 := outer41Link11H0CoprimeThree j 3 2 he hprimary (by norm_num)
  have hneutral := outer41Link11NeutralOfReducedMod j 3 2 4 2 he hzH0
    (by simpa using outer41Q11Q9ModThirtySix_of_mod_three_one j hj) (by decide)
  exact outer41Link11Branch j 3 1 2 4 2 he (by norm_num) hprimary
    (by norm_num) (by norm_num) (by norm_num) hneutral

private theorem outer41Link11_9_e_nine
    (j : Nat) (hj : j % 9 = 2 ∨ j % 9 = 5) :
    jacobiSym (outer41P11 j : Int) (outer41Q11 j) =
      -jacobiSym (outer41P9 j : Int) (outer41Q9 j) := by
  have hjmod : j % 3 = (j % 9) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
  have h8 : j % 9 ≠ 8 := by omega
  have h2 : j % 3 = 2 := by omega
  have he : (outer41LocalLink11 j).e = 9 := by
    rw [outer41E11, if_neg h8, if_pos h2]
  have hprimary : Nat.gcd 81 (outer41LocalLink11 j).h = 9 := by
    rw [(outer41LocalLink11 j).h_eq_gcd]
    simpa [h8, h2] using outer41Primary11 j
  have hzH0 := outer41Link11H0CoprimeThree j 9 1 he hprimary (by norm_num)
  have hneutral := outer41Link11NeutralOfReducedMod j 9 1 3 1 he hzH0
    (by simpa using
      outer41Q11Q9ModOneHundredEight_of_mod_nine_two_or_five j hj) (by decide)
  exact outer41Link11Branch j 9 2 1 3 1 he (by norm_num) hprimary
    (by norm_num) (by norm_num) (by norm_num) hneutral

private theorem outer41Link11_9_e_twentySeven
    (j : Nat) (hj : j % 9 = 8) :
    jacobiSym (outer41P11 j : Int) (outer41Q11 j) =
      -jacobiSym (outer41P9 j : Int) (outer41Q9 j) := by
  have he : (outer41LocalLink11 j).e = 27 := by
    rw [outer41E11, if_pos hj]
  have hprimary : Nat.gcd 81 (outer41LocalLink11 j).h = 27 := by
    rw [(outer41LocalLink11 j).h_eq_gcd]
    simpa [hj] using outer41Primary11 j
  have hzH0 := outer41Link11H0CoprimeThree j 27 0 he hprimary (by norm_num)
  have hLint : Int.gcd (3 : Int) (outer41Link11L j) = 1 := by
    exact_mod_cast (outer41Link11L_coprime_three j).gcd_eq_one
  have hneutral :
      (jacobiSym (3 : Int)
            ((outer41LocalLink11 j).h0 * (outer41LocalLink11 j).Q0) ^ 0 *
          jacobiSym (3 : Int)
            ((outer41LocalLink11 j).h0 * (outer41LocalLink11 j).q0) ^ 0) *
        jacobiSym (3 : Int) (outer41Link11L j) ^ (2 + 0) = 1 := by
    norm_num [jacobiSym.sq_one hLint]
  exact outer41Link11Branch j 27 3 0 2 0 he (by norm_num) hprimary
    (by norm_num) (by norm_num) (by norm_num) hneutral

private theorem outer41Link11_9 (j : Nat) :
    jacobiSym (outer41P11 j : Int) (outer41Q11 j) =
      -jacobiSym (outer41P9 j : Int) (outer41Q9 j) := by
  by_cases h8 : j % 9 = 8
  · exact outer41Link11_9_e_twentySeven j h8
  · have hjmod : j % 3 = (j % 9) % 3 :=
      (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
    by_cases h2 : j % 3 = 2
    · have hjbound : j % 9 < 9 := Nat.mod_lt _ (by decide)
      have hj : j % 9 = 2 ∨ j % 9 = 5 := by omega
      exact outer41Link11_9_e_nine j hj
    · by_cases h1 : j % 3 = 1
      · exact outer41Link11_9_e_three j h1
      · have hbound : j % 3 < 3 := Nat.mod_lt _ (by decide)
        have h0 : j % 3 = 0 := by omega
        exact outer41Link11_9_e_one j h0

private def outer41Link25OffL (j : Nat) : Nat :=
  91370185007570122207 + 76509722917161697392 * j

private def outer41Link25OnL (j : Nat) : Nat :=
  77652835385654653147 + 76509722917161697392 * (j / 13)

private theorem outer41Link25OnL_reconstruct
    (j : Nat) (hj : j % 13 = 12) :
    outer41Link25OffL j = 13 * outer41Link25OnL j := by
  have hdecomp : 13 * (j / 13) + 12 = j :=
    outer41_thirteen_mul_div_add_twelve j hj
  calc
    outer41Link25OffL j =
        91370185007570122207 +
          76509722917161697392 * (13 * (j / 13) + 12) := by
      rw [hdecomp]
      rfl
    _ = 13 * outer41Link25OnL j := by
      simp [outer41Link25OnL]
      ring

private theorem outer41Link25OffL_pos (j : Nat) : 0 < outer41Link25OffL j := by
  simp [outer41Link25OffL]

private theorem outer41Link25OnL_pos (j : Nat) : 0 < outer41Link25OnL j := by
  simp [outer41Link25OnL]

private theorem outer41Link25OffL_odd (j : Nat) : Odd (outer41Link25OffL j) := by
  rw [Nat.odd_iff]
  norm_num [outer41Link25OffL, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link25OnL_odd (j : Nat) : Odd (outer41Link25OnL j) := by
  rw [Nat.odd_iff]
  norm_num [outer41Link25OnL, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link25OffL_coprime_three (j : Nat) :
    (3 : Nat).Coprime (outer41Link25OffL j) := by
  rw [Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
  norm_num [outer41Link25OffL, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link25OnL_coprime_three (j : Nat) :
    (3 : Nat).Coprime (outer41Link25OnL j) := by
  rw [Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
  norm_num [outer41Link25OnL, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link25OffL_coprime_a (j : Nat) :
    (1378913863 : Nat).Coprime (outer41Link25OffL j) := by
  simpa [outer41Link25OffL,
    show 76509722917161697392 = 55485498384 * 1378913863 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 1378913863 91370185007570122207
      (55485498384 * j)).mpr (by norm_num)

private theorem outer41Link25OnL_coprime_a (j : Nat) :
    (1378913863 : Nat).Coprime (outer41Link25OnL j) := by
  simpa [outer41Link25OnL,
    show 76509722917161697392 = 55485498384 * 1378913863 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 1378913863 77652835385654653147
      (55485498384 * (j / 13))).mpr (by norm_num)

private theorem outer41Link25OffL_coprime_b (j : Nat) :
    (385315961 : Nat).Coprime (outer41Link25OffL j) := by
  simpa [outer41Link25OffL,
    show 76509722917161697392 = 198563596272 * 385315961 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 385315961 91370185007570122207
      (198563596272 * j)).mpr (by norm_num)

private theorem outer41Link25OnL_coprime_b (j : Nat) :
    (385315961 : Nat).Coprime (outer41Link25OnL j) := by
  simpa [outer41Link25OnL,
    show 76509722917161697392 = 198563596272 * 385315961 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 385315961 77652835385654653147
      (198563596272 * (j / 13))).mpr (by norm_num)

set_option maxHeartbeats 400000 in
private theorem outer41Link25OffCross
    (j : Nat) (hj : j % 13 ≠ 12) :
    ((outer41LocalLink25 j).h : Int) * (outer41LocalLink25 j).r =
      (-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 * outer41Link25OffL j := by
  let certificate := outer41LocalLink25 j
  calc
    (certificate.h : Int) * certificate.r =
        (outer41ReducedP23 j : Int) * outer41Q25 j -
          (outer41ReducedQ23 j : Int) * outer41P25 j := certificate.cross
    _ = outer41P23Int j * outer41Q25Int j -
        outer41Q23Int j * outer41P25Int j := by
      rw [outer41ReducedP23Cast, outer41ReducedQ23Cast,
        outer41P25Cast, outer41Q25Cast]
      simp [hj]
    _ = -108 * (91370185007570122207 +
        76509722917161697392 * (j : Int)) := outer41PrototypeCross25 j
    _ = (-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 *
        outer41Link25OffL j := by simp [outer41Link25OffL]

set_option maxHeartbeats 500000 in
private theorem outer41Link25OnCross
    (j : Nat) (hj : j % 13 = 12) :
    ((outer41LocalLink25 j).h : Int) * (outer41LocalLink25 j).r =
      (-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 * outer41Link25OnL j := by
  let certificate := outer41LocalLink25 j
  apply mul_left_cancel₀ (show (13 : Int) ≠ 0 by norm_num)
  calc
    (13 : Int) * ((certificate.h : Int) * certificate.r) =
        13 * ((outer41ReducedP23 j : Int) * outer41Q25 j -
          (outer41ReducedQ23 j : Int) * outer41P25 j) := by
      rw [certificate.cross]
    _ = outer41P23Int j * outer41Q25Int j -
        outer41Q23Int j * outer41P25Int j := by
      rw [outer41P23Int_reconstruct_reduced j hj,
        outer41Q23Int_reconstruct_reduced j hj,
        outer41P25Cast, outer41Q25Cast]
      ring
    _ = -108 * (91370185007570122207 +
        76509722917161697392 * (j : Int)) := outer41PrototypeCross25 j
    _ = (13 : Int) *
        ((-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 *
          outer41Link25OnL j) := by
      rw [show (91370185007570122207 +
          76509722917161697392 * (j : Int)) =
          (outer41Link25OffL j : Int) by simp [outer41Link25OffL],
        outer41Link25OnL_reconstruct j hj]
      push_cast
      ring

set_option maxHeartbeats 800000 in
private theorem outer41Link25Branch
    (j e d c zt zd L : Nat) (sigma primary epsilon : Int)
    (he : (outer41LocalLink25 j).e = e)
    (hefactor : e = 3 ^ d)
    (hprimary81 : Nat.gcd 81 (outer41LocalLink25 j).h = e)
    (hcrossPower : e * 3 ^ c = 3 ^ 3)
    (htPower : e * 3 ^ zt = 3 ^ 5)
    (hDeltaPower : e * 3 ^ zd = 3 ^ 3)
    (hLpos : 0 < L) (hLodd : Odd L) (hthreeL : (3 : Nat).Coprime L)
    (haL : (1378913863 : Nat).Coprime L)
    (hbL : (385315961 : Nat).Coprime L)
    (hcrossRaw : ((outer41LocalLink25 j).h : Int) *
      (outer41LocalLink25 j).r =
        (-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 * L)
    (hDeltaRaw : (outer41LocalLink25 j).Delta =
      sigma * (2 : Int) ^ 3 * (3 : Int) ^ 3 * 385315961 ^ 2)
    (hprimaryCorrection :
      jacobiSym (outer41P25 j : Int) (outer41LocalLink25 j).e *
        jacobiSym (outer41ReducedP23 j : Int)
          (outer41LocalLink25 j).e = primary)
    (hprimarySign : primary = 1 ∨ primary = -1)
    (hneutral :
      (jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) ^ c *
          jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) ^ c) *
        jacobiSym (3 : Int) L ^ (zt + zd) = 1)
    (hbase :
      qrSign ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0)
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) *
        (jacobiSym (1 : Int)
              ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) *
          jacobiSym (-1 : Int)
              ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) *
          jacobiSym 2
              ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) ^ 2 *
          jacobiSym 2
              ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) ^ 2 *
          qrSign ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) L *
          qrSign ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) L *
          jacobiSym 2 L ^ (2 + 3) * jacobiSym sigma L) =
        primary * epsilon) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      epsilon * jacobiSym (outer41ReducedP23 j : Int)
        (outer41ReducedQ23 j) := by
  let certificate := outer41LocalLink25 j
  have hepos : 0 < e := by simpa [← he] using certificate.e_pos
  have hzH0 : (3 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactPrimary Nat.prime_three hepos
      (by simpa [certificate, he] using certificate.h_factor)
      (by simpa [certificate] using hprimary81)
      (by
        refine ⟨3 ^ c, ?_⟩
        calc
          81 = 3 * (3 ^ 3) := by norm_num
          _ = 3 * (e * 3 ^ c) := by rw [hcrossPower]
          _ = (3 * e) * 3 ^ c := by ring)
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ c * L := by
    apply mul_left_cancel₀ (show (e : Int) ≠ 0 by exact_mod_cast hepos.ne')
    calc
      (e : Int) * ((certificate.h0 : Int) * certificate.r) =
          (certificate.h : Int) * certificate.r := by
            rw [certificate.h_factor, he]
            push_cast
            ring
      _ = (-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ 3 * L := hcrossRaw
      _ = (e : Int) *
          ((-1 : Int) * (2 : Int) ^ 2 * (3 : Int) ^ c * L) := by
        have hpower : (e : Int) * (3 : Int) ^ c = (3 : Int) ^ 3 := by
          exact_mod_cast hcrossPower
        rw [← hpower]
        ring
  have htfactor : certificate.t0 =
      (((2 ^ 2 * 3 ^ zt * 1378913863 ^ 2 : Nat)) : Int) := by
    apply mul_left_cancel₀ (show (e : Int) ≠ 0 by exact_mod_cast hepos.ne')
    calc
      (e : Int) * certificate.t0 = certificate.t := by
        rw [certificate.t_factor, he]
      _ = 1848164145209522451468 := (outer41Constants25 j).1
      _ = (e : Int) *
          (((2 ^ 2 * 3 ^ zt * 1378913863 ^ 2 : Nat)) : Int) := by
        have hpower : (e : Int) * (3 : Int) ^ zt = (3 : Int) ^ 5 := by
          exact_mod_cast htPower
        push_cast
        rw [show (1848164145209522451468 : Int) =
          4 * (3 : Int) ^ 5 * 1378913863 ^ 2 by norm_num, ← hpower]
        ring
  have hDeltafactor : certificate.Delta0 =
      sigma * (2 : Int) ^ 3 * (3 : Int) ^ zd * 385315961 ^ 2 := by
    apply mul_left_cancel₀ (show (e : Int) ≠ 0 by exact_mod_cast hepos.ne')
    calc
      (e : Int) * certificate.Delta0 = certificate.Delta := by
        rw [certificate.Delta_factor, he]
      _ = sigma * (2 : Int) ^ 3 * (3 : Int) ^ 3 * 385315961 ^ 2 :=
        hDeltaRaw
      _ = (e : Int) *
          (sigma * (2 : Int) ^ 3 * (3 : Int) ^ zd * 385315961 ^ 2) := by
        have hpower : (e : Int) * (3 : Int) ^ zd = (3 : Int) ^ 3 := by
          exact_mod_cast hDeltaPower
        rw [← hpower]
        ring
  have hraw := outer41PrimeRawCharacter_of_neutral
    2 2 3 zt zd c (-1) sigma (primary * epsilon) hbase hneutral
  have hcharacter :
      primary * outer41PrimeRawCharacter 2 2 3 zt zd c (-1) sigma 3
          (certificate.h0 * certificate.Q0)
          (certificate.h0 * certificate.q0) L = epsilon := by
    rw [hraw]
    have hprimarySq : primary ^ 2 = 1 := by
      rcases hprimarySign with rfl | rfl <;> norm_num
    calc
      primary * (primary * epsilon) = primary ^ 2 * epsilon := by ring
      _ = epsilon := by rw [hprimarySq, one_mul]
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A24 j) (outer41B24 j)
    (by
      rw [outer41P25Cast, outer41Q25Cast]
      exact outer41PrototypeEndpoint25 j)
    (outer41Delta25Reduced j)
  exact outer41PrimeLinkFromReducedRaw certificate
    2 2 3 zt zd c d (-1) sigma primary epsilon (Or.inr rfl)
    he hefactor hLpos hLodd hzH0 hthreeL hcrossReduced
    htfactor hDeltafactor haL hbL (outer41RawCoprime25 j)
    hdualRaw hprimaryCorrection hcharacter

private theorem outer41ThreePowerH0Coprime
    {P Q p q : Nat} (certificate : Ss41LocalLinkCertificate P Q p q)
    (e c : Nat) (he : certificate.e = e)
    (hprimary : Nat.gcd 81 certificate.h = e)
    (hpower : e * 3 ^ c = 3 ^ 3) :
    (3 : Nat).Coprime certificate.h0 := by
  have hepos : 0 < e := by simpa [← he] using certificate.e_pos
  apply outer41PrimeCoprimeAfterExactPrimary Nat.prime_three hepos
    (by simpa [he] using certificate.h_factor) hprimary
  refine ⟨3 ^ c, ?_⟩
  calc
    81 = 3 * (3 ^ 3) := by norm_num
    _ = 3 * (e * 3 ^ c) := by rw [hpower]
    _ = (3 * e) * 3 ^ c := by ring

private theorem outer41ThreePowerReducedCross
    {P Q p q L : Nat} (certificate : Ss41LocalLinkCertificate P Q p q)
    (e c : Nat) (s : Int) (he : certificate.e = e)
    (hepos : 0 < e) (hpower : e * 3 ^ c = 3 ^ 3)
    (hraw : (certificate.h : Int) * certificate.r =
      s * (2 : Int) ^ 2 * (3 : Int) ^ 3 * L) :
    (certificate.h0 : Int) * certificate.r =
      s * (2 : Int) ^ 2 * (3 : Int) ^ c * L := by
  apply mul_left_cancel₀ (show (e : Int) ≠ 0 by exact_mod_cast hepos.ne')
  calc
    (e : Int) * ((certificate.h0 : Int) * certificate.r) =
        (certificate.h : Int) * certificate.r := by
          rw [certificate.h_factor, he]
          push_cast
          ring
    _ = s * (2 : Int) ^ 2 * (3 : Int) ^ 3 * L := hraw
    _ = (e : Int) * (s * (2 : Int) ^ 2 * (3 : Int) ^ c * L) := by
      have hpowerInt : (e : Int) * (3 : Int) ^ c = (3 : Int) ^ 3 := by
        exact_mod_cast hpower
      rw [← hpowerInt]
      ring

private theorem outer41Link25QModEight (j : Nat) : outer41Q25 j % 8 = 5 := by
  have h := outer41HornerNat_map_mod j 8 outer41Q25Coeffs
  rw [outer41Q25ModEightCoeffs] at h
  simpa [outer41Q25, outer41HornerNat] using h

private theorem outer41ReducedQ23ModEightOff
    (j : Nat) (hj : j % 13 ≠ 12) : outer41ReducedQ23 j % 8 = 7 := by
  rw [outer41ReducedQ23, if_neg hj]
  have h := outer41HornerNat_map_mod j 8 outer41Q23Coeffs
  rw [outer41Q23ModEightCoeffs] at h
  simpa [outer41Q23, outer41HornerNat] using h

private theorem outer41ReducedQ23ModEightOn
    (j : Nat) (hj : j % 13 = 12) : outer41ReducedQ23 j % 8 = 3 := by
  rw [outer41ReducedQ23, if_pos hj]
  have h := outer41HornerNat_map_mod (j / 13) 8 outer41Q23QuotientCoeffs
  rw [outer41Q23QuotientModEightCoeffs] at h
  simpa [outer41Q23Quotient, outer41HornerNat] using h

private theorem outer41Link25ReducedModEight
    (j e Qres qres : Nat)
    (he : (outer41LocalLink25 j).e = e)
    (hQraw : outer41Q25 j % 8 = (e * Qres) % 8)
    (hqraw : outer41ReducedQ23 j % 8 = (e * qres) % 8) :
    ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 8 = Qres % 8 ∧
      ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 8 = qres % 8 := by
  let certificate := outer41LocalLink25 j
  have hQfactor : outer41Q25 j = e * (certificate.h0 * certificate.Q0) := by
    calc
      outer41Q25 j = certificate.h * certificate.Q0 := certificate.Q_factor
      _ = (certificate.e * certificate.h0) * certificate.Q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.Q0) := by rw [he]; ring
  have hqfactor : outer41ReducedQ23 j =
      e * (certificate.h0 * certificate.q0) := by
    calc
      outer41ReducedQ23 j = certificate.h * certificate.q0 := certificate.q_factor
      _ = (certificate.e * certificate.h0) * certificate.q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.q0) := by rw [he]; ring
  have heodd : Odd e := by simpa [← he] using certificate.e_odd
  have hecop : e.Coprime 8 := by
    simpa [show (8 : Nat) = 2 ^ 3 by decide] using
      heodd.coprime_two_right.pow_right 3
  exact ⟨outer41ReducedFactorMod hQfactor hecop hQraw,
    outer41ReducedFactorMod hqfactor hecop hqraw⟩

set_option maxHeartbeats 300000 in
private theorem outer41Link37_35_zero
    (j : Nat) (hj : j % 3 = 0) :
    jacobiSym (outer41P37 j : Int) (outer41Q37 j) =
      jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
  let certificate := outer41LocalLink37 j
  let L := 1882609 + 1526536 * j
  have hLpos : 0 < L := by omega
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hconstants : certificate.t = 3 * (121 : Int) ^ 2 ∧
      certificate.Delta = 3 * (1577 : Int) ^ 2 := by
    rw [(outer41Constants37 j).1, (outer41Constants37 j).2]
    norm_num
  have he : certificate.e = 3 := by
    rw [outer41E37, if_pos hj]
  have hhfactor : certificate.h = 3 * certificate.h0 := by
    simpa [he] using certificate.h_factor
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  have hprimary : Nat.gcd 9 certificate.h = 3 := by
    rw [certificate.h_eq_gcd]
    simpa [hj] using outer41Primary37 j
  have hthreeH0 : (3 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactExtraction Nat.prime_three
      (by simpa using hprimary) hhfactor
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 2 * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P35 j : Int) * outer41Q37 j -
            (outer41Q35 j : Int) * outer41P37 j := certificate.cross
      _ = outer41P35Int j * outer41Q37Int j -
          outer41Q35Int j * outer41P37Int j := by
            rw [outer41P35Cast, outer41Q37Cast,
              outer41Q35Cast, outer41P37Cast]
      _ = 72 * (1882609 + 1526536 * (j : Int)) := outer41Cross37 j
      _ = (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 2 * L := by
        dsimp [L]
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 1 * L := by
    apply mul_left_cancel₀ (show (3 : Int) ≠ 0 by norm_num)
    calc
      (3 : Int) * ((certificate.h0 : Int) * certificate.r) =
          (certificate.h : Int) * certificate.r := by
            rw [hhfactor]
            push_cast
            ring
      _ = (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 2 * L := hcrossRaw
      _ = (3 : Int) *
          ((1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 1 * L) := by ring
  obtain ⟨R, hLfactor, hRodd, hrfactor⟩ :=
    outer41ExtractOddPrimeCross 3 1 1 certificate.h0_pos hh0odd
      hLodd (Or.inl rfl) hthreeH0 hcrossReduced
  have hRpos : 0 < R := by
    by_contra hR
    have : R = 0 := Nat.eq_zero_of_not_pos hR
    rw [this, mul_zero] at hLfactor
    omega
  have ht0 : certificate.t0 = (121 : Int) ^ 2 := by
    have ht := certificate.t_factor
    rw [he, hconstants.1] at ht
    norm_num at ht ⊢
    omega
  have hDelta0 : certificate.Delta0 = (1577 : Int) ^ 2 := by
    have hDelta := certificate.Delta_factor
    rw [he, hconstants.2] at hDelta
    norm_num at hDelta ⊢
    omega
  have haL : (121 : Nat).Coprime L := by
    simpa [L, show 1526536 = 12616 * 121 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 121 1882609
        (12616 * j)).mpr (by norm_num)
  have hbL : (1577 : Nat).Coprime L := by
    simpa [L, show 1526536 = 968 * 1577 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 1577 1882609
        (968 * j)).mpr (by norm_num)
  have hRdvdL : R ∣ L := ⟨certificate.h0, by rw [hLfactor]; ring⟩
  have haR : (121 : Nat).Coprime R := haL.of_dvd_right hRdvdL
  have haRInt : Int.gcd ((121 : Int) ^ 2) R = 1 := by
    exact_mod_cast (haR.pow_left 2).gcd_eq_one
  have haH0 : (121 : Nat).Coprime certificate.h0 :=
    haL.of_dvd_right ⟨R, hLfactor⟩
  have hbH0 : (1577 : Nat).Coprime certificate.h0 :=
    hbL.of_dvd_right ⟨R, hLfactor⟩
  have haH0Int : Int.gcd (121 : Int) certificate.h0 = 1 := by
    exact_mod_cast haH0.gcd_eq_one
  have hbH0Int : Int.gcd (1577 : Int) certificate.h0 = 1 := by
    exact_mod_cast hbH0.gcd_eq_one
  have hsecondary :
      jacobiSym certificate.t0 certificate.h0 *
          jacobiSym certificate.Delta0 certificate.h0 = 1 := by
    rw [ht0, hDelta0, jacobiSym.sq_one' haH0Int,
      jacobiSym.sq_one' hbH0Int]
    norm_num
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A36 j) (outer41B36 j)
    (by
      rw [outer41P37Cast, outer41Q37Cast]
      exact outer41Endpoint37 j)
    (by
      rw [outer41P35Cast, outer41Q35Cast]
      exact outer41Delta37 j)
  have hthreeRdvr : ((3 : Int) * R) ∣ certificate.r := by
    refine ⟨(2 : Int) ^ 3, ?_⟩
    rw [hrfactor]
    norm_num
    ring
  have hdualThreeR := hdualRaw.of_dvd hthreeRdvr
  have hdualFactored : Int.ModEq ((3 : Int) * R)
      ((3 : Int) * ((certificate.q0 : Int) * (121 : Int) ^ 2))
      ((3 : Int) * ((certificate.Q0 : Int) * (1577 : Int) ^ 2)) := by
    rw [hconstants.1, hconstants.2] at hdualThreeR
    convert hdualThreeR using 1 <;> ring
  have hendpoint : Int.ModEq R
      ((certificate.q0 : Int) * (121 : Int) ^ 2)
      ((certificate.Q0 : Int) * (1577 : Int) ^ 2) :=
    hdualFactored.mul_left_cancel' (by norm_num)
  have hrfactorTotal : certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (3 * R : Nat) := by
    rw [hrfactor]
    push_cast
    ring
  have hQ0ThreeR : certificate.Q0.Coprime (3 * R) :=
    (outer41FactorCoprime (R := 3 * R) (n := certificate.Q0)
      (w := 3) (s := 1) (Or.inl rfl) hrfactorTotal
      (outer41LocalLink_r_coprime_Q0 certificate
        (outer41RawCoprime37 j))).symm
  have hq0ThreeR : (3 * R).Coprime certificate.q0 :=
    outer41FactorCoprime (R := 3 * R) (n := certificate.q0)
      (w := 3) (s := 1) (Or.inl rfl) hrfactorTotal
      certificate.r_coprime_q0
  have hQ0R : certificate.Q0.Coprime R :=
    hQ0ThreeR.of_dvd_right ⟨3, by ring⟩
  have hthreeQ0 : (3 : Nat).Coprime certificate.Q0 :=
    (hQ0ThreeR.of_dvd_right ⟨R, by ring⟩).symm
  have hthreeq0 : (3 : Nat).Coprime certificate.q0 :=
    hq0ThreeR.of_dvd_left ⟨R, by ring⟩
  have hprime := outer41PrimeExceptionalCrossProduct
    (Q0 := certificate.Q0) (q0 := certificate.q0)
    (h := certificate.h0) (R := R) (L := L)
    (a := 121) (b := 1577) (z := 3)
    (r := certificate.r) (t := (121 : Int) ^ 2)
    (Delta := (1577 : Int) ^ 2)
    3 0 0 0 0 1 1 1 certificate.h0_pos hRpos
    certificate.Q0_odd certificate.q0_odd hRodd hLfactor
    (by simpa using hrfactor) (by norm_num) (by norm_num)
    haL hbL haRInt hQ0R hendpoint
  have hcrossSymbols :
      jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 =
        jacobiSym (-1 : Int) certificate.Q0 *
          jacobiSym 2 certificate.Q0 ^ 3 *
          jacobiSym 2 certificate.q0 ^ 3 *
          jacobiSym (3 : Int) certificate.Q0 *
          jacobiSym (3 : Int) certificate.q0 *
          qrSign certificate.Q0 R * qrSign certificate.q0 R := by
    have hsynthetic :
        jacobiSym ((121 : Int) ^ 2) certificate.h0 *
            jacobiSym ((1577 : Int) ^ 2) certificate.h0 = 1 := by
      rw [jacobiSym.sq_one' haH0Int, jacobiSym.sq_one' hbH0Int]
      norm_num
    have hprime' :
        (jacobiSym ((121 : Int) ^ 2) certificate.h0 *
            jacobiSym ((1577 : Int) ^ 2) certificate.h0) *
            (jacobiSym (-certificate.r) certificate.Q0 *
              jacobiSym certificate.r certificate.q0) =
          jacobiSym (-1 : Int) certificate.Q0 *
            jacobiSym 2 certificate.Q0 ^ 3 *
            jacobiSym 2 certificate.q0 ^ 3 *
            jacobiSym (3 : Int) certificate.Q0 *
            jacobiSym (3 : Int) certificate.q0 *
            qrSign certificate.Q0 R * qrSign certificate.q0 R := by
      calc
        _ = jacobiSym ((121 : Int) ^ 2) certificate.h0 *
              jacobiSym ((1577 : Int) ^ 2) certificate.h0 *
              jacobiSym (-certificate.r) certificate.Q0 *
              jacobiSym certificate.r certificate.q0 := by ring
        _ = _ := by
          rw [hprime]
          simp
    calc
      jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 =
          1 * (jacobiSym (-certificate.r) certificate.Q0 *
            jacobiSym certificate.r certificate.q0) := by ring
      _ = (jacobiSym ((121 : Int) ^ 2) certificate.h0 *
            jacobiSym ((1577 : Int) ^ 2) certificate.h0) *
            (jacobiSym (-certificate.r) certificate.Q0 *
              jacobiSym certificate.r certificate.q0) := by rw [hsynthetic]
      _ = _ := hprime'
  have hraw24 := outer41Q37Q35ModTwentyFour j
  have hraw8 : outer41Q37 j % 8 = outer41Q35 j % 8 := by
    calc
      outer41Q37 j % 8 = (outer41Q37 j % 24) % 8 :=
        (Nat.mod_mod_of_dvd (outer41Q37 j) (by decide : 8 ∣ 24)).symm
      _ = (outer41Q35 j % 24) % 8 := by rw [hraw24]
      _ = outer41Q35 j % 8 :=
        Nat.mod_mod_of_dvd (outer41Q35 j) (by decide : 8 ∣ 24)
  have hhEight : Nat.gcd 8 certificate.h = 1 := by
    have hcop : certificate.h.Coprime (2 ^ 3) :=
      certificate.h_odd.coprime_two_right.pow_right 3
    simpa using hcop.symm.gcd_eq_one
  have hmodEight : certificate.Q0 % 8 = certificate.q0 % 8 :=
    outer41ReducedFactorsModEq certificate.Q_factor certificate.q_factor
      hhEight hraw8
  have hraw9 := outer41Q37Q35ModNine_of_mod_three_zero j hj
  have hmodNine : Nat.ModEq 9 (outer41Q37 j) (outer41Q35 j) := by
    change outer41Q37 j % 9 = outer41Q35 j % 9
    exact hraw9.1.trans hraw9.2.symm
  have hmodNineFactored : Nat.ModEq 9
      (3 * (certificate.h0 * certificate.Q0))
      (3 * (certificate.h0 * certificate.q0)) := by
    simpa [certificate.Q_factor, certificate.q_factor,
      hhfactor, mul_assoc] using hmodNine
  have hmodThreeFactored : Nat.ModEq 3
      (certificate.h0 * certificate.Q0)
      (certificate.h0 * certificate.q0) := by
    simpa using hmodNineFactored.cancel_left_div_gcd (by decide : 0 < 9)
  have hmodThree : certificate.Q0 % 3 = certificate.q0 % 3 := by
    exact hmodThreeFactored.cancel_left_of_coprime hthreeH0.gcd_eq_one
  have hcharacter := outer41ThreePrimePairCharacter
    certificate.Q0_odd certificate.q0_odd hRodd
    hthreeQ0 hthreeq0 hmodEight hmodThree
  have hcharacterCompact :
      qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-1 : Int) certificate.Q0 *
            jacobiSym 2 certificate.Q0 ^ 3 *
            jacobiSym 2 certificate.q0 ^ 3 *
            jacobiSym (3 : Int) certificate.Q0 *
            jacobiSym (3 : Int) certificate.q0 *
            qrSign certificate.Q0 R * qrSign certificate.q0 R) = 1 := by
    simpa only [jacobiSym.one_left, mul_one, mul_assoc] using hcharacter
  have hfactored := outer41FactoredLinkTransfer certificate
  have hprimaryCorrection := outer41Correction37 j
  calc
    jacobiSym (outer41P37 j : Int) (outer41Q37 j) =
        qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (outer41P37 j : Int) certificate.e *
            jacobiSym (outer41P35 j : Int) certificate.e) *
          (jacobiSym certificate.t0 certificate.h0 *
            jacobiSym certificate.Delta0 certificate.h0) *
          jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 *
          jacobiSym (outer41P35 j : Int) (outer41Q35 j) := hfactored
    _ = qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-certificate.r) certificate.Q0 *
            jacobiSym certificate.r certificate.q0) *
          jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
            rw [hprimaryCorrection, hsecondary]
            ring
    _ = 1 * jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
      rw [hcrossSymbols]
      rw [hcharacterCompact]
    _ = _ := one_mul _

private theorem outer41Link35_33 (j : Nat) :
    jacobiSym (outer41P35 j : Int) (outer41Q35 j) =
      jacobiSym (outer41P33 j : Int) (outer41Q33 j) := by
  let certificate := outer41LocalLink35 j
  let L := 15600826093 + 13817666464 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P33 j : Int) * outer41Q35 j -
            (outer41Q33 j : Int) * outer41P35 j := certificate.cross
      _ = outer41P33Int j * outer41Q35Int j -
          outer41Q33Int j * outer41P35Int j := by
            rw [outer41P33Cast, outer41Q35Cast,
              outer41Q33Cast, outer41P35Cast]
      _ = 8 * (15600826093 + 13817666464 * (j : Int)) :=
        outer41PrototypeCross35 j
      _ = (1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 8428693448 ∧
        certificate.Delta = 5663033888 := by
    simp only [certificate, outer41LocalLink35,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 8 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (8 : Nat).Coprime certificate.h := by
        simpa [show (8 : Nat) = 2 ^ 3 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 3
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A34 j) (outer41B34 j)
    (by
      rw [outer41P35Cast, outer41Q35Cast]
      exact outer41PrototypeEndpoint35 j)
    (by
      rw [outer41P33Cast, outer41Q33Cast]
      exact outer41Delta35 j)
  rw [← one_mul (jacobiSym (outer41P33 j : Int) (outer41Q33 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 32459) (b := 13303)
    certificate 3 3 5 1 1 1 (Or.inl rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 13817666464 = 425696 * 32459 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 32459 15600826093
        (425696 * j)).mpr (by norm_num)
  · simpa [L, show 13817666464 = 1038688 * 13303 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 13303 15600826093
        (1038688 * j)).mpr (by norm_num)
  · exact outer41RawCoprime35 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q35 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q35Coeffs
      rw [outer41Q35ModEightCoeffs] at h
      simpa [outer41Q35, outer41HornerNat] using h
    have hqmod : outer41Q33 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q33Coeffs
      rw [outer41Q33ModEightCoeffs] at h
      simpa [outer41Q33, outer41HornerNat] using h
    have hLmod : L % 8 = 5 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 3 3 5 1 1
      (Or.inl rfl) (Or.inl rfl) (outer41Q35Odd j)
      (outer41Q33Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link33_31 (j : Nat) :
    jacobiSym (outer41P33 j : Int) (outer41Q33 j) =
      jacobiSym (outer41P31 j : Int) (outer41Q31 j) := by
  let certificate := outer41LocalLink33 j
  let L := 110774232961 + 93970487244 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * ((2 ^ 5 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P31 j : Int) * outer41Q33 j -
            (outer41Q31 j : Int) * outer41P33 j := certificate.cross
      _ = outer41P31Int j * outer41Q33Int j -
          outer41Q31Int j * outer41P33Int j := by
            rw [outer41P31Cast, outer41Q33Cast,
              outer41Q31Cast, outer41P33Cast]
      _ = 32 * (110774232961 + 93970487244 * (j : Int)) :=
        outer41Cross33 j
      _ = (1 : Int) * ((2 ^ 5 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 31451824818 ∧
        certificate.Delta = 70190303138 := by
    simp only [certificate, outer41LocalLink33,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 2 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · exact certificate.h_odd.coprime_two_right.symm.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A32 j) (outer41B32 j)
    (by
      rw [outer41P33Cast, outer41Q33Cast]
      exact outer41Endpoint33 j)
    (by
      rw [outer41P31Cast, outer41Q31Cast]
      exact outer41Delta33 j)
  rw [← one_mul (jacobiSym (outer41P31 j : Int) (outer41Q31 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 125403) (b := 187337)
    certificate 5 1 1 1 1 1 (Or.inl rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 93970487244 = 749348 * 125403 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 125403 110774232961
        (749348 * j)).mpr (by norm_num)
  · simpa [L, show 93970487244 = 501612 * 187337 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 187337 110774232961
        (501612 * j)).mpr (by norm_num)
  · exact outer41RawCoprime33 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q33 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q33Coeffs
      rw [outer41Q33ModEightCoeffs] at h
      simpa [outer41Q33, outer41HornerNat] using h
    have hqmod : outer41Q31 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q31Coeffs
      rw [outer41Q31ModEightCoeffs] at h
      simpa [outer41Q31, outer41HornerNat] using h
    have hLmod : L % 8 = (1 + 4 * (j % 8)) % 8 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    have hjbound : j % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [outer41OrdinaryRawCharacter 5 1 1 1 1
      (Or.inl rfl) (Or.inl rfl) (outer41Q33Odd j)
      (outer41Q31Odd j) hLodd, hQmod, hqmod, hLmod]
    interval_cases hjcase : j % 8
    all_goals
      norm_num [hjcase, outer41OrdinaryActualResidueSign,
        outer41QrResidueCharacter, outer41UnitResidueCharacter,
        outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link31_29 (j : Nat) :
    jacobiSym (outer41P31 j : Int) (outer41Q31 j) =
      jacobiSym (outer41P29 j : Int) (outer41Q29 j) := by
  let certificate := outer41LocalLink31 j
  let L := 26239191634293 + 19221728294080 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P29 j : Int) * outer41Q31 j -
            (outer41Q29 j : Int) * outer41P31 j := certificate.cross
      _ = outer41P29Int j * outer41Q31Int j -
          outer41Q29Int j * outer41P31Int j := by
            rw [outer41P29Cast, outer41Q31Cast,
              outer41Q29Cast, outer41P31Cast]
      _ = -8 * (26239191634293 + 19221728294080 * (j : Int)) :=
        outer41Cross31 j
      _ = (-1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 1214679324800 ∧
        certificate.Delta = -76043699573192 := by
    simp only [certificate, outer41LocalLink31,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 8 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (8 : Nat).Coprime certificate.h := by
        simpa [show (8 : Nat) = 2 ^ 3 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 3
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A30 j) (outer41B30 j)
    (by
      rw [outer41P31Cast, outer41Q31Cast]
      exact outer41Endpoint31 j)
    (by
      rw [outer41P29Cast, outer41Q29Cast]
      exact outer41Delta31 j)
  rw [← one_mul (jacobiSym (outer41P29 j : Int) (outer41Q29 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 97415) (b := 3083093)
    certificate 3 7 3 (-1) (-1) 1 (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 19221728294080 = 197317952 * 97415 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 97415 26239191634293
        (197317952 * j)).mpr (by norm_num)
  · simpa [L, show 19221728294080 = 6234560 * 3083093 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 3083093 26239191634293
        (6234560 * j)).mpr (by norm_num)
  · exact outer41RawCoprime31 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q31 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q31Coeffs
      rw [outer41Q31ModEightCoeffs] at h
      simpa [outer41Q31, outer41HornerNat] using h
    have hqmod : outer41Q29 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q29Coeffs
      rw [outer41Q29ModEightCoeffs] at h
      simpa [outer41Q29, outer41HornerNat] using h
    have hLmod : L % 8 = 5 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 3 7 3 (-1) (-1)
      (Or.inr rfl) (Or.inr rfl) (outer41Q31Odd j)
      (outer41Q29Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link29_27 (j : Nat) :
    jacobiSym (outer41P29 j : Int) (outer41Q29 j) =
      -jacobiSym (outer41P27 j : Int) (outer41Q27 j) := by
  let certificate := outer41LocalLink29 j
  let L := 26687116983557251 + 24429431808968832 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P27 j : Int) * outer41Q29 j -
            (outer41Q27 j : Int) * outer41P29 j := certificate.cross
      _ = outer41P27Int j * outer41Q29Int j -
          outer41Q27Int j * outer41P29Int j := by
            rw [outer41P27Cast, outer41Q29Cast,
              outer41Q27Cast, outer41P29Cast]
      _ = 4 * (26687116983557251 + 24429431808968832 * (j : Int)) :=
        outer41Cross29 j
      _ = (1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 572738492625408 ∧
        certificate.Delta = -130250792070340516 := by
    simp only [certificate, outer41LocalLink29,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 4 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (4 : Nat).Coprime certificate.h := by
        simpa [show (4 : Nat) = 2 ^ 2 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 2
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A28 j) (outer41B28 j)
    (by
      rw [outer41P29Cast, outer41Q29Cast]
      exact outer41Endpoint29 j)
    (by
      rw [outer41P27Cast, outer41Q27Cast]
      exact outer41Delta29 j)
  rw [show -jacobiSym (outer41P27 j : Int) (outer41Q27 j) =
    (-1 : Int) * jacobiSym (outer41P27 j : Int) (outer41Q27 j) by ring]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 1057653) (b := 180451373)
    certificate 2 9 2 1 (-1) (-1) (Or.inl rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 24429431808968832 = 23097775744 * 1057653 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 1057653 26687116983557251
        (23097775744 * j)).mpr (by norm_num)
  · simpa [L, show 24429431808968832 = 135379584 * 180451373 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 180451373 26687116983557251
        (135379584 * j)).mpr (by norm_num)
  · exact outer41RawCoprime29 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q29 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q29Coeffs
      rw [outer41Q29ModEightCoeffs] at h
      simpa [outer41Q29, outer41HornerNat] using h
    have hqmod : outer41Q27 j % 8 = 3 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q27Coeffs
      rw [outer41Q27ModEightCoeffs] at h
      simpa [outer41Q27, outer41HornerNat] using h
    have hLmod : L % 8 = 3 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 2 9 2 1 (-1)
      (Or.inl rfl) (Or.inr rfl) (outer41Q29Odd j)
      (outer41Q27Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link27_25 (j : Nat) :
    jacobiSym (outer41P27 j : Int) (outer41Q27 j) =
      jacobiSym (outer41P25 j : Int) (outer41Q25 j) := by
  let certificate := outer41LocalLink27 j
  let L := 175484751704606747 + 121551398698394784 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 12 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P25 j : Int) * outer41Q27 j -
            (outer41Q25 j : Int) * outer41P27 j := certificate.cross
      _ = outer41P25Int j * outer41Q27Int j -
          outer41Q25Int j * outer41P27Int j := by
            rw [outer41P25Cast, outer41Q27Cast,
              outer41Q25Cast, outer41P27Cast]
      _ = -4096 * (175484751704606747 + 121551398698394784 * (j : Int)) :=
        outer41Cross27 j
      _ = (-1 : Int) * ((2 ^ 12 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 44929151108448768 ∧
        certificate.Delta = -84184410193007063552 := by
    simp only [certificate, outer41LocalLink27,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 512 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (512 : Nat).Coprime certificate.h := by
        simpa [show (512 : Nat) = 2 ^ 9 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 9
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A26 j) (outer41B26 j)
    (by
      rw [outer41P27Cast, outer41Q27Cast]
      exact outer41Endpoint27 j)
    (by
      rw [outer41P25Cast, outer41Q25Cast]
      exact outer41Delta27 j)
  rw [← one_mul (jacobiSym (outer41P25 j : Int) (outer41Q25 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 9367617) (b := 405490661)
    certificate 12 9 9 (-1) (-1) 1 (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 121551398698394784 = 12975701152 * 9367617 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 9367617 175484751704606747
        (12975701152 * j)).mpr (by norm_num)
  · simpa [L, show 121551398698394784 = 299763744 * 405490661 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 405490661 175484751704606747
        (299763744 * j)).mpr (by norm_num)
  · exact outer41RawCoprime27 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q27 j % 8 = 3 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q27Coeffs
      rw [outer41Q27ModEightCoeffs] at h
      simpa [outer41Q27, outer41HornerNat] using h
    have hqmod : outer41Q25 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q25Coeffs
      rw [outer41Q25ModEightCoeffs] at h
      simpa [outer41Q25, outer41HornerNat] using h
    have hLmod : L % 8 = 3 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 12 9 9 (-1) (-1)
      (Or.inr rfl) (Or.inr rfl) (outer41Q27Odd j)
      (outer41Q25Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link17_15 (j : Nat) :
    jacobiSym (outer41P17 j : Int) (outer41Q17 j) =
      -jacobiSym (outer41P15 j : Int) (outer41Q15 j) := by
  let certificate := outer41LocalLink17 j
  let L := 3193003805885964223 + 3716001312460335600 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P15 j : Int) * outer41Q17 j -
            (outer41Q15 j : Int) * outer41P17 j := certificate.cross
      _ = outer41P15Int j * outer41Q17Int j -
          outer41Q15Int j * outer41P17Int j := by
            rw [outer41P15Cast, outer41Q17Cast,
              outer41Q15Cast, outer41P17Cast]
      _ = 8 * (3193003805885964223 + 3716001312460335600 * (j : Int)) :=
        outer41Cross17 j
      _ = (1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 29853776087536915396 ∧
        certificate.Delta = 28908959694322500 := by
    simp only [certificate, outer41LocalLink17,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 4 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (4 : Nat).Coprime certificate.h := by
        simpa [show (4 : Nat) = 2 ^ 2 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 2
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A16 j) (outer41B16 j)
    (by
      rw [outer41P17Cast, outer41Q17Cast]
      exact outer41Endpoint17 j)
    (by
      rw [outer41P15Cast, outer41Q15Cast]
      exact outer41Delta17 j)
  rw [show -jacobiSym (outer41P15 j : Int) (outer41Q15 j) =
    (-1 : Int) * jacobiSym (outer41P15 j : Int) (outer41Q15 j) by ring]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 2731930457) (b := 85013175)
    certificate 3 2 2 1 1 (-1) (Or.inl rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 3716001312460335600 = 1360210800 * 2731930457 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 2731930457 3193003805885964223
        (1360210800 * j)).mpr (by norm_num)
  · simpa [L, show 3716001312460335600 = 43710887312 * 85013175 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 85013175 3193003805885964223
        (43710887312 * j)).mpr (by norm_num)
  · exact outer41RawCoprime17 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q17 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q17Coeffs
      rw [outer41Q17ModEightCoeffs] at h
      simpa [outer41Q17, outer41HornerNat] using h
    have hqmod : outer41Q15 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q15Coeffs
      rw [outer41Q15ModEightCoeffs] at h
      simpa [outer41Q15, outer41HornerNat] using h
    have hLmod : L % 8 = 7 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 3 2 2 1 1
      (Or.inl rfl) (Or.inl rfl) (outer41Q17Odd j)
      (outer41Q15Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link15_13 (j : Nat) :
    jacobiSym (outer41P15 j : Int) (outer41Q15 j) =
      jacobiSym (outer41P13 j : Int) (outer41Q13 j) := by
  let certificate := outer41LocalLink15 j
  let L := 243248593617877651 + 168192744940246176 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P13 j : Int) * outer41Q15 j -
            (outer41Q13 j : Int) * outer41P15 j := certificate.cross
      _ = outer41P13Int j * outer41Q15Int j -
          outer41Q13Int j * outer41P15Int j := by
            rw [outer41P13Cast, outer41Q15Cast,
              outer41Q13Cast, outer41P15Cast]
      _ = -8 * (243248593617877651 + 168192744940246176 * (j : Int)) :=
        outer41Cross15 j
      _ = (-1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 46319273757209672 ∧
        certificate.Delta = -305367476170019904 := by
    simp only [certificate, outer41LocalLink15,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 8 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (8 : Nat).Coprime certificate.h := by
        simpa [show (8 : Nat) = 2 ^ 3 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 3
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A14 j) (outer41B14 j)
    (by
      rw [outer41P15Cast, outer41Q15Cast]
      exact outer41Endpoint15 j)
    (by
      rw [outer41P13Cast, outer41Q13Cast]
      exact outer41Delta15 j)
  rw [← one_mul (jacobiSym (outer41P13 j : Int) (outer41Q13 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 76091453) (b := 69075081)
    certificate 3 3 6 (-1) (-1) 1 (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 168192744940246176 = 2210402592 * 76091453 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 76091453 243248593617877651
        (2210402592 * j)).mpr (by norm_num)
  · simpa [L, show 168192744940246176 = 2434926496 * 69075081 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 69075081 243248593617877651
        (2434926496 * j)).mpr (by norm_num)
  · exact outer41RawCoprime15 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q15 j % 8 = 5 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q15Coeffs
      rw [outer41Q15ModEightCoeffs] at h
      simpa [outer41Q15, outer41HornerNat] using h
    have hqmod : outer41Q13 j % 8 = 3 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q13Coeffs
      rw [outer41Q13ModEightCoeffs] at h
      simpa [outer41Q13, outer41HornerNat] using h
    have hLmod : L % 8 = 3 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 3 3 6 (-1) (-1)
      (Or.inr rfl) (Or.inr rfl) (outer41Q15Odd j)
      (outer41Q13Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link13_11 (j : Nat) :
    jacobiSym (outer41P13 j : Int) (outer41Q13 j) =
      jacobiSym (outer41P11 j : Int) (outer41Q11 j) := by
  let certificate := outer41LocalLink13 j
  let L := 71706996737709405 + 61978941399989824 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P11 j : Int) * outer41Q13 j -
            (outer41Q11 j : Int) * outer41P13 j := certificate.cross
      _ = outer41P11Int j * outer41Q13Int j -
          outer41Q11Int j * outer41P13Int j := by
            rw [outer41P11Cast, outer41Q13Cast,
              outer41Q11Cast, outer41P13Cast]
      _ = -4 * (71706996737709405 + 61978941399989824 * (j : Int)) :=
        outer41Cross13 j
      _ = (-1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 23776391613186304 ∧
        certificate.Delta = 40390792256855236 := by
    simp only [certificate, outer41LocalLink13,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 4 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (4 : Nat).Coprime certificate.h := by
        simpa [show (4 : Nat) = 2 ^ 2 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 2
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A12 j) (outer41B12 j)
    (by
      rw [outer41P13Cast, outer41Q13Cast]
      exact outer41Endpoint13 j)
    (by
      rw [outer41P11Cast, outer41Q11Cast]
      exact outer41Delta13 j)
  rw [← one_mul (jacobiSym (outer41P11 j : Int) (outer41Q11 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 9637247) (b := 100487303)
    certificate 2 8 2 (-1) 1 1 (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 61978941399989824 = 6431187392 * 9637247 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 9637247 71706996737709405
        (6431187392 * j)).mpr (by norm_num)
  · simpa [L, show 61978941399989824 = 616783808 * 100487303 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 100487303 71706996737709405
        (616783808 * j)).mpr (by norm_num)
  · exact outer41RawCoprime13 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q13 j % 8 = 3 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q13Coeffs
      rw [outer41Q13ModEightCoeffs] at h
      simpa [outer41Q13, outer41HornerNat] using h
    have hqmod : outer41Q11 j % 8 = 3 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q11Coeffs
      rw [outer41Q11ModEightCoeffs] at h
      simpa [outer41Q11, outer41HornerNat] using h
    have hLmod : L % 8 = 5 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 2 8 2 (-1) 1
      (Or.inr rfl) (Or.inl rfl) (outer41Q13Odd j)
      (outer41Q11Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link9_7 (j : Nat) :
    jacobiSym (outer41P9 j : Int) (outer41Q9 j) =
      jacobiSym (outer41P7 j : Int) (outer41Q7 j) := by
  let certificate := outer41LocalLink9 j
  let L := 23334013696969 + 20235218897412 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 4 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P7 j : Int) * outer41Q9 j -
            (outer41Q7 j : Int) * outer41P9 j := certificate.cross
      _ = outer41P7Int j * outer41Q9Int j -
          outer41Q7Int j * outer41P9Int j := by
            rw [outer41P7Cast, outer41Q9Cast,
              outer41Q7Cast, outer41P9Cast]
      _ = -16 * (23334013696969 + 20235218897412 * (j : Int)) :=
        outer41Cross9 j
      _ = (-1 : Int) * ((2 ^ 4 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 40985168665156 ∧
        certificate.Delta = 9990542851524 := by
    simp only [certificate, outer41LocalLink9,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 4 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (4 : Nat).Coprime certificate.h := by
        simpa [show (4 : Nat) = 2 ^ 2 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 2
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A8 j) (outer41B8 j)
    (by
      rw [outer41P9Cast, outer41Q9Cast]
      exact outer41Endpoint9 j)
    (by
      rw [outer41P7Cast, outer41Q7Cast]
      exact outer41Delta9 j)
  rw [← one_mul (jacobiSym (outer41P7 j : Int) (outer41Q7 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 3200983) (b := 1580391)
    certificate 4 2 2 (-1) 1 1 (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 20235218897412 = 6321564 * 3200983 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 3200983 23334013696969
        (6321564 * j)).mpr (by norm_num)
  · simpa [L, show 20235218897412 = 12803932 * 1580391 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 1580391 23334013696969
        (12803932 * j)).mpr (by norm_num)
  · exact outer41RawCoprime9 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q9 j % 8 = 3 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q9Coeffs
      rw [outer41Q9ModEightCoeffs] at h
      simpa [outer41Q9, outer41HornerNat] using h
    have hqmod : outer41Q7 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q7Coeffs
      rw [outer41Q7ModEightCoeffs] at h
      simpa [outer41Q7, outer41HornerNat] using h
    have hLmod : L % 8 = (1 + 4 * (j % 8)) % 8 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    have hjbound : j % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [outer41OrdinaryRawCharacter 4 2 2 (-1) 1
      (Or.inr rfl) (Or.inl rfl) (outer41Q9Odd j)
      (outer41Q7Odd j) hLodd, hQmod, hqmod, hLmod]
    interval_cases hjcase : j % 8
    all_goals
      norm_num [hjcase, outer41OrdinaryActualResidueSign,
        outer41QrResidueCharacter, outer41UnitResidueCharacter,
        outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link7_5 (j : Nat) :
    jacobiSym (outer41P7 j : Int) (outer41Q7 j) =
      jacobiSym (outer41P5 j : Int) (outer41Q5 j) := by
  let certificate := outer41LocalLink7 j
  let L := 27556392420649 + 22143385463360 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P5 j : Int) * outer41Q7 j -
            (outer41Q5 j : Int) * outer41P7 j := certificate.cross
      _ = outer41P5Int j * outer41Q7Int j -
          outer41Q5Int j * outer41P7Int j := by
            rw [outer41P5Cast, outer41Q7Cast,
              outer41Q5Cast, outer41P7Cast]
      _ = -4 * (27556392420649 + 22143385463360 * (j : Int)) :=
        outer41Cross7 j
      _ = (-1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 25222271863684 ∧
        certificate.Delta = 607510599200 := by
    simp only [certificate, outer41LocalLink7,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 4 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (4 : Nat).Coprime certificate.h := by
        simpa [show (4 : Nat) = 2 ^ 2 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 2
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A6 j) (outer41B6 j)
    (by
      rw [outer41P7Cast, outer41Q7Cast]
      exact outer41Endpoint7 j)
    (by
      rw [outer41P5Cast, outer41Q5Cast]
      exact outer41Delta7 j)
  rw [← one_mul (jacobiSym (outer41P5 j : Int) (outer41Q5 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 2511089) (b := 137785)
    certificate 2 2 5 (-1) 1 1 (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 22143385463360 = 8818240 * 2511089 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 2511089 27556392420649
        (8818240 * j)).mpr (by norm_num)
  · simpa [L, show 22143385463360 = 160709696 * 137785 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 137785 27556392420649
        (160709696 * j)).mpr (by norm_num)
  · exact outer41RawCoprime7 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q7 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q7Coeffs
      rw [outer41Q7ModEightCoeffs] at h
      simpa [outer41Q7, outer41HornerNat] using h
    have hqmod : outer41Q5 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q5Coeffs
      rw [outer41Q5ModEightCoeffs] at h
      simpa [outer41Q5, outer41HornerNat] using h
    have hLmod : L % 8 = 1 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 2 2 5 (-1) 1
      (Or.inr rfl) (Or.inl rfl) (outer41Q7Odd j)
      (outer41Q5Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link5_3 (j : Nat) :
    jacobiSym (outer41P5 j : Int) (outer41Q5 j) =
      jacobiSym (outer41P3 j : Int) (outer41Q3 j) := by
  let certificate := outer41LocalLink5 j
  let L := 37105198175 + 28386803664 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P3 j : Int) * outer41Q5 j -
            (outer41Q3 j : Int) * outer41P5 j := certificate.cross
      _ = outer41P3Int j * outer41Q5Int j -
          outer41Q3Int j * outer41P5Int j := by
            rw [outer41P3Cast, outer41Q5Cast,
              outer41Q3Cast, outer41P5Cast]
      _ = -4 * (37105198175 + 28386803664 * (j : Int)) :=
        outer41Cross5 j
      _ = (-1 : Int) * ((2 ^ 2 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 204790641444 ∧
        certificate.Delta = 983700496 := by
    simp only [certificate, outer41LocalLink5,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 4 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (4 : Nat).Coprime certificate.h := by
        simpa [show (4 : Nat) = 2 ^ 2 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 2
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A4 j) (outer41B4 j)
    (by
      rw [outer41P5Cast, outer41Q5Cast]
      exact outer41Endpoint5 j)
    (by
      rw [outer41P3Cast, outer41Q3Cast]
      exact outer41Delta5 j)
  rw [← one_mul (jacobiSym (outer41P3 j : Int) (outer41Q3 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 226269) (b := 7841)
    certificate 2 2 4 (-1) 1 1 (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 28386803664 = 125456 * 226269 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 226269 37105198175
        (125456 * j)).mpr (by norm_num)
  · simpa [L, show 28386803664 = 3620304 * 7841 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 7841 37105198175
        (3620304 * j)).mpr (by norm_num)
  · exact outer41RawCoprime5 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q5 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q5Coeffs
      rw [outer41Q5ModEightCoeffs] at h
      simpa [outer41Q5, outer41HornerNat] using h
    have hqmod : outer41Q3 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q3Coeffs
      rw [outer41Q3ModEightCoeffs] at h
      simpa [outer41Q3, outer41HornerNat] using h
    have hLmod : L % 8 = 7 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    rw [outer41OrdinaryRawCharacter 2 2 4 (-1) 1
      (Or.inr rfl) (Or.inl rfl) (outer41Q5Odd j)
      (outer41Q3Odd j) hLodd, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link21_19 (j : Nat) :
    jacobiSym (outer41P21 j : Int) (outer41Q21 j) =
      jacobiSym (outer41P19 j : Int) (outer41Q19 j) := by
  let certificate := outer41LocalLink21 j
  let L := 399192379747426605583 + 300429181725568050396 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P19 j : Int) * outer41Q21 j -
            (outer41Q19 j : Int) * outer41P21 j := certificate.cross
      _ = outer41P19Int j * outer41Q21Int j -
          outer41Q19Int j * outer41P21Int j := by
            rw [outer41P19Cast, outer41Q21Cast,
              outer41Q19Cast, outer41P21Cast]
      _ = 8 * (399192379747426605583 + 300429181725568050396 * (j : Int)) :=
        outer41Cross21 j
      _ = (1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 20310724547543276059208 ∧
        certificate.Delta = 35550752715303478416 := by
    simp only [certificate, outer41LocalLink21,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 8 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (8 : Nat).Coprime certificate.h := by
        simpa [show (8 : Nat) = 2 ^ 3 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 3
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A20 j) (outer41B20 j)
    (by
      rw [outer41P21Cast, outer41Q21Cast]
      exact outer41Endpoint21 j)
    (by
      rw [outer41P19Cast, outer41Q19Cast]
      exact outer41Delta21 j)
  rw [← one_mul (jacobiSym (outer41P19 j : Int) (outer41Q19 j))]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 50386908701) (b := 1490611299)
    certificate 3 3 4 1 1 1 (Or.inl rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 300429181725568050396 = 5962445196 * 50386908701 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 50386908701 399192379747426605583
        (5962445196 * j)).mpr (by norm_num)
  · simpa [L, show 300429181725568050396 = 201547634804 * 1490611299 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 1490611299 399192379747426605583
        (201547634804 * j)).mpr (by norm_num)
  · exact outer41RawCoprime21 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q21 j % 8 = 3 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q21Coeffs
      rw [outer41Q21ModEightCoeffs] at h
      simpa [outer41Q21, outer41HornerNat] using h
    have hqmod : outer41Q19 j % 8 = (5 + (j % 8) * 4) % 8 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q19Coeffs
      rw [outer41Q19ModEightCoeffs] at h
      simpa [outer41Q19, outer41HornerNat, Nat.add_mod, Nat.mul_mod] using h
    have hLmod : L % 8 = (7 + 4 * (j % 8)) % 8 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    have hjbound : j % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [outer41OrdinaryRawCharacter 3 3 4 1 1
      (Or.inl rfl) (Or.inl rfl) (outer41Q21Odd j)
      (outer41Q19Odd j) hLodd, hQmod, hqmod, hLmod]
    interval_cases hjcase : j % 8
    all_goals
      norm_num [hjcase, outer41OrdinaryActualResidueSign,
        outer41QrResidueCharacter, outer41UnitResidueCharacter,
        outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

private theorem outer41Link19_17 (j : Nat) :
    jacobiSym (outer41P19 j : Int) (outer41Q19 j) =
      -jacobiSym (outer41P17 j : Int) (outer41Q17 j) := by
  let certificate := outer41LocalLink19 j
  let L := 1132158241775475559 + 780039964124394844 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLpos : 0 < L := by omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (-1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P17 j : Int) * outer41Q19 j -
            (outer41Q17 j : Int) * outer41P19 j := certificate.cross
      _ = outer41P17Int j * outer41Q19Int j -
          outer41Q17Int j * outer41P19Int j := by
            rw [outer41P17Cast, outer41Q19Cast,
              outer41Q17Cast, outer41P19Cast]
      _ = -8 * (1132158241775475559 + 780039964124394844 * (j : Int)) :=
        outer41Cross19 j
      _ = (-1 : Int) * ((2 ^ 3 : Nat) : Int) * L := by
        dsimp [L]
  have hconstants :
      certificate.t = 829924053674808976 ∧
        certificate.Delta = 5865233985562754888 := by
    simp only [certificate, outer41LocalLink19,
      outer41LocalLinkCertificate_of_endpoint]
    simp
  have he : certificate.e = 1 := by
    apply outer41LocalLink_e_eq_capped certificate 8 1
    · rw [hconstants.1, hconstants.2]
      norm_num
    · have hcop : (8 : Nat).Coprime certificate.h := by
        simpa [show (8 : Nat) = 2 ^ 3 by decide] using
          certificate.h_odd.coprime_two_right.symm.pow_left 3
      exact hcop.gcd_eq_one
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A18 j) (outer41B18 j)
    (by
      rw [outer41P19Cast, outer41Q19Cast]
      exact outer41Endpoint19 j)
    (by
      rw [outer41P17Cast, outer41Q17Cast]
      exact outer41Delta19 j)
  rw [show -jacobiSym (outer41P17 j : Int) (outer41Q17 j) =
    (-1 : Int) * jacobiSym (outer41P17 j : Int) (outer41Q17 j) by ring]
  apply outer41OrdinaryLinkFromRaw (L := L) (a := 227750419) (b := 856244269)
    certificate 3 4 3 (-1) 1 (-1) (Or.inr rfl) he hLpos hLodd hcrossRaw
  · rw [hconstants.1]
    norm_num
  · rw [hconstants.2]
    norm_num
  · simpa [L, show 780039964124394844 = 3424977076 * 227750419 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 227750419 1132158241775475559
        (3424977076 * j)).mpr (by norm_num)
  · simpa [L, show 780039964124394844 = 911001676 * 856244269 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 856244269 1132158241775475559
        (911001676 * j)).mpr (by norm_num)
  · exact outer41RawCoprime19 j
  · exact hdualRaw
  ·
    have hQmod : outer41Q19 j % 8 = (5 + (j % 8) * 4) % 8 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q19Coeffs
      rw [outer41Q19ModEightCoeffs] at h
      simpa [outer41Q19, outer41HornerNat, Nat.add_mod, Nat.mul_mod] using h
    have hqmod : outer41Q17 j % 8 = 7 := by
      have h := outer41HornerNat_map_mod j 8 outer41Q17Coeffs
      rw [outer41Q17ModEightCoeffs] at h
      simpa [outer41Q17, outer41HornerNat] using h
    have hLmod : L % 8 = (7 + 4 * (j % 8)) % 8 := by
      norm_num [L, Nat.add_mod, Nat.mul_mod]
    have hjbound : j % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [outer41OrdinaryRawCharacter 3 4 3 (-1) 1
      (Or.inr rfl) (Or.inl rfl) (outer41Q19Odd j)
      (outer41Q17Odd j) hLodd, hQmod, hqmod, hLmod]
    interval_cases hjcase : j % 8
    all_goals
      norm_num [hjcase, outer41OrdinaryActualResidueSign,
        outer41QrResidueCharacter, outer41UnitResidueCharacter,
        outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

set_option maxHeartbeats 2000000 in
private theorem outer41Link3_1 (j : Nat) :
    jacobiSym (outer41P3 j : Int) (outer41Q3 j) =
      -jacobiSym (outer41P1 j : Int) (outer41Q1 j) := by
  let L := 79613 + 61776 * j
  have hLpos : 0 < L := by omega
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLmod4 : L % 4 = 1 := by
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hPfactor : outer41P3 j = 27 * L := by
    simp [outer41P3, outer41P3Coeffs, outer41HornerNat, L]
    ring
  have hendpoint :
      (4563 : Int) * outer41Q3 j + outer41B2 j * (27 * L) = 4234032 := by
    calc
      (4563 : Int) * outer41Q3 j + outer41B2 j * (27 * L) =
          outer41A2 j * outer41Q3Int j +
            outer41B2 j * outer41P3Int j := by
              rw [← outer41Q3Cast, ← outer41P3Cast, hPfactor]
              simp [outer41A2, outer41A2Coeffs, outer41HornerInt]
      _ = 4234032 := outer41Endpoint3 j
  have hquotient :
      (169 : Int) * outer41Q3 j + outer41B2 j * L = 156816 := by
    apply mul_left_cancel₀ (show (27 : Int) ≠ 0 by norm_num)
    calc
      (27 : Int) * ((169 : Int) * outer41Q3 j + outer41B2 j * L) =
          (4563 : Int) * outer41Q3 j + outer41B2 j * (27 * L) := by ring
      _ = 4234032 := hendpoint
      _ = (27 : Int) * 156816 := by norm_num
  have hmod : Int.ModEq L ((169 : Int) * outer41Q3 j) 156816 := by
    rw [Int.modEq_iff_dvd]
    use outer41B2 j
    calc
      (156816 : Int) - 169 * outer41Q3 j = outer41B2 j * L := by
        linarith
      _ = (L : Int) * outer41B2 j := by ring
  have h13L : (13 : Nat).Coprime L := by
    simpa [L, show 61776 = 4752 * 13 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 13 79613 (4752 * j)).mpr
        (by norm_num)
  have h396L : (396 : Nat).Coprime L := by
    simpa [L, show 61776 = 156 * 396 by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right 396 79613 (156 * j)).mpr
        (by norm_num)
  have h13LInt : Int.gcd (13 : Int) L = 1 := by
    exact_mod_cast h13L.gcd_eq_one
  have h396LInt : Int.gcd (396 : Int) L = 1 := by
    exact_mod_cast h396L.gcd_eq_one
  have h169 : jacobiSym (169 : Int) L = 1 := by
    rw [show (169 : Int) = 13 ^ 2 by norm_num]
    exact jacobiSym.sq_one' h13LInt
  have h156816 : jacobiSym (156816 : Int) L = 1 := by
    rw [show (156816 : Int) = 396 ^ 2 by norm_num]
    exact jacobiSym.sq_one' h396LInt
  have hQL : jacobiSym (outer41Q3 j : Int) L = 1 := by
    have hsymbols := jacobiSym.mod_left' hmod.eq
    rw [jacobiSym.mul_left, h169, one_mul, h156816] at hsymbols
    exact hsymbols
  have hLQ : jacobiSym (L : Int) (outer41Q3 j) = 1 := by
    rw [jacobiSym.quadratic_reciprocity' hLodd (outer41Q3Odd j),
      outer41_qrSign_right_one (outer41Q3Odd j) hLodd hLmod4,
      one_mul, hQL]
  have hQmod3 : outer41Q3 j % 3 = 1 := by
    norm_num [outer41Q3, outer41Q3Coeffs, outer41HornerNat,
      Nat.add_mod, Nat.mul_mod]
  have hQmod4 : outer41Q3 j % 4 = 3 := by
    norm_num [outer41Q3, outer41Q3Coeffs, outer41HornerNat,
      Nat.add_mod, Nat.mul_mod]
  have hQThree : jacobiSym (outer41Q3 j : Int) 3 = 1 := by
    rw [outer41JacobiNat_mod (outer41Q3 j) 3, hQmod3]
    norm_num
  have hThree : jacobiSym (3 : Int) (outer41Q3 j) = -1 := by
    change jacobiSym ((3 : Nat) : Int) (outer41Q3 j) = -1
    rw [jacobiSym.quadratic_reciprocity' (by decide : Odd 3) (outer41Q3Odd j),
      outer41_qrSign_both_three hQmod4 (by decide : 3 % 4 = 3),
      hQThree]
    norm_num
  have hTwentySeven : jacobiSym (27 : Int) (outer41Q3 j) = -1 := by
    rw [show (27 : Int) = 3 ^ 3 by norm_num, jacobiSym.pow_left, hThree]
    norm_num
  calc
    jacobiSym (outer41P3 j : Int) (outer41Q3 j) =
        jacobiSym ((27 * L : Nat) : Int) (outer41Q3 j) := by rw [hPfactor]
    _ = jacobiSym (27 : Int) (outer41Q3 j) *
        jacobiSym (L : Int) (outer41Q3 j) := by
          rw [Nat.cast_mul]
          norm_num
          rw [jacobiSym.mul_left]
    _ = -1 := by rw [hTwentySeven, hLQ]; norm_num
    _ = -jacobiSym (outer41P1 j : Int) (outer41Q1 j) := by
      simp [outer41P1, outer41P1Coeffs, outer41Q1, outer41Q1Coeffs,
        outer41HornerNat]

set_option maxHeartbeats 1000000 in
private theorem outer41Constants23 (j : Nat) :
    (outer41LocalLink23 j).t =
        (if j % 13 = 12 then 306162648197817255968
        else 3980114426571624327584) ∧
      (outer41LocalLink23 j).Delta =
        -1193619024076561249467528 := by
  simp only [outer41LocalLink23,
    outer41LocalLinkCertificate_of_endpoint]
  simp

private theorem outer41E23 (j : Nat) :
    (outer41LocalLink23 j).e = 1 := by
  let certificate := outer41LocalLink23 j
  have hetInt : (certificate.e : Int) ∣ certificate.t :=
    ⟨certificate.t0, certificate.t_factor⟩
  have heDeltaInt : (certificate.e : Int) ∣ certificate.Delta :=
    ⟨certificate.Delta0, certificate.Delta_factor⟩
  have het : certificate.e ∣ certificate.t.natAbs :=
    Int.natCast_dvd.mp hetInt
  have heDelta : certificate.e ∣ certificate.Delta.natAbs :=
    Int.natCast_dvd.mp heDeltaInt
  have heEight : certificate.e ∣ 8 := by
    by_cases hj : j % 13 = 12
    · have ht : certificate.t = 306162648197817255968 := by
        simpa [certificate, hj] using (outer41Constants23 j).1
      have hDelta : certificate.Delta =
          -1193619024076561249467528 := by
        simpa [certificate] using (outer41Constants23 j).2
      rw [ht] at het
      rw [hDelta] at heDelta
      norm_num at het heDelta ⊢
      exact Nat.dvd_gcd het heDelta
    · have ht : certificate.t = 3980114426571624327584 := by
        simpa [certificate, hj] using (outer41Constants23 j).1
      have hDelta : certificate.Delta =
          -1193619024076561249467528 := by
        simpa [certificate] using (outer41Constants23 j).2
      rw [ht] at het
      rw [hDelta] at heDelta
      norm_num at het heDelta ⊢
      exact Nat.dvd_gcd het heDelta
  have heCoprimeEight : certificate.e.Coprime 8 := by
    simpa [show (8 : Nat) = 2 ^ 3 by decide] using
      certificate.e_odd.coprime_two_right.pow_right 3
  exact heCoprimeEight.eq_one_of_dvd heEight

private theorem outer41JacobiThirteenL25 (j : Nat) :
    jacobiSym (13 : Int)
        (91370185007570122207 + 76509722917161697392 * j) =
      -jacobiSym (j + 1 : Nat) 13 := by
  let L := 91370185007570122207 + 76509722917161697392 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLmod : Int.ModEq 13 (L : Int)
      (8 * ((j + 1 : Nat) : Int)) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(7028475769813086323 +
      5885363301320130568 * (j : Int)), ?_⟩
    dsimp [L]
    ring
  have hsymbol : jacobiSym (L : Int) 13 =
      jacobiSym (8 * ((j + 1 : Nat) : Int)) 13 :=
    jacobiSym.mod_left' hLmod
  change jacobiSym (((13 : Nat) : Int)) L =
    -jacobiSym (j + 1 : Nat) 13
  rw [jacobiSym.quadratic_reciprocity_one_mod_four
      (by decide : 13 % 4 = 1) hLodd,
    hsymbol, jacobiSym.mul_left]
  norm_num

private theorem outer41JacobiThirteenL23 (j : Nat) :
    jacobiSym (13 : Int)
        (49817377110831005331401 + 38233051740637926057696 * j) =
      -jacobiSym (j + 1 : Nat) 13 := by
  let L := 49817377110831005331401 + 38233051740637926057696 * j
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, Nat.add_mod, Nat.mul_mod]
  have hLmod : Int.ModEq 13 (L : Int)
      (5 * ((j + 1 : Nat) : Int)) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(3832105931602385025492 +
      2941003980049071235207 * (j : Int)), ?_⟩
    dsimp [L]
    ring
  have hsymbol : jacobiSym (L : Int) 13 =
      jacobiSym (5 * ((j + 1 : Nat) : Int)) 13 :=
    jacobiSym.mod_left' hLmod
  change jacobiSym (((13 : Nat) : Int)) L =
    -jacobiSym (j + 1 : Nat) 13
  rw [jacobiSym.quadratic_reciprocity_one_mod_four
      (by decide : 13 % 4 = 1) hLodd,
    hsymbol, jacobiSym.mul_left]
  norm_num

/-- The exact exceptional multiplier across the divided coefficient-23
position.  It is one on the factor-13 class and the pinned off-class symbol
elsewhere. -/
def ss41_factor13Multiplier (j : Nat) : Int :=
  if j % 13 = 12 then 1 else jacobiSym (j + 1 : Nat) 13

private theorem outer41L23CoprimeThirteen
    (j : Nat) (hj : j % 13 ≠ 12) :
    (13 : Nat).Coprime
      (49817377110831005331401 + 38233051740637926057696 * j) := by
  rw [(by norm_num : Nat.Prime 13).coprime_iff_not_dvd,
    Nat.dvd_iff_mod_eq_zero]
  intro hzero
  have hlinear :
      (49817377110831005331401 + 38233051740637926057696 * j) % 13 =
        (5 + 5 * (j % 13)) % 13 := by
    norm_num [Nat.add_mod, Nat.mul_mod]
  rw [hlinear] at hzero
  have hjbound : j % 13 < 13 := Nat.mod_lt _ (by decide)
  omega

private def outer41Link23L (j : Nat) : Nat :=
  49817377110831005331401 + 38233051740637926057696 * j

private def outer41Link23A : Nat := 10639 * 290737

private def outer41Link23B : Nat := 3 * 306749 * 419743

private structure Outer41Link23FactorData (j : Nat) where
  R : Nat
  R_pos : 0 < R
  R_odd : Odd R
  L_factor :
    outer41Link23L j = (outer41LocalLink23 j).h0 * R
  r_factor :
    (outer41LocalLink23 j).r =
      (1 : Int) * (2 : Int) ^ 3 * (13 : Int) ^ 0 * R

set_option maxHeartbeats 500000 in
private noncomputable def outer41Link23FactorData
    (j : Nat) (hj : j % 13 ≠ 12) : Outer41Link23FactorData j := by
  let certificate := outer41LocalLink23 j
  let L := outer41Link23L j
  have hLpos : 0 < L := by
    simp [L, outer41Link23L]
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, outer41Link23L, Nat.add_mod, Nat.mul_mod]
  have he : certificate.e = 1 := by
    simpa [certificate] using outer41E23 j
  have hh0 : certificate.h0 = certificate.h := by
    have hfactor := certificate.h_factor
    rw [he] at hfactor
    omega
  have hcrossRaw : (certificate.h : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * L := by
    calc
      (certificate.h : Int) * certificate.r =
          (outer41P21 j : Int) * outer41ReducedQ23 j -
            (outer41Q21 j : Int) * outer41ReducedP23 j := certificate.cross
      _ = outer41P21Int j * outer41Q23Int j -
          outer41Q21Int j * outer41P23Int j := by
        rw [outer41P21Cast, outer41Q21Cast,
          outer41ReducedP23Cast, outer41ReducedQ23Cast]
        simp [hj]
      _ = 8 * (49817377110831005331401 +
          38233051740637926057696 * (j : Int)) := outer41Cross23 j
      _ = (1 : Int) * (2 : Int) ^ 3 * L := by
        simp [L, outer41Link23L]
  have hexists :=
    outer41ExtractOddCross 3 1 certificate.h_pos certificate.h_odd
      hLodd (Or.inl rfl) hcrossRaw
  let R := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  have hLfactorH : L = certificate.h * R := hspec.1
  have hRodd : Odd R := hspec.2.1
  have hrfactor : certificate.r =
      (1 : Int) * ((2 ^ 3 : Nat) : Int) * R := hspec.2.2
  have hLfactor : L = certificate.h0 * R := by
    simpa [hh0] using hLfactorH
  have hRpos : 0 < R := by
    by_contra hR
    have hzero : R = 0 := Nat.eq_zero_of_not_pos hR
    rw [hzero, mul_zero] at hLfactor
    omega
  exact
    { R := R
      R_pos := hRpos
      R_odd := hRodd
      L_factor := by simpa [certificate, L] using hLfactor
      r_factor := by simpa [certificate] using hrfactor }

private structure Outer41Link23KernelData
    (j : Nat) (hj : j % 13 ≠ 12)
    (factor : Outer41Link23FactorData j) where
  t_factor :
    (outer41LocalLink23 j).t0 =
      (((2 ^ 5 * 13 ^ 1 * outer41Link23A ^ 2 : Nat)) : Int)
  Delta_factor :
    (outer41LocalLink23 j).Delta0 =
      (-1 : Int) * (2 : Int) ^ 3 * 13 ^ 0 * outer41Link23B ^ 2
  a_coprime_L : outer41Link23A.Coprime (outer41Link23L j)
  b_coprime_L : outer41Link23B.Coprime (outer41Link23L j)
  t_coprime_R : Int.gcd (outer41LocalLink23 j).t0 factor.R = 1
  Q0_coprime_R : (outer41LocalLink23 j).Q0.Coprime factor.R
  endpoint : Int.ModEq factor.R
    (((outer41LocalLink23 j).q0 : Int) * (outer41LocalLink23 j).t0)
    (((outer41LocalLink23 j).Q0 : Int) * (outer41LocalLink23 j).Delta0)
  thirteen_coprime_h0 : (13 : Nat).Coprime (outer41LocalLink23 j).h0
  primary :
    jacobiSym (outer41ReducedP23 j : Int) (outer41LocalLink23 j).e *
      jacobiSym (outer41P21 j : Int) (outer41LocalLink23 j).e = 1

set_option maxHeartbeats 700000 in
private noncomputable def outer41Link23KernelData
    (j : Nat) (hj : j % 13 ≠ 12)
    (factor : Outer41Link23FactorData j) :
    Outer41Link23KernelData j hj factor := by
  let certificate := outer41LocalLink23 j
  let L := outer41Link23L j
  let a := outer41Link23A
  let b := outer41Link23B
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, outer41Link23L, Nat.add_mod, Nat.mul_mod]
  have he : certificate.e = 1 := by
    simpa [certificate] using outer41E23 j
  have h13L : (13 : Nat).Coprime L := by
    simpa [L, outer41Link23L] using outer41L23CoprimeThirteen j hj
  have h13H0 : (13 : Nat).Coprime certificate.h0 :=
    h13L.of_dvd_right ⟨factor.R, by
      simpa [certificate, L] using factor.L_factor⟩
  have haL : a.Coprime L := by
    simpa [a, L, outer41Link23A, outer41Link23L,
      show 38233051740637926057696 =
        12360551568672 * (10639 * 290737) by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right
        (10639 * 290737) 49817377110831005331401
        (12360551568672 * j)).mpr (by norm_num)
  have hbL : b.Coprime L := by
    simpa [b, L, outer41Link23B, outer41Link23L,
      show 38233051740637926057696 =
        98980830176 * (3 * 306749 * 419743) by norm_num,
      mul_assoc, mul_left_comm, mul_comm] using
      (Nat.coprime_add_mul_right_right
        (3 * 306749 * 419743) 49817377110831005331401
        (98980830176 * j)).mpr (by norm_num)
  have ht0eq : certificate.t0 = certificate.t := by
    have hfactor := certificate.t_factor
    rw [he] at hfactor
    norm_num at hfactor
    omega
  have hDelta0eq : certificate.Delta0 = certificate.Delta := by
    have hfactor := certificate.Delta_factor
    rw [he] at hfactor
    norm_num at hfactor
    omega
  have htfactor : certificate.t0 =
      (((2 ^ 5 * 13 ^ 1 * a ^ 2 : Nat)) : Int) := by
    rw [ht0eq, (outer41Constants23 j).1]
    simp [hj, a, outer41Link23A]
  have hDeltafactor : certificate.Delta0 =
      (-1 : Int) * (2 : Int) ^ 3 * 13 ^ 0 * b ^ 2 := by
    rw [hDelta0eq, (outer41Constants23 j).2]
    simp [b, outer41Link23B]
  have hRdvdL : factor.R ∣ L :=
    ⟨certificate.h0, by
      calc
        L = certificate.h0 * factor.R := by
          simpa [certificate, L] using factor.L_factor
        _ = factor.R * certificate.h0 := Nat.mul_comm _ _⟩
  have htwoL : (2 : Nat).Coprime L := hLodd.coprime_two_left
  have htCoprimeL : (2 ^ 5 * 13 ^ 1 * a ^ 2).Coprime L :=
    (((htwoL.pow_left 5).mul_left (h13L.pow_left 1)).mul_left
      (haL.pow_left 2))
  have htR : Int.gcd certificate.t0 factor.R = 1 := by
    rw [htfactor, Int.gcd_natCast_natCast]
    exact (htCoprimeL.of_dvd_right hRdvdL).gcd_eq_one
  have hQ0R : certificate.Q0.Coprime factor.R :=
    (outer41FactorCoprime (R := factor.R) (n := certificate.Q0)
      (w := 3) (s := 1) (Or.inl rfl)
      (by simpa [certificate] using factor.r_factor)
      (outer41LocalLink_r_coprime_Q0 certificate
        (outer41ReducedCoprime23 j))).symm
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A22 j) (outer41B22 j)
    (outer41Endpoint23Reduced j)
    (by
      rw [outer41P21Cast, outer41Q21Cast]
      exact outer41Delta23 j)
  have hRdvdR : (factor.R : Int) ∣ certificate.r := by
    refine ⟨(2 : Int) ^ 3, ?_⟩
    rw [show certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (13 : Int) ^ 0 * factor.R by
        simpa [certificate] using factor.r_factor]
    norm_num
    ring
  have hendpoint : Int.ModEq factor.R
      ((certificate.q0 : Int) * certificate.t0)
      ((certificate.Q0 : Int) * certificate.Delta0) := by
    simpa [ht0eq, hDelta0eq] using hdualRaw.of_dvd hRdvdR
  have hprimary :
      jacobiSym (outer41ReducedP23 j : Int) certificate.e *
        jacobiSym (outer41P21 j : Int) certificate.e = 1 := by
    rw [he]
    simp only [jacobiSym.one_right, mul_one]
  exact
    { t_factor := htfactor
      Delta_factor := hDeltafactor
      a_coprime_L := haL
      b_coprime_L := hbL
      t_coprime_R := htR
      Q0_coprime_R := hQ0R
      endpoint := hendpoint
      thirteen_coprime_h0 := h13H0
      primary := hprimary }

set_option maxHeartbeats 500000 in
private theorem outer41Link23OffCharacter
    (j : Nat) (hj : j % 13 ≠ 12) :
    (1 : Int) *
      outer41PrimeRawCharacter 3 5 3 1 0 0 1 (-1) 13
        ((outer41LocalLink23 j).h0 * (outer41LocalLink23 j).Q0)
        ((outer41LocalLink23 j).h0 * (outer41LocalLink23 j).q0)
        (outer41Link23L j) =
      jacobiSym (j + 1 : Nat) 13 := by
  let certificate := outer41LocalLink23 j
  let L := outer41Link23L j
  have he : certificate.e = 1 := by
    simpa [certificate] using outer41E23 j
  have hh0 : certificate.h0 = certificate.h := by
    have hfactor := certificate.h_factor
    rw [he] at hfactor
    omega
  have hQbar : certificate.h0 * certificate.Q0 =
      outer41ReducedQ23 j := by
    rw [hh0, ← certificate.Q_factor]
  have hqbar : certificate.h0 * certificate.q0 = outer41Q21 j := by
    rw [hh0, ← certificate.q_factor]
  have hQmod : outer41ReducedQ23 j % 8 = 7 := by
    rw [outer41ReducedQ23, if_neg hj]
    have h := outer41HornerNat_map_mod j 8 outer41Q23Coeffs
    rw [outer41Q23ModEightCoeffs] at h
    simpa [outer41Q23, outer41HornerNat] using h
  have hqmod : outer41Q21 j % 8 = 3 := by
    have h := outer41HornerNat_map_mod j 8 outer41Q21Coeffs
    rw [outer41Q21ModEightCoeffs] at h
    simpa [outer41Q21, outer41HornerNat] using h
  have hLodd : Odd L := by
    rw [Nat.odd_iff]
    norm_num [L, outer41Link23L, Nat.add_mod, Nat.mul_mod]
  have hLmod : L % 8 = 1 := by
    norm_num [L, outer41Link23L, Nat.add_mod, Nat.mul_mod]
  have hbase := outer41OrdinaryRawCharacter 3 5 3 1 (-1)
    (Or.inl rfl) (Or.inr rfl)
    (outer41ReducedQ23Odd j) (outer41Q21Odd j) hLodd
  have hbaseValue :
      qrSign (outer41ReducedQ23 j) (outer41Q21 j) *
          (jacobiSym (-1 : Int) (outer41ReducedQ23 j) *
            jacobiSym (1 : Int) (outer41Q21 j) *
            jacobiSym 2 (outer41ReducedQ23 j) ^ 3 *
            jacobiSym 2 (outer41Q21 j) ^ 3 *
            qrSign (outer41ReducedQ23 j) L *
            qrSign (outer41Q21 j) L *
            jacobiSym 2 L ^ (5 + 3) *
            jacobiSym (-1 : Int) L) = -1 := by
    rw [hbase, hQmod, hqmod, hLmod]
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter]
  change (1 : Int) *
      outer41PrimeRawCharacter 3 5 3 1 0 0 1 (-1) 13
        (certificate.h0 * certificate.Q0)
        (certificate.h0 * certificate.q0) L =
      jacobiSym (j + 1 : Nat) 13
  rw [hQbar, hqbar, one_mul,
    outer41PrimeRawCharacter_one_zero_zero, hbaseValue]
  norm_num
  rw [show L =
    49817377110831005331401 +
      38233051740637926057696 * j by
        rfl,
    outer41JacobiThirteenL23]
  norm_num [Nat.cast_add]

set_option maxHeartbeats 300000 in
private theorem outer41Link23_21_off
    (j : Nat) (hj : j % 13 ≠ 12) :
    jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) =
      jacobiSym (j + 1 : Nat) 13 *
        jacobiSym (outer41P21 j : Int) (outer41Q21 j) := by
  let factor := outer41Link23FactorData j hj
  let kernel := outer41Link23KernelData j hj factor
  exact outer41PrimeLinkTransfer (outer41LocalLink23 j)
    3 5 3 1 0 0 1 (-1) 1 (jacobiSym (j + 1 : Nat) 13)
    (Or.inl rfl) factor.R_pos factor.R_odd factor.L_factor
    (by simpa using factor.r_factor) kernel.t_factor kernel.Delta_factor
    kernel.a_coprime_L kernel.b_coprime_L kernel.t_coprime_R
    kernel.Q0_coprime_R kernel.endpoint kernel.thirteen_coprime_h0
    kernel.primary (outer41Link23OffCharacter j hj)

private def outer41Link23OnL (j : Nat) : Nat :=
  39124153692191239847981 + 38233051740637926057696 * (j / 13)

private theorem outer41Link23OnL_reconstruct
    (j : Nat) (hj : j % 13 = 12) :
    outer41Link23L j = 13 * outer41Link23OnL j := by
  have hdecomp : 13 * (j / 13) + 12 = j :=
    outer41_thirteen_mul_div_add_twelve j hj
  calc
    outer41Link23L j =
        49817377110831005331401 +
          38233051740637926057696 * (13 * (j / 13) + 12) := by
      rw [hdecomp]
      rfl
    _ = 13 * outer41Link23OnL j := by
      simp [outer41Link23OnL]
      ring

private theorem outer41Link23OnL_pos (j : Nat) :
    0 < outer41Link23OnL j := by
  simp [outer41Link23OnL]

private theorem outer41Link23OnL_odd (j : Nat) :
    Odd (outer41Link23OnL j) := by
  rw [Nat.odd_iff]
  norm_num [outer41Link23OnL, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link23OnA_coprime (j : Nat) :
    outer41Link23A.Coprime (outer41Link23OnL j) := by
  simpa [outer41Link23A, outer41Link23OnL,
    show 38233051740637926057696 =
      12360551568672 * (10639 * 290737) by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right
      (10639 * 290737) 39124153692191239847981
      (12360551568672 * (j / 13))).mpr (by norm_num)

private theorem outer41Link23OnB_coprime (j : Nat) :
    outer41Link23B.Coprime (outer41Link23OnL j) := by
  simpa [outer41Link23B, outer41Link23OnL,
    show 38233051740637926057696 =
      98980830176 * (3 * 306749 * 419743) by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right
      (3 * 306749 * 419743) 39124153692191239847981
      (98980830176 * (j / 13))).mpr (by norm_num)

set_option maxHeartbeats 400000 in
private theorem outer41Link23OnCross
    (j : Nat) (hj : j % 13 = 12) :
    ((outer41LocalLink23 j).h : Int) * (outer41LocalLink23 j).r =
      (1 : Int) * (2 : Int) ^ 3 * outer41Link23OnL j := by
  let certificate := outer41LocalLink23 j
  apply mul_left_cancel₀ (show (13 : Int) ≠ 0 by norm_num)
  calc
    (13 : Int) * ((certificate.h : Int) * certificate.r) =
        13 * ((outer41P21 j : Int) * outer41ReducedQ23 j -
          (outer41Q21 j : Int) * outer41ReducedP23 j) := by
      rw [certificate.cross]
    _ = outer41P21Int j * outer41Q23Int j -
        outer41Q21Int j * outer41P23Int j := by
      rw [outer41P21Cast, outer41Q21Cast,
        outer41P23Int_reconstruct_reduced j hj,
        outer41Q23Int_reconstruct_reduced j hj]
      ring
    _ = 8 * (49817377110831005331401 +
        38233051740637926057696 * (j : Int)) := outer41Cross23 j
    _ = (13 : Int) *
        ((1 : Int) * (2 : Int) ^ 3 * outer41Link23OnL j) := by
      rw [show (49817377110831005331401 +
          38233051740637926057696 * (j : Int)) =
          (outer41Link23L j : Int) by
            simp [outer41Link23L],
        outer41Link23OnL_reconstruct j hj]
      push_cast
      ring

private theorem outer41Link23OnCharacter
    (j : Nat) (hj : j % 13 = 12) :
    qrSign (outer41ReducedQ23 j) (outer41Q21 j) *
        (jacobiSym (-1 : Int) (outer41ReducedQ23 j) *
          jacobiSym (1 : Int) (outer41Q21 j) *
          jacobiSym 2 (outer41ReducedQ23 j) ^ 3 *
          jacobiSym 2 (outer41Q21 j) ^ 3 *
          qrSign (outer41ReducedQ23 j) (outer41Link23OnL j) *
          qrSign (outer41Q21 j) (outer41Link23OnL j) *
          jacobiSym 2 (outer41Link23OnL j) ^ (5 + 3) *
          jacobiSym (-1 : Int) (outer41Link23OnL j)) = 1 := by
  have hQmod : outer41ReducedQ23 j % 8 = 3 := by
    rw [outer41ReducedQ23, if_pos hj]
    have h := outer41HornerNat_map_mod (j / 13) 8
      outer41Q23QuotientCoeffs
    rw [outer41Q23QuotientModEightCoeffs] at h
    simpa [outer41Q23Quotient, outer41HornerNat] using h
  have hqmod : outer41Q21 j % 8 = 3 := by
    have h := outer41HornerNat_map_mod j 8 outer41Q21Coeffs
    rw [outer41Q21ModEightCoeffs] at h
    simpa [outer41Q21, outer41HornerNat] using h
  have hLmod : outer41Link23OnL j % 8 = 5 := by
    norm_num [outer41Link23OnL, Nat.add_mod, Nat.mul_mod]
  have hbase := outer41OrdinaryRawCharacter 3 5 3 1 (-1)
    (Or.inl rfl) (Or.inr rfl)
    (outer41ReducedQ23Odd j) (outer41Q21Odd j)
    (outer41Link23OnL_odd j)
  rw [hbase, hQmod, hqmod, hLmod]
  norm_num [outer41OrdinaryActualResidueSign,
    outer41QrResidueCharacter, outer41UnitResidueCharacter,
    outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

set_option maxHeartbeats 700000 in
private theorem outer41Link23_21_on
    (j : Nat) (hj : j % 13 = 12) :
    jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) =
      jacobiSym (outer41P21 j : Int) (outer41Q21 j) := by
  let certificate := outer41LocalLink23 j
  have he : certificate.e = 1 := by
    simpa [certificate] using outer41E23 j
  have htfactor : certificate.t =
      ((2 ^ 5 * outer41Link23A ^ 2 : Nat) : Int) := by
    rw [(outer41Constants23 j).1, if_pos hj]
    norm_num [outer41Link23A]
  have hDeltafactor : certificate.Delta =
      (-1 : Int) * (2 : Int) ^ 3 * outer41Link23B ^ 2 := by
    rw [(outer41Constants23 j).2]
    norm_num [outer41Link23B]
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A22 j) (outer41B22 j)
    (outer41Endpoint23Reduced j)
    (by
      rw [outer41P21Cast, outer41Q21Cast]
      exact outer41Delta23 j)
  simpa only [one_mul] using outer41OrdinaryLinkFromRaw certificate
    3 5 3 1 (-1) 1 (Or.inl rfl) he
    (outer41Link23OnL_pos j) (outer41Link23OnL_odd j)
    (by simpa [certificate] using outer41Link23OnCross j hj)
    htfactor hDeltafactor
    (outer41Link23OnA_coprime j) (outer41Link23OnB_coprime j)
    (outer41ReducedCoprime23 j) hdualRaw
    (outer41Link23OnCharacter j hj)

/-- The factor-13 multiplier is always a sign. -/
theorem ss41_factor13Multiplier_sq (j : Nat) :
    ss41_factor13Multiplier j ^ 2 = 1 := by
  by_cases hj : j % 13 = 12
  · simp [ss41_factor13Multiplier, hj]
  · rw [ss41_factor13Multiplier, if_neg hj,
      outer41Factor13OffClassSymbol j hj]
    split <;> norm_num

set_option maxHeartbeats 500000 in
private theorem outer41Link23_21 (j : Nat) :
    jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) =
      ss41_factor13Multiplier j *
        jacobiSym (outer41P21 j : Int) (outer41Q21 j) := by
  by_cases hj : j % 13 = 12
  · rw [ss41_factor13Multiplier, if_pos hj, one_mul]
    exact outer41Link23_21_on j hj
  · rw [ss41_factor13Multiplier, if_neg hj]
    exact outer41Link23_21_off j hj

set_option maxHeartbeats 5000000 in
private theorem outer41Link25OffResidueTable (j : Nat) :
    (j % 3 = 0 → outer41Q25 j % 12 = 5 ∧ outer41Q23 j % 12 = 7) ∧
    (j % 3 = 2 → outer41Q25 j % 12 = 1 ∧ outer41Q23 j % 12 = 11) ∧
    (j % 9 = 1 → outer41Q25 j % 36 = 21 ∧ outer41Q23 j % 36 = 15) ∧
    (j % 9 = 4 → outer41Q25 j % 36 = 33 ∧ outer41Q23 j % 36 = 3) ∧
    (j % 27 = 7 → outer41Q25 j % 108 = 9 ∧ outer41Q23 j % 108 = 99) ∧
    (j % 27 = 16 → outer41Q25 j % 108 = 45 ∧ outer41Q23 j % 108 = 63) := by
  have h25 := outer41HornerNat_mod j 108 outer41Q25Coeffs
  have h23 := outer41HornerNat_mod j 108 outer41Q23Coeffs
  change outer41Q25 j % 108 = _ at h25
  change outer41Q23 j % 108 = _ at h23
  have hj3 : j % 3 = (j % 108) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 108)).symm
  have hj9 : j % 9 = (j % 108) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 108)).symm
  have hj27 : j % 27 = (j % 108) % 27 :=
    (Nat.mod_mod_of_dvd j (by decide : 27 ∣ 108)).symm
  have h25mod12 : outer41Q25 j % 12 = (outer41Q25 j % 108) % 12 :=
    (Nat.mod_mod_of_dvd (outer41Q25 j) (by decide : 12 ∣ 108)).symm
  have h23mod12 : outer41Q23 j % 12 = (outer41Q23 j % 108) % 12 :=
    (Nat.mod_mod_of_dvd (outer41Q23 j) (by decide : 12 ∣ 108)).symm
  have h25mod36 : outer41Q25 j % 36 = (outer41Q25 j % 108) % 36 :=
    (Nat.mod_mod_of_dvd (outer41Q25 j) (by decide : 36 ∣ 108)).symm
  have h23mod36 : outer41Q23 j % 36 = (outer41Q23 j % 108) % 36 :=
    (Nat.mod_mod_of_dvd (outer41Q23 j) (by decide : 36 ∣ 108)).symm
  have hjbound : j % 108 < 108 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 108 <;>
    norm_num [outer41Q25Coeffs, outer41Q23Coeffs,
      outer41HornerNat] at h25 h23
  all_goals
    norm_num [hcase, h25, h23] at hj3 hj9 hj27 h25mod12 h23mod12 h25mod36 h23mod36
    simp [hj3, hj9, hj27, h25, h23, h25mod12, h23mod12,
      h25mod36, h23mod36]

set_option maxHeartbeats 5000000 in
private theorem outer41Link25OnResidueTable
    (j : Nat) (hj : j % 13 = 12) :
    (j % 3 = 0 → outer41Q25 j % 12 = 5 ∧
      outer41Q23Quotient (j / 13) % 12 = 7) ∧
    (j % 3 = 2 → outer41Q25 j % 12 = 1 ∧
      outer41Q23Quotient (j / 13) % 12 = 11) ∧
    (j % 9 = 1 → outer41Q25 j % 36 = 21 ∧
      outer41Q23Quotient (j / 13) % 36 = 15) ∧
    (j % 9 = 4 → outer41Q25 j % 36 = 33 ∧
      outer41Q23Quotient (j / 13) % 36 = 3) ∧
    (j % 27 = 7 → outer41Q25 j % 108 = 9 ∧
      outer41Q23Quotient (j / 13) % 108 = 99) ∧
    (j % 27 = 16 → outer41Q25 j % 108 = 45 ∧
      outer41Q23Quotient (j / 13) % 108 = 63) := by
  have hdecomp : 13 * (j / 13) + 12 = j :=
    outer41_thirteen_mul_div_add_twelve j hj
  have h25 := outer41HornerNat_mod j 108 outer41Q25Coeffs
  have h23 := outer41HornerNat_mod (j / 13) 108 outer41Q23QuotientCoeffs
  change outer41Q25 j % 108 = _ at h25
  change outer41Q23Quotient (j / 13) % 108 = _ at h23
  have hj108 : j % 108 =
      (13 * ((j / 13) % 108) + 12) % 108 := by
    calc
      j % 108 = (13 * (j / 13) + 12) % 108 :=
        (congrArg (fun n : Nat => n % 108) hdecomp).symm
      _ = (13 * ((j / 13) % 108) + 12) % 108 := by
        simp [Nat.add_mod, Nat.mul_mod]
  have hj3 : j % 3 = (j % 108) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 108)).symm
  have hj9 : j % 9 = (j % 108) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 108)).symm
  have hj27 : j % 27 = (j % 108) % 27 :=
    (Nat.mod_mod_of_dvd j (by decide : 27 ∣ 108)).symm
  have h25mod12 : outer41Q25 j % 12 = (outer41Q25 j % 108) % 12 :=
    (Nat.mod_mod_of_dvd (outer41Q25 j) (by decide : 12 ∣ 108)).symm
  have h23mod12 : outer41Q23Quotient (j / 13) % 12 =
      (outer41Q23Quotient (j / 13) % 108) % 12 :=
    (Nat.mod_mod_of_dvd (outer41Q23Quotient (j / 13))
      (by decide : 12 ∣ 108)).symm
  have h25mod36 : outer41Q25 j % 36 = (outer41Q25 j % 108) % 36 :=
    (Nat.mod_mod_of_dvd (outer41Q25 j) (by decide : 36 ∣ 108)).symm
  have h23mod36 : outer41Q23Quotient (j / 13) % 36 =
      (outer41Q23Quotient (j / 13) % 108) % 36 :=
    (Nat.mod_mod_of_dvd (outer41Q23Quotient (j / 13))
      (by decide : 36 ∣ 108)).symm
  have hnbound : (j / 13) % 108 < 108 := Nat.mod_lt _ (by decide)
  interval_cases hcase : (j / 13) % 108 <;>
    norm_num [outer41Q25Coeffs, outer41Q23QuotientCoeffs,
      outer41HornerNat, hcase, hj108] at h25 h23
  all_goals
    norm_num [hcase, hj108, h25, h23] at hj3 hj9 hj27 h25mod12 h23mod12 h25mod36 h23mod36
    simp [hj3, hj9, hj27, h25, h23, h25mod12, h23mod12,
      h25mod36, h23mod36]

private theorem outer41Link25ResidueTable (j : Nat) :
    (j % 3 = 0 → outer41Q25 j % 12 = 5 ∧
      outer41ReducedQ23 j % 12 = 7) ∧
    (j % 3 = 2 → outer41Q25 j % 12 = 1 ∧
      outer41ReducedQ23 j % 12 = 11) ∧
    (j % 9 = 1 → outer41Q25 j % 36 = 21 ∧
      outer41ReducedQ23 j % 36 = 15) ∧
    (j % 9 = 4 → outer41Q25 j % 36 = 33 ∧
      outer41ReducedQ23 j % 36 = 3) ∧
    (j % 27 = 7 → outer41Q25 j % 108 = 9 ∧
      outer41ReducedQ23 j % 108 = 99) ∧
    (j % 27 = 16 → outer41Q25 j % 108 = 45 ∧
      outer41ReducedQ23 j % 108 = 63) := by
  by_cases hj : j % 13 = 12
  · simpa [outer41ReducedQ23, hj] using outer41Link25OnResidueTable j hj
  · simpa [outer41ReducedQ23, hj] using outer41Link25OffResidueTable j

private theorem outer41ReducedFactorModAfterExact
    {Q e Q0 modulus residue : Nat} (hmoduluspos : 0 < modulus)
    (hepos : 0 < e) (hfactor : Q = e * Q0)
    (hmod : Nat.ModEq (modulus * e) Q (e * residue)) :
    Nat.ModEq modulus Q0 residue := by
  rw [hfactor] at hmod
  have hcancel := hmod.cancel_left_div_gcd (mul_pos hmoduluspos hepos)
  have hgcd : Nat.gcd (modulus * e) e = e :=
    Nat.gcd_eq_right_iff_dvd.mpr (dvd_mul_left e modulus)
  simpa [hgcd, Nat.mul_comm, Nat.mul_div_right modulus hepos] using hcancel

private theorem outer41Link25ReducedModTwelve
    (j e Qres qres : Nat) (he : (outer41LocalLink25 j).e = e)
    (hepos : 0 < e)
    (hQraw : outer41Q25 j % (12 * e) = (e * Qres) % (12 * e))
    (hqraw : outer41ReducedQ23 j % (12 * e) = (e * qres) % (12 * e)) :
    ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = Qres % 12 ∧
      ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = qres % 12 := by
  let certificate := outer41LocalLink25 j
  have hQfactor : outer41Q25 j = e * (certificate.h0 * certificate.Q0) := by
    calc
      outer41Q25 j = certificate.h * certificate.Q0 := certificate.Q_factor
      _ = (certificate.e * certificate.h0) * certificate.Q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.Q0) := by rw [he]; ring
  have hqfactor : outer41ReducedQ23 j =
      e * (certificate.h0 * certificate.q0) := by
    calc
      outer41ReducedQ23 j = certificate.h * certificate.q0 := certificate.q_factor
      _ = (certificate.e * certificate.h0) * certificate.q0 := by
        rw [certificate.h_factor]
      _ = e * (certificate.h0 * certificate.q0) := by rw [he]; ring
  have hQmod : Nat.ModEq (12 * e) (outer41Q25 j) (e * Qres) := hQraw
  have hqmod : Nat.ModEq (12 * e) (outer41ReducedQ23 j) (e * qres) := hqraw
  exact ⟨outer41ReducedFactorModAfterExact (by norm_num) hepos hQfactor hQmod,
    outer41ReducedFactorModAfterExact (by norm_num) hepos hqfactor hqmod⟩

private theorem outer41Link25NeutralOfResidues
    (j c exponent L : Nat) (hthreeL : (3 : Nat).Coprime L)
    (hresidue :
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 1 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 11) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 5 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 7) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 7 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 5) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 11 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 1))
    (heven : Even exponent) :
    (jacobiSym (3 : Int)
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) ^ c *
        jacobiSym (3 : Int)
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) ^ c) *
      jacobiSym (3 : Int) L ^ exponent = 1 := by
  let certificate := outer41LocalLink25 j
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  have hQodd : Odd (certificate.h0 * certificate.Q0) :=
    hh0odd.mul certificate.Q0_odd
  have hqodd : Odd (certificate.h0 * certificate.q0) :=
    hh0odd.mul certificate.q0_odd
  have hQmod3 : (certificate.h0 * certificate.Q0) % 3 =
      ((certificate.h0 * certificate.Q0) % 12) % 3 :=
    (Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 12)).symm
  have hqmod3 : (certificate.h0 * certificate.q0) % 3 =
      ((certificate.h0 * certificate.q0) % 12) % 3 :=
    (Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 12)).symm
  have hthreeQ : (3 : Nat).Coprime (certificate.h0 * certificate.Q0) := by
    rw [Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
    rcases hresidue with h | h | h | h <;>
      simp_all [certificate]
  have hthreeq : (3 : Nat).Coprime (certificate.h0 * certificate.q0) := by
    rw [Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
    rcases hresidue with h | h | h | h <;>
      simp_all [certificate]
  have hsame : jacobiSym (3 : Int) (certificate.h0 * certificate.Q0) =
      jacobiSym (3 : Int) (certificate.h0 * certificate.q0) := by
    rw [outer41JacobiThreeOfModTwelve hQodd hthreeQ,
      outer41JacobiThreeOfModTwelve hqodd hthreeq]
    rcases hresidue with h | h | h | h <;>
      simp_all [certificate]
  have hQint : Int.gcd (3 : Int) (certificate.h0 * certificate.Q0) = 1 := by
    exact_mod_cast hthreeQ.gcd_eq_one
  have hqint : Int.gcd (3 : Int) (certificate.h0 * certificate.q0) = 1 := by
    exact_mod_cast hthreeq.gcd_eq_one
  have hLint : Int.gcd (3 : Int) L = 1 := by
    exact_mod_cast hthreeL.gcd_eq_one
  exact outer41PrimeNeutralOfSameSymbol hQint hqint hLint hsame heven

private theorem outer41Link25UnitBase
    {Q q L : Nat} (hQodd : Odd Q) (hqodd : Odd q) (hLodd : Odd L) :
    qrSign Q q *
        (jacobiSym (1 : Int) Q * jacobiSym (-1 : Int) q *
          jacobiSym 2 Q ^ 2 * jacobiSym 2 q ^ 2 *
          qrSign Q L * qrSign q L * jacobiSym 2 L ^ (2 + 3) *
          jacobiSym (1 : Int) L) =
      outer41OrdinaryActualResidueSign 2 2 3 (-1) 1
        (Q % 8) (q % 8) (L % 8) (L % 8) := by
  simpa using outer41OrdinaryRawCharacter 2 2 3 (-1) 1
    (Or.inr rfl) (Or.inl rfl) hQodd hqodd hLodd

private theorem outer41Link25OffBaseFromUnit
    (j Q q : Nat) (primary : Int)
    (hunit :
      qrSign Q q *
          (jacobiSym (1 : Int) Q * jacobiSym (-1 : Int) q *
            jacobiSym 2 Q ^ 2 * jacobiSym 2 q ^ 2 *
            qrSign Q (outer41Link25OffL j) *
            qrSign q (outer41Link25OffL j) *
            jacobiSym 2 (outer41Link25OffL j) ^ (2 + 3) *
            jacobiSym (1 : Int) (outer41Link25OffL j)) = primary) :
    qrSign Q q *
        (jacobiSym (1 : Int) Q * jacobiSym (-1 : Int) q *
          jacobiSym 2 Q ^ 2 * jacobiSym 2 q ^ 2 *
          qrSign Q (outer41Link25OffL j) *
          qrSign q (outer41Link25OffL j) *
          jacobiSym 2 (outer41Link25OffL j) ^ (2 + 3) *
          jacobiSym (13 : Int) (outer41Link25OffL j)) =
      primary * (-jacobiSym (j + 1 : Nat) 13) := by
  have hthirteen : jacobiSym (13 : Int) (outer41Link25OffL j) =
      -jacobiSym (j + 1 : Nat) 13 := by
    simpa [outer41Link25OffL] using outer41JacobiThirteenL25 j
  calc
    qrSign Q q *
        (jacobiSym (1 : Int) Q * jacobiSym (-1 : Int) q *
          jacobiSym 2 Q ^ 2 * jacobiSym 2 q ^ 2 *
          qrSign Q (outer41Link25OffL j) *
          qrSign q (outer41Link25OffL j) *
          jacobiSym 2 (outer41Link25OffL j) ^ (2 + 3) *
          jacobiSym (13 : Int) (outer41Link25OffL j)) =
        (qrSign Q q *
          (jacobiSym (1 : Int) Q * jacobiSym (-1 : Int) q *
            jacobiSym 2 Q ^ 2 * jacobiSym 2 q ^ 2 *
            qrSign Q (outer41Link25OffL j) *
            qrSign q (outer41Link25OffL j) *
            jacobiSym 2 (outer41Link25OffL j) ^ (2 + 3) *
            jacobiSym (1 : Int) (outer41Link25OffL j))) *
          jacobiSym (13 : Int) (outer41Link25OffL j) := by
            simp only [jacobiSym.one_left]
            ring
    _ = primary * (-jacobiSym (j + 1 : Nat) 13) := by
      rw [hunit, hthirteen]

set_option maxHeartbeats 1000000 in
private theorem outer41Link25FactorSplit
    (j e d c zt zd Qres qoff qon : Nat) (primary : Int)
    (he : (outer41LocalLink25 j).e = e)
    (hefactor : e = 3 ^ d)
    (hprimary81 : Nat.gcd 81 (outer41LocalLink25 j).h = e)
    (hcrossPower : e * 3 ^ c = 3 ^ 3)
    (htPower : e * 3 ^ zt = 3 ^ 5)
    (hDeltaPower : e * 3 ^ zd = 3 ^ 3)
    (hprimaryCorrection :
      jacobiSym (outer41P25 j : Int) (outer41LocalLink25 j).e *
        jacobiSym (outer41ReducedP23 j : Int)
          (outer41LocalLink25 j).e = primary)
    (hprimarySign : primary = 1 ∨ primary = -1)
    (hneutralOff :
      (jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) ^ c *
          jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) ^ c) *
        jacobiSym (3 : Int) (outer41Link25OffL j) ^ (zt + zd) = 1)
    (hneutralOn :
      (jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) ^ c *
          jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) ^ c) *
        jacobiSym (3 : Int) (outer41Link25OnL j) ^ (zt + zd) = 1)
    (hQeight : (e * Qres) % 8 = 5)
    (hqoffeight : (e * qoff) % 8 = 7)
    (hqoneight : (e * qon) % 8 = 3)
    (hoffUnit : outer41OrdinaryActualResidueSign 2 2 3 (-1) 1
      (Qres % 8) (qoff % 8) 7 7 = primary)
    (honUnit : outer41OrdinaryActualResidueSign 2 2 3 (-1) 1
      (Qres % 8) (qon % 8) 3 3 = primary * (-1)) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      (-ss41_factor13Multiplier j) *
        jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) := by
  let certificate := outer41LocalLink25 j
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  have hQodd : Odd (certificate.h0 * certificate.Q0) :=
    hh0odd.mul certificate.Q0_odd
  have hqodd : Odd (certificate.h0 * certificate.q0) :=
    hh0odd.mul certificate.q0_odd
  by_cases hj : j % 13 = 12
  · have hmods := outer41Link25ReducedModEight j e Qres qon he
      (by rw [outer41Link25QModEight, hQeight])
      (by rw [outer41ReducedQ23ModEightOn j hj, hqoneight])
    have hLmod : outer41Link25OnL j % 8 = 3 := by
      norm_num [outer41Link25OnL, Nat.add_mod, Nat.mul_mod]
    have hunit := outer41Link25UnitBase hQodd hqodd
      (outer41Link25OnL_odd j)
    have hbase :
        qrSign (certificate.h0 * certificate.Q0)
            (certificate.h0 * certificate.q0) *
          (jacobiSym (1 : Int) (certificate.h0 * certificate.Q0) *
            jacobiSym (-1 : Int) (certificate.h0 * certificate.q0) *
            jacobiSym 2 (certificate.h0 * certificate.Q0) ^ 2 *
            jacobiSym 2 (certificate.h0 * certificate.q0) ^ 2 *
            qrSign (certificate.h0 * certificate.Q0) (outer41Link25OnL j) *
            qrSign (certificate.h0 * certificate.q0) (outer41Link25OnL j) *
            jacobiSym 2 (outer41Link25OnL j) ^ (2 + 3) *
            jacobiSym (1 : Int) (outer41Link25OnL j)) = primary * (-1) := by
      rw [hmods.1, hmods.2, hLmod, honUnit] at hunit
      exact hunit
    have hDelta : certificate.Delta =
        (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 3 * 385315961 ^ 2 := by
      rw [(outer41Constants25 j).2, if_pos hj]
      norm_num
    have hlink := outer41Link25Branch j e d c zt zd
      (outer41Link25OnL j) 1 primary (-1) he hefactor hprimary81
      hcrossPower htPower hDeltaPower (outer41Link25OnL_pos j)
      (outer41Link25OnL_odd j) (outer41Link25OnL_coprime_three j)
      (outer41Link25OnL_coprime_a j) (outer41Link25OnL_coprime_b j)
      (outer41Link25OnCross j hj) hDelta hprimaryCorrection
      hprimarySign hneutralOn hbase
    rw [ss41_factor13Multiplier, if_pos hj]
    exact hlink
  · have hmods := outer41Link25ReducedModEight j e Qres qoff he
      (by rw [outer41Link25QModEight, hQeight])
      (by rw [outer41ReducedQ23ModEightOff j hj, hqoffeight])
    have hLmod : outer41Link25OffL j % 8 = 7 := by
      norm_num [outer41Link25OffL, Nat.add_mod, Nat.mul_mod]
    have hunitRaw := outer41Link25UnitBase hQodd hqodd
      (outer41Link25OffL_odd j)
    have hunit :
        qrSign (certificate.h0 * certificate.Q0)
            (certificate.h0 * certificate.q0) *
          (jacobiSym (1 : Int) (certificate.h0 * certificate.Q0) *
            jacobiSym (-1 : Int) (certificate.h0 * certificate.q0) *
            jacobiSym 2 (certificate.h0 * certificate.Q0) ^ 2 *
            jacobiSym 2 (certificate.h0 * certificate.q0) ^ 2 *
            qrSign (certificate.h0 * certificate.Q0) (outer41Link25OffL j) *
            qrSign (certificate.h0 * certificate.q0) (outer41Link25OffL j) *
            jacobiSym 2 (outer41Link25OffL j) ^ (2 + 3) *
            jacobiSym (1 : Int) (outer41Link25OffL j)) = primary := by
      rw [hmods.1, hmods.2, hLmod, hoffUnit] at hunitRaw
      exact hunitRaw
    have hbase := outer41Link25OffBaseFromUnit j
      (certificate.h0 * certificate.Q0) (certificate.h0 * certificate.q0)
      primary hunit
    have hDelta : certificate.Delta =
        (13 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 3 * 385315961 ^ 2 := by
      rw [(outer41Constants25 j).2, if_neg hj]
      norm_num
    have hlink := outer41Link25Branch j e d c zt zd
      (outer41Link25OffL j) 13 primary (-jacobiSym (j + 1 : Nat) 13)
      he hefactor hprimary81 hcrossPower htPower hDeltaPower
      (outer41Link25OffL_pos j) (outer41Link25OffL_odd j)
      (outer41Link25OffL_coprime_three j) (outer41Link25OffL_coprime_a j)
      (outer41Link25OffL_coprime_b j) (outer41Link25OffCross j hj)
      hDelta hprimaryCorrection hprimarySign hneutralOff hbase
    rw [ss41_factor13Multiplier, if_neg hj]
    exact hlink

set_option maxHeartbeats 1000000 in
private theorem outer41Link25_23_e_one
    (j : Nat) (hj : j % 3 = 0 ∨ j % 3 = 2) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      (-ss41_factor13Multiplier j) *
        jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) := by
  have hjmod9 : j % 3 = (j % 9) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
  have hjmod27 : j % 9 = (j % 27) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 27)).symm
  have h27 : j % 27 ≠ 25 := by omega
  have h7 : j % 9 ≠ 7 := by omega
  have h14 : ¬(j % 9 = 1 ∨ j % 9 = 4) := by omega
  have he : (outer41LocalLink25 j).e = 1 := by
    rw [outer41E25, if_neg h27, if_neg h7, if_neg h14]
  have hprimary : Nat.gcd 81 (outer41LocalLink25 j).h = 1 := by
    rw [(outer41LocalLink25 j).h_eq_gcd]
    simpa [h27, h7, h14] using outer41Primary25 j
  have hcorrection := outer41Correction25 j
  rw [if_neg h27, if_neg h14] at hcorrection
  rcases outer41Link25ResidueTable j with
    ⟨hzero, htwo, hmodOne, hmodFour, hmodSeven, hmodSixteen⟩
  have hresidue :
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 1 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 11) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 5 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 7) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 7 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 5) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 11 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 1) := by
    rcases hj with hzero' | htwo'
    · have hraw := hzero hzero'
      have hred := outer41Link25ReducedModTwelve j 1 5 7 he (by norm_num)
        (by simpa using hraw.1) (by simpa using hraw.2)
      exact Or.inr (Or.inl hred)
    · have hraw := htwo htwo'
      have hred := outer41Link25ReducedModTwelve j 1 1 11 he (by norm_num)
        (by simpa using hraw.1) (by simpa using hraw.2)
      exact Or.inl hred
  have hneutralOff := outer41Link25NeutralOfResidues j 3 (5 + 3)
    (outer41Link25OffL j) (outer41Link25OffL_coprime_three j)
    hresidue (by decide)
  have hneutralOn := outer41Link25NeutralOfResidues j 3 (5 + 3)
    (outer41Link25OnL j) (outer41Link25OnL_coprime_three j)
    hresidue (by decide)
  exact outer41Link25FactorSplit j 1 0 3 5 3 5 7 3 1 he
    (by norm_num) hprimary (by norm_num) (by norm_num) (by norm_num)
    hcorrection (Or.inl rfl) hneutralOff hneutralOn
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])

set_option maxHeartbeats 1000000 in
private theorem outer41Link25_23_e_three
    (j : Nat) (hj : j % 9 = 1 ∨ j % 9 = 4) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      (-ss41_factor13Multiplier j) *
        jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) := by
  have hjmod27 : j % 9 = (j % 27) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 27)).symm
  have h27 : j % 27 ≠ 25 := by omega
  have h7 : j % 9 ≠ 7 := by omega
  have he : (outer41LocalLink25 j).e = 3 := by
    rw [outer41E25, if_neg h27, if_neg h7, if_pos hj]
  have hprimary : Nat.gcd 81 (outer41LocalLink25 j).h = 3 := by
    rw [(outer41LocalLink25 j).h_eq_gcd]
    simpa [h27, h7, hj] using outer41Primary25 j
  have hcorrection := outer41Correction25 j
  rw [if_neg h27, if_pos hj] at hcorrection
  rcases outer41Link25ResidueTable j with
    ⟨hzero, htwo, hmodOne, hmodFour, hmodSeven, hmodSixteen⟩
  have hresidue :
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 1 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 11) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 5 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 7) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 7 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 5) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 11 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 1) := by
    rcases hj with hone | hfour
    · have hraw := hmodOne hone
      have hred := outer41Link25ReducedModTwelve j 3 7 5 he (by norm_num)
        (by simpa using hraw.1) (by simpa using hraw.2)
      exact Or.inr (Or.inr (Or.inl hred))
    · have hraw := hmodFour hfour
      have hred := outer41Link25ReducedModTwelve j 3 11 1 he (by norm_num)
        (by simpa using hraw.1) (by simpa using hraw.2)
      exact Or.inr (Or.inr (Or.inr hred))
  have hneutralOff := outer41Link25NeutralOfResidues j 2 (4 + 2)
    (outer41Link25OffL j) (outer41Link25OffL_coprime_three j)
    hresidue (by decide)
  have hneutralOn := outer41Link25NeutralOfResidues j 2 (4 + 2)
    (outer41Link25OnL j) (outer41Link25OnL_coprime_three j)
    hresidue (by decide)
  exact outer41Link25FactorSplit j 3 1 2 4 2 7 5 1 (-1) he
    (by norm_num) hprimary (by norm_num) (by norm_num) (by norm_num)
    hcorrection (Or.inr rfl) hneutralOff hneutralOn
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])

set_option maxHeartbeats 1000000 in
private theorem outer41Link25_23_e_nine
    (j : Nat) (hj7 : j % 9 = 7) (hj25 : j % 27 ≠ 25) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      (-ss41_factor13Multiplier j) *
        jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) := by
  have h14 : ¬(j % 9 = 1 ∨ j % 9 = 4) := by omega
  have he : (outer41LocalLink25 j).e = 9 := by
    rw [outer41E25, if_neg hj25, if_pos hj7]
  have hprimary : Nat.gcd 81 (outer41LocalLink25 j).h = 9 := by
    rw [(outer41LocalLink25 j).h_eq_gcd]
    simpa [hj25, hj7] using outer41Primary25 j
  have hcorrection := outer41Correction25 j
  rw [if_neg hj25, if_neg h14] at hcorrection
  have hjmod27 : j % 9 = (j % 27) % 9 :=
    (Nat.mod_mod_of_dvd j (by decide : 9 ∣ 27)).symm
  have hjbound : j % 27 < 27 := Nat.mod_lt _ (by decide)
  have hj : j % 27 = 7 ∨ j % 27 = 16 := by omega
  rcases outer41Link25ResidueTable j with
    ⟨hzero, htwo, hmodOne, hmodFour, hmodSeven, hmodSixteen⟩
  have hresidue :
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 1 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 11) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 5 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 7) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 7 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 5) ∨
      (((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) % 12 = 11 ∧
          ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) % 12 = 1) := by
    rcases hj with hseven | hsixteen
    · have hraw := hmodSeven hseven
      have hred := outer41Link25ReducedModTwelve j 9 1 11 he (by norm_num)
        (by simpa using hraw.1) (by simpa using hraw.2)
      exact Or.inl hred
    · have hraw := hmodSixteen hsixteen
      have hred := outer41Link25ReducedModTwelve j 9 5 7 he (by norm_num)
        (by simpa using hraw.1) (by simpa using hraw.2)
      exact Or.inr (Or.inl hred)
  have hneutralOff := outer41Link25NeutralOfResidues j 1 (3 + 1)
    (outer41Link25OffL j) (outer41Link25OffL_coprime_three j)
    hresidue (by decide)
  have hneutralOn := outer41Link25NeutralOfResidues j 1 (3 + 1)
    (outer41Link25OnL j) (outer41Link25OnL_coprime_three j)
    hresidue (by decide)
  exact outer41Link25FactorSplit j 9 2 1 3 1 5 7 3 1 he
    (by norm_num) hprimary (by norm_num) (by norm_num) (by norm_num)
    hcorrection (Or.inl rfl) hneutralOff hneutralOn
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])

set_option maxHeartbeats 1000000 in
private theorem outer41Link25_23_e_twentySeven
    (j : Nat) (hj25 : j % 27 = 25) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      (-ss41_factor13Multiplier j) *
        jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) := by
  have he : (outer41LocalLink25 j).e = 27 := by
    rw [outer41E25, if_pos hj25]
  have hprimary : Nat.gcd 81 (outer41LocalLink25 j).h = 27 := by
    rw [(outer41LocalLink25 j).h_eq_gcd]
    simpa [hj25] using outer41Primary25 j
  have hcorrection := outer41Correction25 j
  rw [if_pos hj25] at hcorrection
  have hLintOff : Int.gcd (3 : Int) (outer41Link25OffL j) = 1 := by
    exact_mod_cast (outer41Link25OffL_coprime_three j).gcd_eq_one
  have hLintOn : Int.gcd (3 : Int) (outer41Link25OnL j) = 1 := by
    exact_mod_cast (outer41Link25OnL_coprime_three j).gcd_eq_one
  have hneutralOff :
      (jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) ^ 0 *
          jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) ^ 0) *
        jacobiSym (3 : Int) (outer41Link25OffL j) ^ (2 + 0) = 1 := by
    norm_num [jacobiSym.sq_one hLintOff]
  have hneutralOn :
      (jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).Q0) ^ 0 *
          jacobiSym (3 : Int)
            ((outer41LocalLink25 j).h0 * (outer41LocalLink25 j).q0) ^ 0) *
        jacobiSym (3 : Int) (outer41Link25OnL j) ^ (2 + 0) = 1 := by
    norm_num [jacobiSym.sq_one hLintOn]
  exact outer41Link25FactorSplit j 27 3 0 2 0 7 5 1 (-1) he
    (by norm_num) hprimary (by norm_num) (by norm_num) (by norm_num)
    hcorrection (Or.inr rfl) hneutralOff hneutralOn
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])
    (by norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter])

set_option maxHeartbeats 500000 in
private theorem outer41Link25_23 (j : Nat) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      (-ss41_factor13Multiplier j) *
        jacobiSym (outer41ReducedP23 j : Int) (outer41ReducedQ23 j) := by
  by_cases h25 : j % 27 = 25
  · exact outer41Link25_23_e_twentySeven j h25
  · by_cases h7 : j % 9 = 7
    · exact outer41Link25_23_e_nine j h7 h25
    · by_cases h14 : j % 9 = 1 ∨ j % 9 = 4
      · exact outer41Link25_23_e_three j h14
      · have hjmod : j % 3 = (j % 9) % 3 :=
          (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
        have hjbound : j % 9 < 9 := Nat.mod_lt _ (by decide)
        have hj : j % 3 = 0 ∨ j % 3 = 2 := by omega
        exact outer41Link25_23_e_one j hj

private def outer41Link37L (j : Nat) : Nat :=
  1882609 + 1526536 * j

private theorem outer41Link37L_pos (j : Nat) : 0 < outer41Link37L j := by
  simp [outer41Link37L]

private theorem outer41Link37L_odd (j : Nat) : Odd (outer41Link37L j) := by
  rw [Nat.odd_iff]
  norm_num [outer41Link37L, Nat.add_mod, Nat.mul_mod]

private theorem outer41Link37L_coprime_a (j : Nat) :
    (121 : Nat).Coprime (outer41Link37L j) := by
  simpa [outer41Link37L, show 1526536 = 12616 * 121 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 121 1882609 (12616 * j)).mpr
      (by norm_num)

private theorem outer41Link37L_coprime_b (j : Nat) :
    (1577 : Nat).Coprime (outer41Link37L j) := by
  simpa [outer41Link37L, show 1526536 = 968 * 1577 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 1577 1882609 (968 * j)).mpr
      (by norm_num)

set_option maxHeartbeats 400000 in
private theorem outer41Link37Cross (j : Nat) :
    ((outer41LocalLink37 j).h : Int) * (outer41LocalLink37 j).r =
      (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 2 * outer41Link37L j := by
  let certificate := outer41LocalLink37 j
  calc
    (certificate.h : Int) * certificate.r =
        (outer41P35 j : Int) * outer41Q37 j -
          (outer41Q35 j : Int) * outer41P37 j := certificate.cross
    _ = outer41P35Int j * outer41Q37Int j -
        outer41Q35Int j * outer41P37Int j := by
      rw [outer41P35Cast, outer41Q37Cast,
        outer41Q35Cast, outer41P37Cast]
    _ = 72 * (1882609 + 1526536 * (j : Int)) := outer41Cross37 j
    _ = (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 2 *
        outer41Link37L j := by simp [outer41Link37L]

private theorem outer41Q35ModEight (j : Nat) : outer41Q35 j % 8 = 7 := by
  have h := outer41HornerNat_map_mod j 8 outer41Q35Coeffs
  rw [outer41Q35ModEightCoeffs] at h
  simpa [outer41Q35, outer41HornerNat] using h

private theorem outer41Q37ModEight (j : Nat) : outer41Q37 j % 8 = 7 := by
  have h24 := outer41Q37Q35ModTwentyFour j
  have h8 : outer41Q37 j % 8 = outer41Q35 j % 8 := by
    calc
      outer41Q37 j % 8 = (outer41Q37 j % 24) % 8 :=
        (Nat.mod_mod_of_dvd (outer41Q37 j) (by decide : 8 ∣ 24)).symm
      _ = (outer41Q35 j % 24) % 8 := by rw [h24]
      _ = outer41Q35 j % 8 :=
        Nat.mod_mod_of_dvd (outer41Q35 j) (by decide : 8 ∣ 24)
  rw [h8, outer41Q35ModEight]

private theorem outer41Link37BaseCharacter
    {Q q L : Nat} (hQodd : Odd Q) (hqodd : Odd q) (hLodd : Odd L)
    (hQmod : Q % 8 = 7) (hqmod : q % 8 = 7) (hLmod : L % 8 = 1) :
    qrSign Q q *
        (jacobiSym (-1 : Int) Q * jacobiSym (1 : Int) q *
          jacobiSym 2 Q ^ 3 * jacobiSym 2 q ^ 3 *
          qrSign Q L * qrSign q L * jacobiSym 2 L ^ (0 + 0) *
          jacobiSym (1 : Int) L) = 1 := by
  rw [outer41OrdinaryRawCharacter 3 0 0 1 1
    (Or.inl rfl) (Or.inl rfl) hQodd hqodd hLodd,
    hQmod, hqmod, hLmod]
  norm_num [outer41OrdinaryActualResidueSign,
    outer41QrResidueCharacter, outer41UnitResidueCharacter,
    outer41NegOneResidueCharacter, outer41TwoResidueCharacter]

set_option maxHeartbeats 1000000 in
private theorem outer41Link37_35_one
    (j : Nat) (hj : j % 3 = 1) :
    jacobiSym (outer41P37 j : Int) (outer41Q37 j) =
      jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
  let certificate := outer41LocalLink37 j
  have he : certificate.e = 1 := by
    rw [outer41E37, if_neg (by omega : j % 3 ≠ 0)]
  have hprimary : Nat.gcd 9 certificate.h = 1 := by
    rw [certificate.h_eq_gcd]
    simpa [hj] using outer41Primary37 j
  have hthreeH0 : (3 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactPrimary Nat.prime_three (by norm_num)
      (by simpa [he] using certificate.h_factor) hprimary (by norm_num)
  have hthreeL : (3 : Nat).Coprime (outer41Link37L j) := by
    rw [Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
    norm_num [outer41Link37L, Nat.add_mod, Nat.mul_mod, hj]
  have hh0 : certificate.h0 = certificate.h := by
    have hh := certificate.h_factor
    rw [he] at hh
    omega
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 2 * outer41Link37L j := by
    simpa [hh0, certificate] using outer41Link37Cross j
  have ht0 : certificate.t0 =
      (((2 ^ 0 * 3 ^ 1 * 121 ^ 2 : Nat)) : Int) := by
    have ht := certificate.t_factor
    rw [he, (outer41Constants37 j).1] at ht
    norm_num at ht ⊢
    omega
  have hDelta0 : certificate.Delta0 =
      (1 : Int) * (2 : Int) ^ 0 * (3 : Int) ^ 1 * 1577 ^ 2 := by
    have hDelta := certificate.Delta_factor
    rw [he, (outer41Constants37 j).2] at hDelta
    norm_num at hDelta ⊢
    omega
  have hdenom := outer41PrimeCoprimeReducedDenominators certificate
    3 2 1 Nat.prime_three (by norm_num) hthreeH0
    (outer41RawCoprime37 j) hcrossReduced
  have hQint : Int.gcd (3 : Int) (certificate.h0 * certificate.Q0) = 1 := by
    exact_mod_cast hdenom.1.gcd_eq_one
  have hqint : Int.gcd (3 : Int) (certificate.h0 * certificate.q0) = 1 := by
    exact_mod_cast hdenom.2.gcd_eq_one
  have hLint : Int.gcd (3 : Int) (outer41Link37L j) = 1 := by
    exact_mod_cast hthreeL.gcd_eq_one
  have hneutral :
      (jacobiSym (3 : Int) (certificate.h0 * certificate.Q0) ^ 2 *
          jacobiSym (3 : Int) (certificate.h0 * certificate.q0) ^ 2) *
        jacobiSym (3 : Int) (outer41Link37L j) ^ (1 + 1) = 1 :=
    outer41PrimeNeutralOfEvenPowers hQint hqint hLint
      (by decide) (by decide)
  have hQbar : certificate.h0 * certificate.Q0 = outer41Q37 j := by
    rw [hh0, ← certificate.Q_factor]
  have hqbar : certificate.h0 * certificate.q0 = outer41Q35 j := by
    rw [hh0, ← certificate.q_factor]
  have hQodd : Odd (certificate.h0 * certificate.Q0) := by
    rw [hQbar]
    exact outer41Q37Odd j
  have hqodd : Odd (certificate.h0 * certificate.q0) := by
    rw [hqbar]
    exact outer41Q35Odd j
  have hLmod : outer41Link37L j % 8 = 1 := by
    norm_num [outer41Link37L, Nat.add_mod, Nat.mul_mod]
  have hQmod : (certificate.h0 * certificate.Q0) % 8 = 7 := by
    rw [hQbar]
    exact outer41Q37ModEight j
  have hqmod : (certificate.h0 * certificate.q0) % 8 = 7 := by
    rw [hqbar]
    exact outer41Q35ModEight j
  have hbaseOne := outer41Link37BaseCharacter hQodd hqodd
    (outer41Link37L_odd j) hQmod hqmod hLmod
  have hrawCharacter := outer41PrimeRawCharacter_of_neutral
    3 0 0 1 1 2 1 1 1 hbaseOne hneutral
  have hcharacter :
      (1 : Int) * outer41PrimeRawCharacter 3 0 0 1 1 2 1 1 3
          (certificate.h0 * certificate.Q0)
          (certificate.h0 * certificate.q0) (outer41Link37L j) = 1 := by
    simpa using hrawCharacter
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A36 j) (outer41B36 j)
    (by
      rw [outer41P37Cast, outer41Q37Cast]
      exact outer41Endpoint37 j)
    (by
      rw [outer41P35Cast, outer41Q35Cast]
      exact outer41Delta37 j)
  simpa only [one_mul] using outer41PrimeLinkFromReducedRaw certificate
    3 0 0 1 1 2 0 1 1 1 1 (Or.inl rfl) he (by norm_num)
    (outer41Link37L_pos j) (outer41Link37L_odd j) hthreeH0 hthreeL
    hcrossReduced ht0 hDelta0 (outer41Link37L_coprime_a j)
    (outer41Link37L_coprime_b j) (outer41RawCoprime37 j)
    hdualRaw (outer41Correction37 j) hcharacter

private def outer41Link37DivThreeL (j : Nat) : Nat :=
  1645227 + 1526536 * (j / 3)

private theorem outer41Link37DivThreeL_reconstruct
    (j : Nat) (hj : j % 3 = 2) :
    outer41Link37L j = 3 * outer41Link37DivThreeL j := by
  have hdecomp : 3 * (j / 3) + 2 = j := by
    have hdivision := Nat.mod_add_div j 3
    omega
  calc
    outer41Link37L j =
        1882609 + 1526536 * (3 * (j / 3) + 2) := by
      simpa [outer41Link37L] using
        (congrArg (fun n : Nat => 1882609 + 1526536 * n) hdecomp).symm
    _ = 3 * outer41Link37DivThreeL j := by
      simp [outer41Link37DivThreeL]
      ring

private theorem outer41Link37DivThreeL_pos (j : Nat) :
    0 < outer41Link37DivThreeL j := by
  simp [outer41Link37DivThreeL]

private theorem outer41Link37DivThreeL_odd (j : Nat) :
    Odd (outer41Link37DivThreeL j) := by
  rw [Nat.odd_iff]
  norm_num [outer41Link37DivThreeL, Nat.add_mod, Nat.mul_mod]

set_option maxHeartbeats 2000000 in
private theorem outer41Q37Q35ModNine_of_mod_three_two
    (j : Nat) (hj : j % 3 = 2) :
    outer41Q37 j % 9 = 5 ∧ outer41Q35 j % 9 = 8 := by
  have h37 := outer41HornerNat_mod j 9 outer41Q37Coeffs
  have h35 := outer41HornerNat_mod j 9 outer41Q35Coeffs
  change outer41Q37 j % 9 = _ at h37
  change outer41Q35 j % 9 = _ at h35
  have hjmod3 : j % 3 = (j % 9) % 3 :=
    (Nat.mod_mod_of_dvd j (by decide : 3 ∣ 9)).symm
  have hjbound : j % 9 < 9 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 9 <;>
    norm_num [outer41Q37Coeffs, outer41Q35Coeffs,
      outer41HornerNat] at h37 h35 hjmod3
  all_goals omega

set_option maxHeartbeats 2000000 in
private theorem outer41Link37_35_two
    (j : Nat) (hj : j % 3 = 2) :
    jacobiSym (outer41P37 j : Int) (outer41Q37 j) =
      jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
  let certificate := outer41LocalLink37 j
  let L := outer41Link37L j
  let L1 := outer41Link37DivThreeL j
  have he : certificate.e = 1 := by
    rw [outer41E37, if_neg (by omega : j % 3 ≠ 0)]
  have hh0 : certificate.h0 = certificate.h := by
    have hh := certificate.h_factor
    rw [he] at hh
    omega
  have hprimary : Nat.gcd 9 certificate.h = 1 := by
    rw [certificate.h_eq_gcd]
    simpa [hj] using outer41Primary37 j
  have hthreeH0 : (3 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactPrimary Nat.prime_three (by norm_num)
      (by simpa [he] using certificate.h_factor) hprimary (by norm_num)
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 2 * L := by
    simpa [hh0, certificate, L] using outer41Link37Cross j
  obtain ⟨R, hLfactor, hRodd, hrfactor⟩ :=
    outer41ExtractOddPrimeCross 3 2 1 certificate.h0_pos
      (by
        have hproduct : Odd (certificate.e * certificate.h0) := by
          simpa [certificate.h_factor] using certificate.h_odd
        exact Nat.Odd.of_mul_right hproduct)
      (by simpa [L] using outer41Link37L_odd j) (Or.inl rfl)
      hthreeH0 hcrossReduced
  have hRpos : 0 < R := by
    by_contra hR
    have : R = 0 := Nat.eq_zero_of_not_pos hR
    rw [this, mul_zero] at hLfactor
    have hLpos : 0 < L := by simpa [L] using outer41Link37L_pos j
    omega
  have hLthree : L = 3 * L1 := by
    simpa [L, L1] using outer41Link37DivThreeL_reconstruct j hj
  have hthreeR : 3 ∣ R := by
    have hthreeProduct : 3 ∣ certificate.h0 * R := by
      rw [← hLfactor, hLthree]
      exact dvd_mul_right 3 L1
    rcases Nat.prime_three.dvd_mul.mp hthreeProduct with hthreeH | hthreeR
    · exact False.elim
        ((Nat.prime_three.coprime_iff_not_dvd.mp hthreeH0) hthreeH)
    · exact hthreeR
  obtain ⟨R1, hRfactor⟩ := hthreeR
  have hR1pos : 0 < R1 := by omega
  have hR1odd : Odd R1 := by
    rw [hRfactor] at hRodd
    exact Nat.Odd.of_mul_right hRodd
  have hL1factor : L1 = certificate.h0 * R1 := by
    have hscaled : 3 * L1 = 3 * (certificate.h0 * R1) := by
      calc
        3 * L1 = L := hLthree.symm
        _ = certificate.h0 * R := hLfactor
        _ = 3 * (certificate.h0 * R1) := by rw [hRfactor]; ring
    omega
  have hrfactor1 : certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (3 : Int) ^ 3 * R1 := by
    rw [hrfactor, hRfactor]
    push_cast
    ring
  have hL1dvdL : L1 ∣ L := ⟨3, by rw [hLthree]; ring⟩
  have haL1 : (121 : Nat).Coprime L1 :=
    (outer41Link37L_coprime_a j).of_dvd_right (by simpa [L] using hL1dvdL)
  have hbL1 : (1577 : Nat).Coprime L1 :=
    (outer41Link37L_coprime_b j).of_dvd_right (by simpa [L] using hL1dvdL)
  have hR1dvdL1 : R1 ∣ L1 := ⟨certificate.h0, by rw [hL1factor]; ring⟩
  have haR1 : (121 : Nat).Coprime R1 := haL1.of_dvd_right hR1dvdL1
  have htR1 : Int.gcd ((121 : Int) ^ 2) R1 = 1 := by
    exact_mod_cast (haR1.pow_left 2).gcd_eq_one
  have hrfactorTotal : certificate.r =
      (1 : Int) * (2 : Int) ^ 3 * (3 ^ 3 * R1 : Nat) := by
    rw [hrfactor1]
    push_cast
    ring
  have hQ0Total : certificate.Q0.Coprime (3 ^ 3 * R1) :=
    (outer41FactorCoprime (R := 3 ^ 3 * R1) (n := certificate.Q0)
      (w := 3) (s := 1) (Or.inl rfl) hrfactorTotal
      (outer41LocalLink_r_coprime_Q0 certificate
        (outer41RawCoprime37 j))).symm
  have hQ0R1 : certificate.Q0.Coprime R1 :=
    hQ0Total.of_dvd_right ⟨3 ^ 3, by ring⟩
  have hdualRaw := outer41LocalLinkDualEndpoint certificate
    (outer41A36 j) (outer41B36 j)
    (by
      rw [outer41P37Cast, outer41Q37Cast]
      exact outer41Endpoint37 j)
    (by
      rw [outer41P35Cast, outer41Q35Cast]
      exact outer41Delta37 j)
  have hthreeR1dvdR : ((3 : Int) * R1) ∣ certificate.r := by
    refine ⟨(2 : Int) ^ 3 * (3 : Int) ^ 2, ?_⟩
    rw [hrfactor1]
    push_cast
    ring
  have hdualThreeR1 := hdualRaw.of_dvd hthreeR1dvdR
  have hdualFactored : Int.ModEq ((3 : Int) * R1)
      ((3 : Int) * ((certificate.q0 : Int) * (121 : Int) ^ 2))
      ((3 : Int) * ((certificate.Q0 : Int) * (1577 : Int) ^ 2)) := by
    rw [(outer41Constants37 j).1, (outer41Constants37 j).2] at hdualThreeR1
    convert hdualThreeR1 using 1 <;> ring
  have hendpoint : Int.ModEq R1
      ((certificate.q0 : Int) * (121 : Int) ^ 2)
      ((certificate.Q0 : Int) * (1577 : Int) ^ 2) :=
    hdualFactored.mul_left_cancel' (by norm_num)
  have hprime := outer41PrimeExceptionalCrossProduct
    (Q0 := certificate.Q0) (q0 := certificate.q0)
    (h := certificate.h0) (R := R1) (L := L1)
    (a := 121) (b := 1577) (z := 3)
    (r := certificate.r) (t := (121 : Int) ^ 2)
    (Delta := (1577 : Int) ^ 2)
    3 0 0 0 0 3 1 1 certificate.h0_pos hR1pos
    certificate.Q0_odd certificate.q0_odd hR1odd hL1factor
    hrfactor1 (by norm_num) (by norm_num) haL1 hbL1 htR1 hQ0R1 hendpoint
  have haH0 : (121 : Nat).Coprime certificate.h0 :=
    haL1.of_dvd_right ⟨R1, hL1factor⟩
  have hbH0 : (1577 : Nat).Coprime certificate.h0 :=
    hbL1.of_dvd_right ⟨R1, hL1factor⟩
  have haH0Int : Int.gcd (121 : Int) certificate.h0 = 1 := by
    exact_mod_cast haH0.gcd_eq_one
  have hbH0Int : Int.gcd (1577 : Int) certificate.h0 = 1 := by
    exact_mod_cast hbH0.gcd_eq_one
  have hthreeH0Int : Int.gcd (3 : Int) certificate.h0 = 1 := by
    exact_mod_cast hthreeH0.gcd_eq_one
  have hsynthetic :
      jacobiSym ((121 : Int) ^ 2) certificate.h0 *
          jacobiSym ((1577 : Int) ^ 2) certificate.h0 = 1 := by
    rw [jacobiSym.sq_one' haH0Int, jacobiSym.sq_one' hbH0Int]
    norm_num
  have ht0 : certificate.t0 = (3 : Int) * (121 : Int) ^ 2 := by
    have ht := certificate.t_factor
    rw [he, (outer41Constants37 j).1] at ht
    norm_num at ht ⊢
    omega
  have hDelta0 : certificate.Delta0 = (3 : Int) * (1577 : Int) ^ 2 := by
    have hDelta := certificate.Delta_factor
    rw [he, (outer41Constants37 j).2] at hDelta
    norm_num at hDelta ⊢
    omega
  have hsecondary :
      jacobiSym certificate.t0 certificate.h0 *
          jacobiSym certificate.Delta0 certificate.h0 = 1 := by
    rw [ht0, hDelta0, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.sq_one' haH0Int, jacobiSym.sq_one' hbH0Int]
    rw [mul_one, ← pow_two, jacobiSym.sq_one hthreeH0Int]
  have hcrossSymbols :
      jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 =
        jacobiSym (-1 : Int) certificate.Q0 *
          jacobiSym 2 certificate.Q0 ^ 3 *
          jacobiSym 2 certificate.q0 ^ 3 *
          jacobiSym (3 : Int) certificate.Q0 ^ 3 *
          jacobiSym (3 : Int) certificate.q0 ^ 3 *
          qrSign certificate.Q0 R1 * qrSign certificate.q0 R1 := by
    have hprime' := hprime
    rw [hsynthetic, one_mul] at hprime'
    simpa only [pow_zero, one_mul, mul_one, Nat.zero_add,
      jacobiSym.one_left, Nat.cast_ofNat] using hprime'
  have hraw8 : outer41Q37 j % 8 = outer41Q35 j % 8 := by
    rw [outer41Q37ModEight, outer41Q35ModEight]
  have hhEight : Nat.gcd 8 certificate.h = 1 := by
    have hcop : certificate.h.Coprime (2 ^ 3) :=
      certificate.h_odd.coprime_two_right.pow_right 3
    simpa using hcop.symm.gcd_eq_one
  have hmodEight : certificate.Q0 % 8 = certificate.q0 % 8 :=
    outer41ReducedFactorsModEq certificate.Q_factor certificate.q_factor
      hhEight hraw8
  have hraw9 := outer41Q37Q35ModNine_of_mod_three_two j hj
  have hrawThree : Nat.ModEq 3 (outer41Q37 j) (outer41Q35 j) := by
    change outer41Q37 j % 3 = outer41Q35 j % 3
    calc
      outer41Q37 j % 3 = (outer41Q37 j % 9) % 3 :=
        (Nat.mod_mod_of_dvd (outer41Q37 j) (by decide : 3 ∣ 9)).symm
      _ = (outer41Q35 j % 9) % 3 := by rw [hraw9.1, hraw9.2]
      _ = outer41Q35 j % 3 :=
        Nat.mod_mod_of_dvd (outer41Q35 j) (by decide : 3 ∣ 9)
  have hmodThreeFactored : Nat.ModEq 3
      (certificate.h0 * certificate.Q0)
      (certificate.h0 * certificate.q0) := by
    simpa [hh0, certificate.Q_factor, certificate.q_factor] using hrawThree
  have hmodThree : certificate.Q0 % 3 = certificate.q0 % 3 :=
    hmodThreeFactored.cancel_left_of_coprime hthreeH0.gcd_eq_one
  have hthreeProducts := outer41PrimeCoprimePairOfCommonCoprimeAndModEq
    Nat.prime_three hthreeH0 certificate.Q0_coprime_q0 hmodThreeFactored
  have hthreeQ0 : (3 : Nat).Coprime certificate.Q0 :=
    hthreeProducts.1.of_dvd_right ⟨certificate.h0, by ring⟩
  have hthreeq0 : (3 : Nat).Coprime certificate.q0 :=
    hthreeProducts.2.of_dvd_right ⟨certificate.h0, by ring⟩
  have hcharacter := outer41ThreePrimePairCharacter
    certificate.Q0_odd certificate.q0_odd hR1odd
    hthreeQ0 hthreeq0 hmodEight hmodThree
  have hthreeQ0Int : Int.gcd (3 : Int) certificate.Q0 = 1 := by
    exact_mod_cast hthreeQ0.gcd_eq_one
  have hthreeq0Int : Int.gcd (3 : Int) certificate.q0 = 1 := by
    exact_mod_cast hthreeq0.gcd_eq_one
  have hQcube : jacobiSym (3 : Int) certificate.Q0 ^ 3 =
      jacobiSym (3 : Int) certificate.Q0 := by
    calc
      jacobiSym (3 : Int) certificate.Q0 ^ 3 =
          jacobiSym (3 : Int) certificate.Q0 ^ 2 *
            jacobiSym (3 : Int) certificate.Q0 := by ring
      _ = jacobiSym (3 : Int) certificate.Q0 := by
        rw [jacobiSym.sq_one hthreeQ0Int, one_mul]
  have hqcube : jacobiSym (3 : Int) certificate.q0 ^ 3 =
      jacobiSym (3 : Int) certificate.q0 := by
    calc
      jacobiSym (3 : Int) certificate.q0 ^ 3 =
          jacobiSym (3 : Int) certificate.q0 ^ 2 *
            jacobiSym (3 : Int) certificate.q0 := by ring
      _ = jacobiSym (3 : Int) certificate.q0 := by
        rw [jacobiSym.sq_one hthreeq0Int, one_mul]
  have hcharacterCompact :
      qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-1 : Int) certificate.Q0 *
            jacobiSym 2 certificate.Q0 ^ 3 *
            jacobiSym 2 certificate.q0 ^ 3 *
            jacobiSym (3 : Int) certificate.Q0 ^ 3 *
            jacobiSym (3 : Int) certificate.q0 ^ 3 *
            qrSign certificate.Q0 R1 * qrSign certificate.q0 R1) = 1 := by
    rw [hQcube, hqcube]
    simpa only [jacobiSym.one_left, mul_one, mul_assoc] using hcharacter
  have hfactored := outer41FactoredLinkTransfer certificate
  have hprimaryCorrection := outer41Correction37 j
  calc
    jacobiSym (outer41P37 j : Int) (outer41Q37 j) =
        qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (outer41P37 j : Int) certificate.e *
            jacobiSym (outer41P35 j : Int) certificate.e) *
          (jacobiSym certificate.t0 certificate.h0 *
            jacobiSym certificate.Delta0 certificate.h0) *
          jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 *
          jacobiSym (outer41P35 j : Int) (outer41Q35 j) := hfactored
    _ = qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-certificate.r) certificate.Q0 *
            jacobiSym certificate.r certificate.q0) *
          jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
      rw [hprimaryCorrection, hsecondary]
      ring
    _ = 1 * jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
      rw [hcrossSymbols, hcharacterCompact]
    _ = _ := one_mul _

private theorem outer41Link37_35 (j : Nat) :
    jacobiSym (outer41P37 j : Int) (outer41Q37 j) =
      jacobiSym (outer41P35 j : Int) (outer41Q35 j) := by
  by_cases hzero : j % 3 = 0
  · exact outer41Link37_35_zero j hzero
  · by_cases hone : j % 3 = 1
    · exact outer41Link37_35_one j hone
    · have hbound : j % 3 < 3 := Nat.mod_lt _ (by decide)
      have htwo : j % 3 = 2 := by omega
      exact outer41Link37_35_two j htwo

private def outer41RootL (j : Nat) : Nat :=
  17 + 14 * j

private theorem outer41RootL_pos (j : Nat) : 0 < outer41RootL j := by
  simp [outer41RootL]

private theorem outer41RootL_odd (j : Nat) : Odd (outer41RootL j) := by
  rw [Nat.odd_iff]
  norm_num [outer41RootL, Nat.add_mod, Nat.mul_mod]

private theorem outer41RootL_coprime_seven (j : Nat) :
    (7 : Nat).Coprime (outer41RootL j) := by
  simpa [outer41RootL, show 14 = 2 * 7 by norm_num,
    mul_assoc, mul_left_comm, mul_comm] using
    (Nat.coprime_add_mul_right_right 7 17 (2 * j)).mpr (by norm_num)

private theorem outer41RootL_coprime_five_of_not_mod_two
    (j : Nat) (hj : j % 5 ≠ 2) :
    (5 : Nat).Coprime (outer41RootL j) := by
  rw [(by norm_num : Nat.Prime 5).coprime_iff_not_dvd,
    Nat.dvd_iff_mod_eq_zero]
  norm_num [outer41RootL, Nat.add_mod, Nat.mul_mod]
  omega

set_option maxHeartbeats 400000 in
private theorem outer41RootCrossReduced (j : Nat) :
    ((outer41RootLocalLink j).h : Int) * (outer41RootLocalLink j).r =
      (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 2 * outer41RootL j := by
  let certificate := outer41RootLocalLink j
  calc
    (certificate.h : Int) * certificate.r =
        (outer41P37 j : Int) * outer41Gamma j -
          (outer41Q37 j : Int) * outer41Alpha j := certificate.cross
    _ = outer41P37Int j * outer41GammaInt j -
        outer41Q37Int j * outer41AlphaInt j := by
          rw [outer41P37Cast, outer41Q37Cast,
            outer41AlphaCast, outer41GammaCast]
    _ = 800 * (17 + 14 * (j : Int)) := outer41RootCross j
    _ = (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 2 *
        outer41RootL j := by
          simp [outer41RootL]

private theorem outer41RootDualEndpoint (j : Nat) :
    Int.ModEq (outer41RootLocalLink j).r
      (((outer41RootLocalLink j).q0 : Int) *
        (outer41RootLocalLink j).t)
      (((outer41RootLocalLink j).Q0 : Int) *
        (outer41RootLocalLink j).Delta) := by
  exact outer41LocalLinkDualEndpoint (outer41RootLocalLink j)
    (outer41A38 j) (outer41B38 j)
    (by
      rw [outer41AlphaCast, outer41GammaCast]
      exact outer41RootEndpoint j)
    (by
      rw [outer41P37Cast, outer41Q37Cast]
      calc
        outer41A38 j * outer41Q37Int j +
            outer41B38 j * outer41P37Int j =
            outer41P37Int j * outer41B38 j +
              outer41Q37Int j * outer41A38 j := by ring
        _ = 245 := outer41RootDeterminant j)

private theorem outer41GammaModEightCoeffs :
    outer41GammaCoeffs.map (· % 8) =
      [7] ++ List.replicate 38 0 := by
  decide

private theorem outer41GammaModEight (j : Nat) :
    outer41Gamma j % 8 = 7 := by
  have h := outer41HornerNat_map_mod j 8 outer41GammaCoeffs
  rw [outer41GammaModEightCoeffs] at h
  simpa [outer41Gamma, outer41HornerNat] using h

set_option maxHeartbeats 3000000 in
private theorem outer41RootResidueTable (j : Nat) :
    (j % 5 ≠ 4 →
      outer41Gamma j % 5 ≠ 0 ∧ outer41Q37 j % 5 ≠ 0) ∧
    (j % 5 = 4 →
      outer41Gamma j % 25 = 20 ∧ outer41Q37 j % 25 = 5) ∧
    (j % 5 = 2 →
      outer41Gamma j % 5 = 2 ∧ outer41Q37 j % 5 = 3) := by
  have hGamma := outer41HornerNat_mod j 25 outer41GammaCoeffs
  have hQ37 := outer41HornerNat_mod j 25 outer41Q37Coeffs
  change outer41Gamma j % 25 = _ at hGamma
  change outer41Q37 j % 25 = _ at hQ37
  have hGamma5 : outer41Gamma j % 5 =
      (outer41Gamma j % 25) % 5 :=
    (Nat.mod_mod_of_dvd (outer41Gamma j) (by decide : 5 ∣ 25)).symm
  have hQ375 : outer41Q37 j % 5 =
      (outer41Q37 j % 25) % 5 :=
    (Nat.mod_mod_of_dvd (outer41Q37 j) (by decide : 5 ∣ 25)).symm
  have hj5 : j % 5 = (j % 25) % 5 :=
    (Nat.mod_mod_of_dvd j (by decide : 5 ∣ 25)).symm
  have hjbound : j % 25 < 25 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 25 <;>
    norm_num [outer41GammaCoeffs, outer41Q37Coeffs,
      outer41HornerNat] at hGamma hQ37
  all_goals
    norm_num [hcase, hGamma, hQ37] at hj5 hGamma5 hQ375
    simp [hj5, hGamma, hQ37, hGamma5, hQ375]

set_option maxHeartbeats 2000000 in
private theorem outer41AlphaGamma_not_both_five (j : Nat) :
    ¬(5 ∣ outer41Alpha j ∧ 5 ∣ outer41Gamma j) := by
  have hAlpha := outer41HornerNat_mod j 5 outer41AlphaCoeffs
  have hGamma := outer41HornerNat_mod j 5 outer41GammaCoeffs
  change outer41Alpha j % 5 = _ at hAlpha
  change outer41Gamma j % 5 = _ at hGamma
  intro hboth
  have hAlphaZero := Nat.dvd_iff_mod_eq_zero.mp hboth.1
  have hGammaZero := Nat.dvd_iff_mod_eq_zero.mp hboth.2
  have hjbound : j % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases hcase : j % 5 <;>
    norm_num [outer41AlphaCoeffs, outer41GammaCoeffs,
      outer41HornerNat] at hAlpha hGamma
  all_goals omega

private theorem outer41AlphaGamma_coprime (j : Nat) :
    (outer41Alpha j).Coprime (outer41Gamma j) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd (outer41Alpha j) (outer41Gamma j)
  have hgAlpha : (g : Int) ∣ outer41AlphaInt j := by
    rw [← outer41AlphaCast]
    exact_mod_cast Nat.gcd_dvd_left (outer41Alpha j) (outer41Gamma j)
  have hgGamma : (g : Int) ∣ outer41GammaInt j := by
    rw [← outer41GammaCast]
    exact_mod_cast Nat.gcd_dvd_right (outer41Alpha j) (outer41Gamma j)
  have hgFiveInt : (g : Int) ∣ (5 : Int) := by
    rw [← outer41RootEndpoint j]
    exact Int.dvd_add
      (dvd_mul_of_dvd_right hgGamma (outer41A38 j))
      (dvd_mul_of_dvd_right hgAlpha (outer41B38 j))
  have hgFive : g ∣ 5 := by exact_mod_cast hgFiveInt
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hgFive with hg | hg
  · exact hg
  · exfalso
    apply outer41AlphaGamma_not_both_five j
    rw [← hg]
    exact ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

private theorem outer41RootBaseCharacter
    {Q q L : Nat} (hQodd : Odd Q) (hqodd : Odd q) (hLodd : Odd L)
    (hmodEight : Q % 8 = q % 8) :
    qrSign Q q *
        (jacobiSym (-1 : Int) Q * jacobiSym (1 : Int) q *
          jacobiSym 2 Q ^ 5 * jacobiSym 2 q ^ 5 *
          qrSign Q L * qrSign q L * jacobiSym 2 L ^ (0 + 0) *
          jacobiSym (1 : Int) L) = 1 := by
  rw [outer41OrdinaryRawCharacter 5 0 0 1 1
    (Or.inl rfl) (Or.inl rfl) hQodd hqodd hLodd]
  rw [hmodEight]
  have hqmodTwo : q % 2 = 1 := Nat.odd_iff.mp hqodd
  have hLmodTwo : L % 2 = 1 := Nat.odd_iff.mp hLodd
  have hqmodTwoEight : q % 2 = (q % 8) % 2 :=
    (Nat.mod_mod_of_dvd q (by decide : 2 ∣ 8)).symm
  have hLmodTwoEight : L % 2 = (L % 8) % 2 :=
    (Nat.mod_mod_of_dvd L (by decide : 2 ∣ 8)).symm
  have hqbound : q % 8 < 8 := Nat.mod_lt _ (by decide)
  have hLbound : L % 8 < 8 := Nat.mod_lt _ (by decide)
  interval_cases hqcase : q % 8 <;> interval_cases hLcase : L % 8 <;>
    norm_num [outer41OrdinaryActualResidueSign,
      outer41QrResidueCharacter, outer41UnitResidueCharacter,
      outer41NegOneResidueCharacter, outer41TwoResidueCharacter] at * <;>
    omega

private theorem outer41Root_37_e_one
    (j : Nat) (hfour : j % 5 ≠ 4) (htwo : j % 5 ≠ 2) :
    jacobiSym (outer41Alpha j : Int) (outer41Gamma j) =
      jacobiSym (outer41P37 j : Int) (outer41Q37 j) := by
  let certificate := outer41RootLocalLink j
  let L := outer41RootL j
  have he : certificate.e = 1 := by
    rw [outer41RootE, if_neg hfour]
  have hh0 : certificate.h = certificate.h0 := by
    have hh := certificate.h_factor
    rw [he] at hh
    omega
  have hprimary : Nat.gcd 25 certificate.h = 1 := by
    rw [certificate.h_eq_gcd]
    simpa [hfour] using outer41RootPrimary j
  have hfiveH0 : (5 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactPrimary (by norm_num)
      (by norm_num) (by simpa [he] using certificate.h_factor)
      hprimary (by norm_num)
  have hfiveL : (5 : Nat).Coprime L := by
    simpa [L] using outer41RootL_coprime_five_of_not_mod_two j htwo
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 2 * L := by
    simpa [hh0, certificate, L] using outer41RootCrossReduced j
  have ht0 : certificate.t0 = (5 : Int) := by
    have ht := certificate.t_factor
    rw [he, (outer41RootConstants j).1] at ht
    norm_num at ht ⊢
    omega
  have hDelta0 : certificate.Delta0 = (245 : Int) := by
    have hDelta := certificate.Delta_factor
    rw [he, (outer41RootConstants j).2] at hDelta
    norm_num at hDelta ⊢
    omega
  have hQbar : certificate.h0 * certificate.Q0 = outer41Gamma j := by
    rw [← hh0, ← certificate.Q_factor]
  have hqbar : certificate.h0 * certificate.q0 = outer41Q37 j := by
    rw [← hh0, ← certificate.q_factor]
  have hQodd : Odd (certificate.h0 * certificate.Q0) := by
    rw [hQbar]
    exact outer41GammaOdd j
  have hqodd : Odd (certificate.h0 * certificate.q0) := by
    rw [hqbar]
    exact outer41Q37Odd j
  have hmodEight :
      (certificate.h0 * certificate.Q0) % 8 =
        (certificate.h0 * certificate.q0) % 8 := by
    rw [hQbar, hqbar, outer41GammaModEight, outer41Q37ModEight]
  have hbase := outer41RootBaseCharacter hQodd hqodd
    (outer41RootL_odd j) hmodEight
  have hresidue := (outer41RootResidueTable j).1 hfour
  have hfiveQbar : (5 : Nat).Coprime
      (certificate.h0 * certificate.Q0) := by
    rw [hQbar, (by norm_num : Nat.Prime 5).coprime_iff_not_dvd,
      Nat.dvd_iff_mod_eq_zero]
    exact hresidue.1
  have hfiveqbar : (5 : Nat).Coprime
      (certificate.h0 * certificate.q0) := by
    rw [hqbar, (by norm_num : Nat.Prime 5).coprime_iff_not_dvd,
      Nat.dvd_iff_mod_eq_zero]
    exact hresidue.2
  have hfiveQbarInt : Int.gcd (5 : Int)
      (certificate.h0 * certificate.Q0) = 1 := by
    exact_mod_cast hfiveQbar.gcd_eq_one
  have hfiveqbarInt : Int.gcd (5 : Int)
      (certificate.h0 * certificate.q0) = 1 := by
    exact_mod_cast hfiveqbar.gcd_eq_one
  have hfiveLInt : Int.gcd (5 : Int) L = 1 := by
    exact_mod_cast hfiveL.gcd_eq_one
  have hneutral :
      (jacobiSym (5 : Int) (certificate.h0 * certificate.Q0) ^ 2 *
          jacobiSym (5 : Int) (certificate.h0 * certificate.q0) ^ 2) *
        jacobiSym (5 : Int) L ^ (1 + 1) = 1 :=
    outer41PrimeNeutralOfEvenPowers hfiveQbarInt hfiveqbarInt
      hfiveLInt (by simp) (by simp)
  have hcharacter := outer41PrimeRawCharacter_of_neutral
    5 0 0 1 1 2 1 1 1 hbase hneutral
  have hdualRaw : Int.ModEq certificate.r
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta) := by
    simpa [certificate] using outer41RootDualEndpoint j
  rw [← one_mul
    (jacobiSym (outer41P37 j : Int) (outer41Q37 j))]
  apply outer41PrimeLinkFromReducedRaw (L := L) (a := 1) (b := 7)
    certificate 5 0 0 1 1 2 0 1 1 1 1 (Or.inl rfl) he
    (by norm_num) (outer41RootL_pos j) (outer41RootL_odd j)
    hfiveH0 hfiveL hcrossReduced
  · rw [ht0]
    norm_num
  · rw [hDelta0]
    norm_num
  · simp
  · simpa [L] using outer41RootL_coprime_seven j
  · exact outer41AlphaGamma_coprime j
  · exact hdualRaw
  · exact outer41RootCorrection j
  · simpa [L] using hcharacter

private theorem outer41Root_37_e_five
    (j : Nat) (hfour : j % 5 = 4) :
    jacobiSym (outer41Alpha j : Int) (outer41Gamma j) =
      jacobiSym (outer41P37 j : Int) (outer41Q37 j) := by
  let certificate := outer41RootLocalLink j
  let L := outer41RootL j
  have he : certificate.e = 5 := by
    rw [outer41RootE, if_pos hfour]
  have hh : certificate.h = 5 * certificate.h0 := by
    simpa [he] using certificate.h_factor
  have hprimary : Nat.gcd 25 certificate.h = 5 := by
    rw [certificate.h_eq_gcd]
    simpa [hfour] using outer41RootPrimary j
  have hfiveH0 : (5 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactPrimary (by norm_num)
      (by norm_num) (by simpa [he] using certificate.h_factor)
      hprimary (by norm_num)
  have hfiveL : (5 : Nat).Coprime L := by
    apply outer41RootL_coprime_five_of_not_mod_two
    omega
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 1 * L := by
    apply mul_left_cancel₀ (show (5 : Int) ≠ 0 by norm_num)
    calc
      (5 : Int) * ((certificate.h0 : Int) * certificate.r) =
          (certificate.h : Int) * certificate.r := by
            rw [hh]
            push_cast
            ring
      _ = (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 2 * L := by
            simpa [certificate, L] using outer41RootCrossReduced j
      _ = (5 : Int) *
          ((1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 1 * L) := by ring
  have ht0 : certificate.t0 = (1 : Int) := by
    have ht := certificate.t_factor
    rw [he, (outer41RootConstants j).1] at ht
    norm_num at ht ⊢
    omega
  have hDelta0 : certificate.Delta0 = (49 : Int) := by
    have hDelta := certificate.Delta_factor
    rw [he, (outer41RootConstants j).2] at hDelta
    norm_num at hDelta ⊢
    omega
  have hQfactor : outer41Gamma j =
      5 * (certificate.h0 * certificate.Q0) := by
    calc
      outer41Gamma j = certificate.h * certificate.Q0 := certificate.Q_factor
      _ = 5 * (certificate.h0 * certificate.Q0) := by rw [hh]; ring
  have hqfactor : outer41Q37 j =
      5 * (certificate.h0 * certificate.q0) := by
    calc
      outer41Q37 j = certificate.h * certificate.q0 := certificate.q_factor
      _ = 5 * (certificate.h0 * certificate.q0) := by rw [hh]; ring
  have hresidue := (outer41RootResidueTable j).2.1 hfour
  have hQrawFive : Nat.ModEq 25 (outer41Gamma j) (5 * 4) := by
    change outer41Gamma j % 25 = (5 * 4) % 25
    norm_num [hresidue.1]
  have hqrawFive : Nat.ModEq 25 (outer41Q37 j) (5 * 1) := by
    change outer41Q37 j % 25 = (5 * 1) % 25
    norm_num [hresidue.2]
  have hQbarFive :
      (certificate.h0 * certificate.Q0) % 5 = 4 := by
    have hmod := outer41ReducedFactorModAfterExact
      (Q := outer41Gamma j) (e := 5)
      (Q0 := certificate.h0 * certificate.Q0)
      (modulus := 5) (residue := 4)
      (by norm_num) (by norm_num) hQfactor hQrawFive
    exact hmod
  have hqbarFive :
      (certificate.h0 * certificate.q0) % 5 = 1 := by
    have hmod := outer41ReducedFactorModAfterExact
      (Q := outer41Q37 j) (e := 5)
      (Q0 := certificate.h0 * certificate.q0)
      (modulus := 5) (residue := 1)
      (by norm_num) (by norm_num) hqfactor hqrawFive
    exact hmod
  have hQbarEight :
      (certificate.h0 * certificate.Q0) % 8 = 3 := by
    exact outer41ReducedFactorMod
      (Q := outer41Gamma j) (e := 5)
      (Q0 := certificate.h0 * certificate.Q0)
      (modulus := 8) (residue := 3) hQfactor (by norm_num) (by
        rw [outer41GammaModEight])
  have hqbarEight :
      (certificate.h0 * certificate.q0) % 8 = 3 := by
    exact outer41ReducedFactorMod
      (Q := outer41Q37 j) (e := 5)
      (Q0 := certificate.h0 * certificate.q0)
      (modulus := 8) (residue := 3) hqfactor (by norm_num) (by
        rw [outer41Q37ModEight])
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  have hQodd : Odd (certificate.h0 * certificate.Q0) :=
    hh0odd.mul certificate.Q0_odd
  have hqodd : Odd (certificate.h0 * certificate.q0) :=
    hh0odd.mul certificate.q0_odd
  have hbase := outer41RootBaseCharacter hQodd hqodd
    (outer41RootL_odd j) (hQbarEight.trans hqbarEight.symm)
  have hQsymbol :
      jacobiSym (((5 : Nat) : Int))
        (certificate.h0 * certificate.Q0) = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
      (by norm_num : 5 % 4 = 1) hQodd,
      outer41JacobiNat_mod (certificate.h0 * certificate.Q0) 5,
      hQbarFive]
    norm_num
  have hqsymbol :
      jacobiSym (((5 : Nat) : Int))
        (certificate.h0 * certificate.q0) = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
      (by norm_num : 5 % 4 = 1) hqodd,
      outer41JacobiNat_mod (certificate.h0 * certificate.q0) 5,
      hqbarFive]
    norm_num
  have hneutral :
      (jacobiSym (((5 : Nat) : Int))
            (certificate.h0 * certificate.Q0) ^ 1 *
          jacobiSym (((5 : Nat) : Int))
            (certificate.h0 * certificate.q0) ^ 1) *
        jacobiSym (((5 : Nat) : Int)) L ^ (0 + 0) = 1 := by
    rw [hQsymbol, hqsymbol]
    norm_num
  have hcharacter := outer41PrimeRawCharacter_of_neutral
    5 0 0 0 0 1 1 1 1 hbase hneutral
  have hdualRaw : Int.ModEq certificate.r
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta) := by
    simpa [certificate] using outer41RootDualEndpoint j
  rw [← one_mul
    (jacobiSym (outer41P37 j : Int) (outer41Q37 j))]
  apply outer41PrimeLinkFromReducedRaw (L := L) (a := 1) (b := 7)
    certificate 5 0 0 0 0 1 1 1 1 1 1 (Or.inl rfl) he
    (by norm_num) (outer41RootL_pos j) (outer41RootL_odd j)
    hfiveH0 hfiveL hcrossReduced
  · rw [ht0]
    norm_num
  · rw [hDelta0]
    norm_num
  · simp
  · simpa [L] using outer41RootL_coprime_seven j
  · exact outer41AlphaGamma_coprime j
  · exact hdualRaw
  · exact outer41RootCorrection j
  · simpa [L] using hcharacter

private def outer41RootDivFiveL (j : Nat) : Nat :=
  9 + 14 * (j / 5)

private theorem outer41RootDivFiveL_reconstruct
    (j : Nat) (hj : j % 5 = 2) :
    outer41RootL j = 5 * outer41RootDivFiveL j := by
  have hdecomp : 5 * (j / 5) + 2 = j := by
    have hdivision := Nat.mod_add_div j 5
    omega
  calc
    outer41RootL j = 17 + 14 * (5 * (j / 5) + 2) := by
      simpa [outer41RootL] using
        (congrArg (fun n : Nat => 17 + 14 * n) hdecomp).symm
    _ = 5 * outer41RootDivFiveL j := by
      simp [outer41RootDivFiveL]
      ring

private theorem outer41RootDivFiveL_pos (j : Nat) :
    0 < outer41RootDivFiveL j := by
  simp [outer41RootDivFiveL]

private theorem outer41RootDivFiveL_odd (j : Nat) :
    Odd (outer41RootDivFiveL j) := by
  rw [Nat.odd_iff]
  norm_num [outer41RootDivFiveL, Nat.add_mod, Nat.mul_mod]

private theorem outer41RootDivFiveL_coprime_seven (j : Nat) :
    (7 : Nat).Coprime (outer41RootDivFiveL j) := by
  change (7 : Nat).Coprime (9 + 14 * (j / 5))
  convert (Nat.coprime_add_mul_right_right 7 9 (2 * (j / 5))).mpr
    (by norm_num) using 1
  ring

set_option maxHeartbeats 3000000 in
private theorem outer41Root_37_extra_five
    (j : Nat) (htwo : j % 5 = 2) :
    jacobiSym (outer41Alpha j : Int) (outer41Gamma j) =
      jacobiSym (outer41P37 j : Int) (outer41Q37 j) := by
  let certificate := outer41RootLocalLink j
  let L := outer41RootL j
  let L1 := outer41RootDivFiveL j
  have hfour : j % 5 ≠ 4 := by omega
  have he : certificate.e = 1 := by
    rw [outer41RootE, if_neg hfour]
  have hh0 : certificate.h = certificate.h0 := by
    have hh := certificate.h_factor
    rw [he] at hh
    omega
  have hprimary : Nat.gcd 25 certificate.h = 1 := by
    rw [certificate.h_eq_gcd]
    simpa [hfour] using outer41RootPrimary j
  have hfiveH0 : (5 : Nat).Coprime certificate.h0 :=
    outer41PrimeCoprimeAfterExactPrimary (by norm_num)
      (by norm_num) (by simpa [he] using certificate.h_factor)
      hprimary (by norm_num)
  have hLfive : L = 5 * L1 := by
    simpa [L, L1] using outer41RootDivFiveL_reconstruct j htwo
  have hcrossReduced : (certificate.h0 : Int) * certificate.r =
      (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 3 * L1 := by
    calc
      (certificate.h0 : Int) * certificate.r =
          (certificate.h : Int) * certificate.r := by rw [hh0]
      _ = (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 2 * L := by
          simpa [certificate, L] using outer41RootCrossReduced j
      _ = (1 : Int) * (2 : Int) ^ 5 * (5 : Int) ^ 3 * L1 := by
          rw [hLfive]
          push_cast
          ring
  have hh0odd : Odd certificate.h0 := by
    have hproduct : Odd (certificate.e * certificate.h0) := by
      simpa [certificate.h_factor] using certificate.h_odd
    exact Nat.Odd.of_mul_right hproduct
  obtain ⟨R, hLfactor, hRodd, hrfactor⟩ :=
    outer41ExtractOddPrimeCross 5 3 1 certificate.h0_pos hh0odd
      (outer41RootDivFiveL_odd j) (Or.inl rfl) hfiveH0 hcrossReduced
  have hRpos : 0 < R := by
    by_contra hR
    have : R = 0 := Nat.eq_zero_of_not_pos hR
    rw [this, mul_zero] at hLfactor
    have hL1pos : 0 < L1 := by
      simpa [L1] using outer41RootDivFiveL_pos j
    omega
  have hQ0total : certificate.Q0.Coprime (5 ^ 3 * R) := by
    apply (outer41FactorCoprime (R := 5 ^ 3 * R)
      (n := certificate.Q0) (w := 5) (s := 1) (Or.inl rfl) _
      (outer41LocalLink_r_coprime_Q0 certificate
        (outer41AlphaGamma_coprime j))).symm
    rw [hrfactor]
    push_cast
    ring
  have hQ0R : certificate.Q0.Coprime R :=
    hQ0total.of_dvd_right ⟨5 ^ 3, by ring⟩
  have hdualRaw : Int.ModEq certificate.r
      ((certificate.q0 : Int) * certificate.t)
      ((certificate.Q0 : Int) * certificate.Delta) := by
    simpa [certificate] using outer41RootDualEndpoint j
  have hfiveRdvd : ((5 : Int) * R) ∣ certificate.r := by
    refine ⟨(2 : Int) ^ 5 * (5 : Int) ^ 2, ?_⟩
    rw [hrfactor]
    push_cast
    ring
  have hdualFiveR := hdualRaw.of_dvd hfiveRdvd
  have hdualFactored : Int.ModEq ((5 : Int) * R)
      ((5 : Int) * ((certificate.q0 : Int) * (1 : Int)))
      ((5 : Int) * ((certificate.Q0 : Int) * (49 : Int))) := by
    rw [(outer41RootConstants j).1,
      (outer41RootConstants j).2] at hdualFiveR
    convert hdualFiveR using 1 <;> ring
  have hendpoint : Int.ModEq R
      ((certificate.q0 : Int) * (1 : Int))
      ((certificate.Q0 : Int) * (49 : Int)) :=
    hdualFactored.mul_left_cancel' (by norm_num)
  have hprime := outer41PrimeExceptionalCrossProduct
    (Q0 := certificate.Q0) (q0 := certificate.q0)
    (h := certificate.h0) (R := R) (L := L1)
    (a := 1) (b := 7) (z := 5)
    (r := certificate.r) (t := (1 : Int)) (Delta := (49 : Int))
    5 0 0 0 0 3 1 1 certificate.h0_pos hRpos
    certificate.Q0_odd certificate.q0_odd hRodd hLfactor
    hrfactor (by norm_num) (by norm_num) (by simp)
    (by simpa [L1] using outer41RootDivFiveL_coprime_seven j)
    (by simp) hQ0R hendpoint
  have hsevenH0 : (7 : Nat).Coprime certificate.h0 :=
    (outer41RootDivFiveL_coprime_seven j).of_dvd_right
      ⟨R, by simpa [L1] using hLfactor⟩
  have hsevenH0Int : Int.gcd (7 : Int) certificate.h0 = 1 := by
    exact_mod_cast hsevenH0.gcd_eq_one
  have hsynthetic :
      jacobiSym (1 : Int) certificate.h0 *
          jacobiSym (49 : Int) certificate.h0 = 1 := by
    rw [show (49 : Int) = (7 : Int) ^ 2 by norm_num,
      jacobiSym.one_left, jacobiSym.sq_one' hsevenH0Int]
    norm_num
  have ht0 : certificate.t0 = (5 : Int) := by
    have ht := certificate.t_factor
    rw [he, (outer41RootConstants j).1] at ht
    norm_num at ht ⊢
    omega
  have hDelta0 : certificate.Delta0 = (245 : Int) := by
    have hDelta := certificate.Delta_factor
    rw [he, (outer41RootConstants j).2] at hDelta
    norm_num at hDelta ⊢
    omega
  have hfiveH0Int : Int.gcd (5 : Int) certificate.h0 = 1 := by
    exact_mod_cast hfiveH0.gcd_eq_one
  have hsecondary :
      jacobiSym certificate.t0 certificate.h0 *
          jacobiSym certificate.Delta0 certificate.h0 = 1 := by
    rw [ht0, hDelta0]
    calc
      jacobiSym (5 : Int) certificate.h0 *
          jacobiSym (245 : Int) certificate.h0 =
          jacobiSym (5 : Int) certificate.h0 ^ 2 *
            jacobiSym (7 : Int) certificate.h0 ^ 2 := by
              rw [show (245 : Int) = (5 : Int) * 7 ^ 2 by norm_num,
                jacobiSym.mul_left, jacobiSym.pow_left]
              ring
      _ = 1 := by
        rw [jacobiSym.sq_one hfiveH0Int,
          jacobiSym.sq_one hsevenH0Int]
        norm_num
  have hcrossSymbols :
      jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 =
        jacobiSym (-1 : Int) certificate.Q0 *
          jacobiSym (1 : Int) certificate.q0 *
          jacobiSym 2 certificate.Q0 ^ 5 *
          jacobiSym 2 certificate.q0 ^ 5 *
          jacobiSym (5 : Int) certificate.Q0 ^ 3 *
          jacobiSym (5 : Int) certificate.q0 ^ 3 *
          qrSign certificate.Q0 R * qrSign certificate.q0 R := by
    have hprime' := hprime
    rw [hsynthetic, one_mul] at hprime'
    simpa only [pow_zero, one_mul, mul_one, Nat.zero_add,
      jacobiSym.one_left, Nat.cast_ofNat] using hprime'
  have hQbar : certificate.h0 * certificate.Q0 = outer41Gamma j := by
    rw [← hh0, ← certificate.Q_factor]
  have hqbar : certificate.h0 * certificate.q0 = outer41Q37 j := by
    rw [← hh0, ← certificate.q_factor]
  have hhEight : Nat.gcd 8 certificate.h0 = 1 := by
    have hcop : certificate.h0.Coprime (2 ^ 3) :=
      hh0odd.coprime_two_right.pow_right 3
    simpa using hcop.symm.gcd_eq_one
  have hrawEight : outer41Gamma j % 8 = outer41Q37 j % 8 := by
    rw [outer41GammaModEight, outer41Q37ModEight]
  have hmodEight : certificate.Q0 % 8 = certificate.q0 % 8 :=
    outer41ReducedFactorsModEq
      hQbar.symm hqbar.symm
      hhEight hrawEight
  have hbase := outer41RootBaseCharacter certificate.Q0_odd
    certificate.q0_odd hRodd hmodEight
  have hresidue := (outer41RootResidueTable j).2.2 htwo
  have hfiveQbar : (5 : Nat).Coprime
      (certificate.h0 * certificate.Q0) := by
    rw [hQbar, (by norm_num : Nat.Prime 5).coprime_iff_not_dvd,
      Nat.dvd_iff_mod_eq_zero, hresidue.1]
    norm_num
  have hfiveqbar : (5 : Nat).Coprime
      (certificate.h0 * certificate.q0) := by
    rw [hqbar, (by norm_num : Nat.Prime 5).coprime_iff_not_dvd,
      Nat.dvd_iff_mod_eq_zero, hresidue.2]
    norm_num
  have hfiveQ0 : (5 : Nat).Coprime certificate.Q0 :=
    hfiveQbar.of_dvd_right ⟨certificate.h0, by ring⟩
  have hfiveq0 : (5 : Nat).Coprime certificate.q0 :=
    hfiveqbar.of_dvd_right ⟨certificate.h0, by ring⟩
  have hfactoredFive : Nat.ModEq 5
      (certificate.h0 * (4 * certificate.Q0))
      (certificate.h0 * certificate.q0) := by
    change (certificate.h0 * (4 * certificate.Q0)) % 5 =
      (certificate.h0 * certificate.q0) % 5
    rw [show certificate.h0 * (4 * certificate.Q0) =
      4 * (certificate.h0 * certificate.Q0) by ring,
      hQbar, hqbar, Nat.mul_mod, hresidue.1, hresidue.2]
  have hmodFive : Nat.ModEq 5 (4 * certificate.Q0) certificate.q0 :=
    hfactoredFive.cancel_left_of_coprime hfiveH0.gcd_eq_one
  have hmodFiveInt : Int.ModEq 5
      ((4 : Int) * certificate.Q0) certificate.q0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      AddCommGroup.modEq_iff_intModEq.mp
        (AddCommGroup.ModEq.natCast (M := Int) hmodFive)
  have hsame :
      jacobiSym (((5 : Nat) : Int)) certificate.Q0 =
        jacobiSym (((5 : Nat) : Int)) certificate.q0 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
      (by norm_num : 5 % 4 = 1) certificate.Q0_odd,
      jacobiSym.quadratic_reciprocity_one_mod_four
        (by norm_num : 5 % 4 = 1) certificate.q0_odd]
    calc
      jacobiSym (certificate.Q0 : Int) 5 =
          jacobiSym ((4 : Int) * certificate.Q0) 5 := by
        symm
        rw [jacobiSym.mul_left, jacobiSym.at_four (by norm_num : Odd 5), one_mul]
      _ = jacobiSym (certificate.q0 : Int) 5 :=
        jacobiSym.mod_left' hmodFiveInt.eq
  have hfiveq0Int : Int.gcd (5 : Int) certificate.q0 = 1 := by
    exact_mod_cast hfiveq0.gcd_eq_one
  have hneutral :
      (jacobiSym (((5 : Nat) : Int)) certificate.Q0 ^ 3 *
          jacobiSym (((5 : Nat) : Int)) certificate.q0 ^ 3) *
        jacobiSym (((5 : Nat) : Int)) R ^ (0 + 0) = 1 := by
    have hqSquare :
        jacobiSym (((5 : Nat) : Int)) certificate.q0 ^ 2 = 1 := by
      simpa only [Nat.cast_ofNat] using jacobiSym.sq_one hfiveq0Int
    rw [pow_zero, mul_one, hsame]
    calc
      jacobiSym (((5 : Nat) : Int)) certificate.q0 ^ 3 *
          jacobiSym (((5 : Nat) : Int)) certificate.q0 ^ 3 =
          (jacobiSym (((5 : Nat) : Int)) certificate.q0 ^ 2) ^ 3 := by
            ring
      _ = 1 := by
        rw [hqSquare]
        norm_num
  have hcharacter := outer41PrimeRawCharacter_of_neutral
    5 0 0 0 0 3 1 1 1 hbase hneutral
  have hfactored := outer41FactoredLinkTransfer certificate
  calc
    jacobiSym (outer41Alpha j : Int) (outer41Gamma j) =
        qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (outer41Alpha j : Int) certificate.e *
            jacobiSym (outer41P37 j : Int) certificate.e) *
          (jacobiSym certificate.t0 certificate.h0 *
            jacobiSym certificate.Delta0 certificate.h0) *
          jacobiSym (-certificate.r) certificate.Q0 *
          jacobiSym certificate.r certificate.q0 *
          jacobiSym (outer41P37 j : Int) (outer41Q37 j) := hfactored
    _ = qrSign certificate.Q0 certificate.q0 *
          (jacobiSym (-certificate.r) certificate.Q0 *
            jacobiSym certificate.r certificate.q0) *
          jacobiSym (outer41P37 j : Int) (outer41Q37 j) := by
      rw [outer41RootCorrection j, hsecondary]
      ring
    _ = outer41PrimeRawCharacter 5 0 0 0 0 3 1 1 5
          certificate.Q0 certificate.q0 R *
          jacobiSym (outer41P37 j : Int) (outer41Q37 j) := by
      rw [hcrossSymbols]
      simp only [outer41PrimeRawCharacter, pow_zero, mul_one,
        Nat.zero_add, jacobiSym.one_left]
      ring
    _ = _ := by rw [hcharacter, one_mul]

private theorem outer41Root_37 (j : Nat) :
    jacobiSym (outer41Alpha j : Int) (outer41Gamma j) =
      jacobiSym (outer41P37 j : Int) (outer41Q37 j) := by
  by_cases hfour : j % 5 = 4
  · exact outer41Root_37_e_five j hfour
  · by_cases htwo : j % 5 = 2
    · exact outer41Root_37_extra_five j htwo
    · exact outer41Root_37_e_one j hfour htwo

private theorem outer41Link25_21 (j : Nat) :
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
      -jacobiSym (outer41P21 j : Int) (outer41Q21 j) := by
  calc
    jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
        (-ss41_factor13Multiplier j) *
          jacobiSym (outer41ReducedP23 j : Int)
            (outer41ReducedQ23 j) := outer41Link25_23 j
    _ = (-ss41_factor13Multiplier j) *
          (ss41_factor13Multiplier j *
            jacobiSym (outer41P21 j : Int) (outer41Q21 j)) := by
      rw [outer41Link23_21]
    _ = -jacobiSym (outer41P21 j : Int) (outer41Q21 j) := by
      calc
        (-ss41_factor13Multiplier j) *
            (ss41_factor13Multiplier j *
              jacobiSym (outer41P21 j : Int) (outer41Q21 j)) =
            -(ss41_factor13Multiplier j ^ 2) *
              jacobiSym (outer41P21 j : Int) (outer41Q21 j) := by ring
        _ = -jacobiSym (outer41P21 j : Int) (outer41Q21 j) := by
          rw [ss41_factor13Multiplier_sq]
          ring

private theorem outer41DirectedTelescope (j : Nat) :
    jacobiSym (outer41Alpha j : Int) (outer41Gamma j) =
      jacobiSym (outer41P1 j : Int) (outer41Q1 j) := by
  rw [outer41Root_37, outer41Link37_35, outer41Link35_33,
    outer41Link33_31, outer41Link31_29, outer41Link29_27,
    outer41Link27_25, outer41Link25_21, outer41Link21_19,
    outer41Link19_17, outer41Link17_15, outer41Link15_13,
    outer41Link13_11, outer41Link11_9, outer41Link9_7,
    outer41Link7_5, outer41Link5_3, outer41Link3_1]
  ring

/-- The exceptional factor-13 links compose without any uncancelled moving
symbol. -/
theorem ss41_factor13_block_25_21 (j : Nat) :
    jacobiSym
        ((ss41_localCertificate j).P ⟨6, by decide⟩ : Int)
        ((ss41_localCertificate j).Q ⟨6, by decide⟩) =
      -jacobiSym
        ((ss41_localCertificate j).P ⟨8, by decide⟩ : Int)
        ((ss41_localCertificate j).Q ⟨8, by decide⟩) := by
  change jacobiSym (outer41P25 j : Int) (outer41Q25 j) =
    -jacobiSym (outer41P21 j : Int) (outer41Q21 j)
  exact outer41Link25_21 j

/-- Direct fixed-41 terminal transfer from coefficient index `3` to the
degree-one endpoint. -/
theorem ss41_direct_endpoint_3_1 (j : Nat) :
    jacobiSym
        ((ss41_localCertificate j).P ⟨17, by decide⟩ : Int)
        ((ss41_localCertificate j).Q ⟨17, by decide⟩) =
      -jacobiSym
        ((ss41_localCertificate j).P ⟨18, by decide⟩ : Int)
        ((ss41_localCertificate j).Q ⟨18, by decide⟩) := by
  change jacobiSym (outer41P3 j : Int) (outer41Q3 j) =
    -jacobiSym (outer41P1 j : Int) (outer41Q1 j)
  exact outer41Link3_1 j

/-- The complete universal directed telescope from the determinant-245 root
to the degree-one endpoint of the fixed-41 coefficient chain. -/
theorem ss41_directedTelescope (j : Nat) :
    jacobiSym ((ss41_localCertificate j).rootP : Int)
        (ss41_localCertificate j).rootQ =
      jacobiSym
        ((ss41_localCertificate j).P ⟨18, by decide⟩ : Int)
        ((ss41_localCertificate j).Q ⟨18, by decide⟩) := by
  change jacobiSym (outer41Alpha j : Int) (outer41Gamma j) =
    jacobiSym (outer41P1 j : Int) (outer41Q1 j)
  exact outer41DirectedTelescope j

/-- The universal coefficient Jacobi theorem required by
`ss41_globalJacobiTransfer`.  This is not by itself a pure `SS41` theorem. -/
theorem ss41_coefficientJacobi (j : Nat) :
    jacobiSym ((ss41_localCertificate j).rootP : Int)
      (ss41_localCertificate j).rootQ = 1 := by
  rw [ss41_directedTelescope,
    (ss41_localCertificate j).terminal_P,
    (ss41_localCertificate j).terminal_Q]
  norm_num

/-! ## Pure fixed-`41` shifted-square obstruction -/

private def outer41MainQ0Coeffs : List Nat := [121772437791801274596617268962070420678645127024280409,3974313822528288004147515193066298439644909556142752328,63281291295004382603320153705792476550097844461825561600,655021786100065053723345148151333365489395561278535413760,4955303868638739531007534058707669046684510541967468134400,29204302287745041940282594713798367381047493369943756898304,139571515513617799814899501097760756119779032085893029560320,555929083392849727009957838838055015605965169237766132727808,1882412557668623753868480623909337321548605032876923745730560,5499796527584925776897505825278813529035374268554418189238272,14025258665607375525975341199748825427615957821260836739481600,31502721215793365576910838008313983696981077067219415313940480,62778389195391185820505298346965401541230330931911319355392000,111645395579498110959762698606821024770006665867896959480627200,178033092335180572398957405288703404133803279324607317803008000,255538940463036902027809754024255821967835637714687773911285760,331167902946447087880739783770390632194553773702126441909452800,388446354076609283323080572910132288467199414833470017078558720,413157327954369694531275874187953424892752035977085262915174400,399015096493449575250717909221962037530286574472789057685422080,350215700661529315230637621334868005585784571969469627655782400,279475144518792806383518656288910640782782944850691061469675520,202773907003136832458356472125876594077126422078552090345472000,133706769988142324465769630818330681578772098783822260417331200,80054220703797567714235313259818009835309426806091895799808000,43462703983086877684482981392869757160088888187325329027629056,21357037286063213643128548015736381627789362092443817612410880,9475457260547767879115136962940316279252374946909182599626752,3784041739379713902311898591528585293239560556653349112381440,1355005580635439308563395093421766109047149687674853274943488,433007058052579054734244989056318131943798995541514382213120,122764831201064868284882676162881917801903858625802997334016,30656750295462893222008246996469069207190526790917213388800,6682068839004028950287875431246880537204110829563024506880,1256702349504353667686798200751546229679337217411199795200,200921773845671324313710959598302894557175610362482917376,26772844855905888549956483976582068904442893155623239680,2892915676392500208695617409875495979961126128778739712,243522653230353990507293742919911880170364304663511040,14982264331614585130951718006533818689092242729074688,599215671305670196463510781413676038058932342620160,11692013098647223345629478661730264157247460343808]
private def outer41MainQ1Coeffs : List Nat := [57592395689789572353787555566335921220845468686696291,1836395690665850400835795945067769016894695187023730784,28549295108486719554913588062552672863800085732655533568,288340493247028256293259246367842173676138839338521980928,2126907853669281339322390454154905041495598094387988004864,12213380423932766092592825491187934050494214166273371144192,56827795571008206534002352558086336842580179018868536115200,220192865920869358914798744788453918677113749564443678736384,724673184637276267465058718983146104366332607312821642854400,2055976288528473415298385563163742085691652632196534824337408,5086296756413981733860673009970289852342208614938240520028160,11071478832291387531687172806148463270696941385534664337260544,21357540409469818304104793016224779565043815056275064123031552,36723854713597272119835913364735296798920900206656309652619264,56548337417504128449274230913999918463890154511436379655766016,78269273298833524433882040935667152781613534186634376787263488,97668436100051401870576404731357910368125448937632094134206464,110131868799141956502126713140316696146053963223093033836740608,112413470998931827418292050803338686752554686144163964069609472,103989869836016542817229092638865303721944722209778734125285376,87244392990520409880040103349920637681205968955541185311539200,66398616298729035427629974176868458743316327097888558328840192,45830477271732517177555939546405454254036265168997479759216640,28669302372718009682688022613137256965140687186466545887870976,16234037472946867707071789661126016367598416795856701830987776,8306765280194009927664921668900190665796987618665974269476864,3832030627276123098291345546678275037279741927822646013067264,1589008002062336715552466668057260679213575497615146672455680,590062460959809833564627300805228232274722160812843442634752,195308693809715890360621231745142300986456691145410443476992,57291095688028428560834470266143631374708472777294938636288,14786771405463297359317986774144253298202706156655650799616,3327879857937535267266228164758943967067060266204840067072,645653161724091158952624018081342051286213031256846761984,106396629574315922327540737641946222545905786928096083968,14600725476907248284994561222748580152276246774729932800,1623525876254832660907008459127669073909243990926950400,140536359679012244525502819130847831874445474130821120,8884879500670058156205944884441485931087692159778816,364918690071059822388982556668846916470340656824320,7307508186654514591018424163581415098279662714880]
private def outer41BetaCoeffs : List Nat := [3724388006819626504237162166111994089780986814228167,112517212055814823287097348343773308829068695516895184,1655110461405976620254337005110307711784688128762410496,15794299178950161900962706454645092033538180063775014912,109914850641861925804665500189001797308462057242144276480,594523561803300705261555461558242850856002169737637265408,2601305514786876874368827591353274985553936304435009421312,9461472082702825481452258000572421518695406334583051911168,29174380128153175600605822063386808185579048651468860030976,77394019397638797507801468388601780411254058594827048583168,178643910313063649313660651652376555998173677186790035816448,361986331998358199374856230474760997736059240738333346758656,648438946193125565592396816221502756944477179062703601221632,1032640789467880369413741067463394405902990003347238714081280,1468477253712507295265707080097231494946576323015086195081216,1871323909787819104195841938821823179938051911085344883212288,2142764113860996001168113324551322296397635135225910718889984,2209130910593511517713689547813329097960895043689899976818688,2053512521150883704774849822782582928303417180515135880429568,1722497692514500100526730309445661294243146391270743429087232,1304136169579198935321644259629599225595746203444608677969920,890989581100212677595856489268852406087389209473309701308416,548846796008449560396257330438265685378750895875337316466688,304404691999361977697795588506828189596567754948689143005184,151703367342706655071523168180137109105524347421357793869824,67749003636047398597511985544525551772374472050882417524736,27017700922395768773369462578472638501762205796689057415168,9578492390100133985877965656938281380757331427738915962880,3002056896878717583047900204708684927992603880061541548032,825969202441545191828401473991044245207957608681036578816,197735149168141698316023275974658083586206683792305815552,40725533041462863751439606900391458487927485415404077056,7110911885707525507133479427568055089930246777827491840,1032116983547103478350910687972350220664746761676390400,121183138684568427643430556789287519585387706434191360,11058907022495853683698202600599168989301999604334592,735978135640732235696841530256968558413329586978816,31774815382712784832000620537854110221289088090112,667951920186389224335277833702363723827125420032]
private def outer41DeltaCoeffs : List Nat := [1362235444993468262421572550983418510082416621913967,42171788767986112393465154441761579845743071668672304,636112037015098476642247547344979148868975877803431936,6229092865488720794446742948429633722830623969576681472,44517498357142570603748336269922768291015563086438858752,247482744601759492119521004225628424366364260807074643968,1113887682045174389761111052807827103763254910775457742848,4171370578498030845976079305194434135122937421640822161408,13256011812991347265902531579951798377121170086608657973248,36279292838238125752562675277352548210412104834504212873216,86488711550423189573262042459258078265661108894530915008512,181216065734348019318559094889930288167749222343923564806144,336091882541788908727226106876172340314022793409788974727168,554901047208075298672763258273899203690565063521303084924928,819314273268966578037175742080106861337671704545694945640448,1085779094997759496454306035493500155530884535513333914140672,1295172063806678181920866858741361924721116052813995787157504,1393649720671743673208452906340067805986634501926005831106560,1354888511403239861980414653358492697787850907264433818435584,1191300977147289960916652012357450351540594857326604697206784,947820771754106572056953350258576638078131131257730040332288,682366538083115437472822509307205871294857402581671309475840,444300905213199992444525860671589115435964731017991680950272,261372796227136331884842689141245669363364140690365248176128,138702300589434613605038101925032403206946637142771537805312,66252441020094496753771706888169788547409474012331083038720,28403768336445204129950470908248363772111278172439020830720,10889986775372736644860231220809534001259167815417991266304,3716847766613987563042280687140870391554089256631480090624,1122912883122273556572086166765664362861410259248261103616,298163036625438392964364008588429181692671398717069197312,68962975946838164952954921725569248190128543689517039616,13736932213839140819985016390101184689835549030239698944,2321988037872848170477654310825057601667474954033037312,326565873930375047177520944269209766919357131640537088,37184642165434085888269903171308086092008094160650240,3293550293708306413056682431286218767204169598107648,212901824697101682477523988919796464746646122528768,8934570556339308855424870168753839553755993866240,182687704666362864775460604089535377456991567872]

private def outer41MainQ0 (j : Nat) :=
  outer41HornerNat j outer41MainQ0Coeffs

private def outer41MainQ1 (j : Nat) :=
  outer41HornerNat j outer41MainQ1Coeffs

private def outer41Beta (j : Nat) :=
  outer41HornerNat j outer41BetaCoeffs

private def outer41Delta (j : Nat) :=
  outer41HornerNat j outer41DeltaCoeffs

private def outer41MainQ39Coeffs : List Nat := [1433, 2400, 1024]

private def outer41MainQ39 (j : Nat) :=
  outer41HornerNat j outer41MainQ39Coeffs

private def outer41MainRealCoeffs : Nat → List Int
  | 0 => [1]
  | 1 => [10, 8]
  | n + 2 =>
      outer41CoeffAdd
        (outer41CoeffMul [20, 16] (outer41MainRealCoeffs (n + 1)))
        (outer41MainRealCoeffs n)

private theorem outer41HornerInt_append_zeros
    (j : Int) (coefficients : List Int) (count : Nat) :
    outer41HornerInt j (coefficients ++ List.replicate count 0) =
      outer41HornerInt j coefficients := by
  induction coefficients with
  | nil =>
      induction count with
      | zero => simp [outer41HornerInt]
      | succ count ih =>
          rw [List.replicate_succ]
          have hzero :
              outer41HornerInt j (List.replicate count 0) = 0 := by
            simpa [outer41HornerInt] using ih
          simp [outer41HornerInt, hzero]
  | cons coefficient coefficients ih =>
      simp [outer41HornerInt, ih]

private theorem outer41MainRealCoeffs_eval (j n : Nat) :
    outer41HornerInt (j : Int) (outer41MainRealCoeffs n) =
      (sm2LucasReal (8 * j + 10) n : Int) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [outer41MainRealCoeffs, outer41HornerInt]
  | one =>
      simp [outer41MainRealCoeffs, outer41HornerInt, sm2LucasReal]
      ring
  | more n h0 h1 =>
      rw [outer41MainRealCoeffs, outer41HornerInt_add,
        outer41HornerInt_mul, h1, h0, sm2LucasReal_succ_succ]
      simp only [outer41HornerInt, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem outer41MainRealCoeffs_fortyOne :
    outer41MainRealCoeffs 41 =
      outer41CoeffAdd [1]
        (outer41NatCoeffs outer41MainQ0Coeffs) := by
  decide

set_option maxHeartbeats 1000000 in
private theorem outer41MainReal_eq (j : Nat) :
    sm2LucasReal (8 * j + 10) 41 = outer41MainQ0 j + 1 := by
  have hEval := outer41MainRealCoeffs_eval j 41
  have hCast :
      (sm2LucasReal (8 * j + 10) 41 : Int) =
        (outer41MainQ0 j : Int) + 1 := by
    calc
      (sm2LucasReal (8 * j + 10) 41 : Int) =
          outer41HornerInt (j : Int)
            (outer41MainRealCoeffs 41) := hEval.symm
      _ = outer41HornerInt (j : Int)
          (outer41CoeffAdd [1]
            (outer41NatCoeffs outer41MainQ0Coeffs)) := by
              rw [outer41MainRealCoeffs_fortyOne]
      _ = outer41HornerInt (j : Int) [1] +
          outer41HornerInt (j : Int)
            (outer41NatCoeffs outer41MainQ0Coeffs) := by
              rw [outer41HornerInt_add]
      _ = 1 + (outer41MainQ0 j : Int) := by
              change 1 + outer41HornerInt (j : Int)
                  (outer41NatCoeffs outer41MainQ0Coeffs) =
                1 + (outer41HornerNat j outer41MainQ0Coeffs : Int)
              rw [← outer41HornerNat_cast]
      _ = (outer41MainQ0 j : Int) + 1 := by ring
  exact_mod_cast hCast

set_option maxHeartbeats 3000000 in
private theorem outer41MainRowCoeffs :
    outer41CoeffSub
      (outer41CoeffScale 2
        (outer41CoeffMul
          (outer41NatCoeffs outer41AlphaCoeffs)
          (outer41NatCoeffs outer41MainQ0Coeffs)))
      (outer41CoeffMul
        (outer41NatCoeffs outer41BetaCoeffs)
        (outer41NatCoeffs outer41MainQ1Coeffs)) =
      outer41NatCoeffs outer41MainQ39Coeffs ++
        List.replicate 76 0 := by
  decide

set_option maxHeartbeats 3000000 in
private theorem outer41MainBezoutCoeffs :
    outer41CoeffSub
      (outer41CoeffScale 2
        (outer41CoeffMul
          (outer41NatCoeffs outer41GammaCoeffs)
          (outer41NatCoeffs outer41MainQ0Coeffs)))
      (outer41CoeffMul
        (outer41NatCoeffs outer41DeltaCoeffs)
        (outer41NatCoeffs outer41MainQ1Coeffs)) =
      [1] ++ List.replicate 79 0 := by
  decide

set_option maxHeartbeats 3000000 in
private theorem outer41MainDeterminantCoeffs :
    outer41CoeffSub
      (outer41CoeffMul
        (outer41NatCoeffs outer41BetaCoeffs)
        (outer41NatCoeffs outer41GammaCoeffs))
      (outer41CoeffMul
        (outer41NatCoeffs outer41AlphaCoeffs)
        (outer41NatCoeffs outer41DeltaCoeffs)) =
      [-8] ++ List.replicate 76 0 := by
  decide

private theorem outer41MainRow (j : Nat) :
    (outer41MainQ39 j : Int) =
      2 * outer41Alpha j * outer41MainQ0 j -
        outer41Beta j * outer41MainQ1 j := by
  change (outer41HornerNat j outer41MainQ39Coeffs : Int) =
    2 * (outer41HornerNat j outer41AlphaCoeffs : Int) *
      (outer41HornerNat j outer41MainQ0Coeffs : Int) -
    (outer41HornerNat j outer41BetaCoeffs : Int) *
      (outer41HornerNat j outer41MainQ1Coeffs : Int)
  rw [outer41HornerNat_cast, outer41HornerNat_cast,
    outer41HornerNat_cast, outer41HornerNat_cast,
    outer41HornerNat_cast]
  symm
  calc
    _ = outer41HornerInt (j : Int)
        (outer41CoeffSub
          (outer41CoeffScale 2
            (outer41CoeffMul
              (outer41NatCoeffs outer41AlphaCoeffs)
              (outer41NatCoeffs outer41MainQ0Coeffs)))
          (outer41CoeffMul
            (outer41NatCoeffs outer41BetaCoeffs)
            (outer41NatCoeffs outer41MainQ1Coeffs))) := by
          rw [outer41HornerInt_sub, outer41HornerInt_scale,
            outer41HornerInt_mul, outer41HornerInt_mul]
          ring
    _ = outer41HornerInt (j : Int)
        (outer41NatCoeffs outer41MainQ39Coeffs ++
          List.replicate 76 0) := by
            rw [outer41MainRowCoeffs]
    _ = outer41HornerInt (j : Int)
        (outer41NatCoeffs outer41MainQ39Coeffs) := by
          exact outer41HornerInt_append_zeros _ _ _

private theorem outer41MainBezout (j : Nat) :
    (1 : Int) =
      2 * outer41Gamma j * outer41MainQ0 j -
        outer41Delta j * outer41MainQ1 j := by
  change (1 : Int) =
    2 * (outer41HornerNat j outer41GammaCoeffs : Int) *
      (outer41HornerNat j outer41MainQ0Coeffs : Int) -
    (outer41HornerNat j outer41DeltaCoeffs : Int) *
      (outer41HornerNat j outer41MainQ1Coeffs : Int)
  rw [outer41HornerNat_cast, outer41HornerNat_cast,
    outer41HornerNat_cast, outer41HornerNat_cast]
  symm
  calc
    _ = outer41HornerInt (j : Int)
        (outer41CoeffSub
          (outer41CoeffScale 2
            (outer41CoeffMul
              (outer41NatCoeffs outer41GammaCoeffs)
              (outer41NatCoeffs outer41MainQ0Coeffs)))
          (outer41CoeffMul
            (outer41NatCoeffs outer41DeltaCoeffs)
            (outer41NatCoeffs outer41MainQ1Coeffs))) := by
          rw [outer41HornerInt_sub, outer41HornerInt_scale,
            outer41HornerInt_mul, outer41HornerInt_mul]
          ring
    _ = outer41HornerInt (j : Int)
        ([1] ++ List.replicate 79 0) := by
          rw [outer41MainBezoutCoeffs]
    _ = 1 := by simp [outer41HornerInt]

private theorem outer41MainDeterminant (j : Nat) :
    (outer41Beta j : Int) * outer41Gamma j -
        outer41Alpha j * outer41Delta j = -8 := by
  change (outer41HornerNat j outer41BetaCoeffs : Int) *
      (outer41HornerNat j outer41GammaCoeffs : Int) -
    (outer41HornerNat j outer41AlphaCoeffs : Int) *
      (outer41HornerNat j outer41DeltaCoeffs : Int) = -8
  rw [outer41HornerNat_cast, outer41HornerNat_cast,
    outer41HornerNat_cast, outer41HornerNat_cast]
  calc
    _ = outer41HornerInt (j : Int)
        (outer41CoeffSub
          (outer41CoeffMul
            (outer41NatCoeffs outer41BetaCoeffs)
            (outer41NatCoeffs outer41GammaCoeffs))
          (outer41CoeffMul
            (outer41NatCoeffs outer41AlphaCoeffs)
            (outer41NatCoeffs outer41DeltaCoeffs))) := by
          rw [outer41HornerInt_sub, outer41HornerInt_mul,
            outer41HornerInt_mul]
    _ = outer41HornerInt (j : Int)
        ([-8] ++ List.replicate 76 0) := by
          rw [outer41MainDeterminantCoeffs]
    _ = -8 := by simp [outer41HornerInt]

private theorem outer41MainQ0ModEightCoeffs :
    outer41MainQ0Coeffs.map (· % 8) =
      [1] ++ List.replicate 41 0 := by
  decide

private theorem outer41MainQ1ModEightCoeffs :
    outer41MainQ1Coeffs.map (· % 8) =
      [3] ++ List.replicate 40 0 := by
  decide

private theorem outer41MainQ0ModEight (j : Nat) :
    outer41MainQ0 j % 8 = 1 := by
  have h := outer41HornerNat_map_mod j 8 outer41MainQ0Coeffs
  rw [outer41MainQ0ModEightCoeffs] at h
  simpa [outer41MainQ0, outer41HornerNat] using h

private theorem outer41MainQ1ModEight (j : Nat) :
    outer41MainQ1 j % 8 = 3 := by
  have h := outer41HornerNat_map_mod j 8 outer41MainQ1Coeffs
  rw [outer41MainQ1ModEightCoeffs] at h
  simpa [outer41MainQ1, outer41HornerNat] using h

private theorem outer41MainQ0_pos (j : Nat) :
    0 < outer41MainQ0 j := by
  apply outer41HornerNat_pos_of_head
  norm_num [outer41MainQ0Coeffs]

private theorem outer41MainJacobi (j : Nat) :
    jacobiSym (outer41MainQ1 j : Int) (outer41MainQ0 j) = -1 := by
  have htransfer := ss41_globalJacobiTransfer_of_endpoint
    (outer41MainQ0 j) (outer41MainQ1 j)
    (outer41Alpha j) (outer41Beta j)
    (outer41Gamma j) (outer41Delta j) (outer41MainQ39 j)
    (outer41MainQ0ModEight j) (outer41MainQ1ModEight j)
    (outer41GammaModEight j) (outer41MainRow j)
    (outer41MainBezout j) (outer41MainDeterminant j)
  have hcoeff := ss41_coefficientJacobi j
  change jacobiSym (outer41Alpha j : Int) (outer41Gamma j) = 1 at hcoeff
  rw [hcoeff] at htransfer
  exact htransfer

private theorem ss41_jacobi_right_square_ne_neg_one
    {a : Int} {y : Nat} :
    jacobiSym a (y ^ 2) ≠ -1 := by
  intro h
  rw [jacobiSym.pow_right] at h
  rcases jacobiSym.trichotomy a y with hzero | hone | hneg
  · rw [hzero] at h
    norm_num at h
  · rw [hone] at h
    norm_num at h
  · rw [hneg] at h
    norm_num at h

private theorem ss41_main_phase_impossible
    (j y : Nat)
    (hreal : sm2LucasReal (8 * j + 10) 41 = y ^ 2 + 1) :
    False := by
  have hsource := outer41MainReal_eq j
  have hQ0 : outer41MainQ0 j = y ^ 2 := by omega
  have hcharacter := outer41MainJacobi j
  rw [hQ0] at hcharacter
  exact ss41_jacobi_right_square_ne_neg_one hcharacter

private theorem ss41_boundary_two_impossible
    (y : Nat)
    (hreal : sm2LucasReal 2 41 = y ^ 2 + 1) :
    False := by
  have hmod : sm2LucasReal 2 41 % 23 = 21 := by
    norm_num [sm2LucasReal]
  have hvalue :
      (sm2LucasReal 2 41 : ZMod 23) = 21 :=
    (ZMod.natCast_eq_natCast_iff'
      (sm2LucasReal 2 41) 21 23).mpr hmod
  have hrealCast := congrArg (fun n : Nat => (n : ZMod 23)) hreal
  push_cast at hrealCast
  rw [hvalue] at hrealCast
  have hsq : (y : ZMod 23) ^ 2 = 20 := by
    linear_combination -hrealCast
  have hnot : ∀ z : ZMod 23, z ^ 2 ≠ 20 := by
    decide
  exact hnot y hsq

private theorem ss41_mod_eight_two_cases
    {A : Nat} (hA : A % 8 = 2) :
    A = 2 ∨ ∃ j : Nat, A = 8 * j + 10 := by
  have hdecomp := (Nat.mod_add_div A 8).symm
  rw [hA] at hdecomp
  by_cases htwo : A = 2
  · exact Or.inl htwo
  · right
    refine ⟨A / 8 - 1, ?_⟩
    omega

/-- Pure fixed-`41` shifted-square obstruction.  This theorem contains no
packet terminology and covers every natural `A = 2 mod 8`, including the
separate boundary value `A = 2`. -/
theorem ss41_shiftedSquare_impossible
    {A y : Nat}
    (hA : A % 8 = 2)
    (hreal : sm2LucasReal A 41 = y ^ 2 + 1) :
    False := by
  rcases ss41_mod_eight_two_cases hA with htwo | ⟨j, hj⟩
  · subst A
    exact ss41_boundary_two_impossible y hreal
  · subst A
    exact ss41_main_phase_impossible j y hreal

set_option maxHeartbeats 1000000 in
private theorem ss41_outerSelectedSource
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (houter : generator.outerIndex ≠ 0)
    (h41 : 41 ∣ 2 * generator.outerIndex + 1) :
    ∃ m A B : Nat,
      0 < m ∧
        Odd m ∧
        2 * generator.outerIndex + 1 = m * 41 ∧
        generator.point ^ m =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A % 8 = 2 ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 ∧
        sm2LucasReal A 41 = allocation.y ^ 2 + 1 := by
  obtain ⟨m, hm⟩ := h41
  have hmFactor :
      2 * generator.outerIndex + 1 = m * 41 := by
    simpa [Nat.mul_comm] using hm
  have houterPos : 0 < generator.outerIndex :=
    Nat.pos_of_ne_zero houter
  have hmPos : 0 < m := by omega
  have htotalOdd : Odd (2 * generator.outerIndex + 1) :=
    ⟨generator.outerIndex, by omega⟩
  have hmOdd : Odd m := by
    rw [hmFactor] at htotalOdd
    exact (Nat.odd_mul.mp htotalOdd).1
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
  have hsource :
      sm2UpperSourcePoint data.upperKernel data.center
          (data.upperKernel * data.upperSquarePart) =
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 := by
    calc
      sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          generator.point ^ (2 * generator.outerIndex + 1) := by
            simpa [Sm2LowerSquareUpperSourceGenerator.point] using
              generator.source_power
      _ = generator.point ^ (m * 41) := by rw [hmFactor]
      _ = (generator.point ^ m) ^ 41 := by rw [pow_mul]
      _ = (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 := by
            rw [hcoords]
  have hpowerCoordinates :
      (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 =
        (⟨sm2LucasReal A 41,
            B * sm2LucasCoeff A 41⟩ :
          ℤ√(data.upperKernel : Int)) := by
    change sm2UpperNegativeUnit data.upperKernel A B ^ 41 = _
    exact
      sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel) (u := A) (v := B) (n := 41)
        hnegative
  have hrealInt := congrArg Zsqrtd.re hsource
  rw [hpowerCoordinates] at hrealInt
  change (data.center : Int) = (sm2LucasReal A 41 : Int) at hrealInt
  have hrealCenter : sm2LucasReal A 41 = data.center := by
    exact_mod_cast hrealInt.symm
  have hreal :
      sm2LucasReal A 41 = allocation.y ^ 2 + 1 :=
    hrealCenter.trans allocation.center_eq
  exact
    ⟨m, A, B, hmPos, hmOdd, hmFactor, hcoords,
      hAEight, hsource, hreal⟩

set_option maxHeartbeats 1000000 in
private theorem ss41_rankSelectedSource
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (hzero : generator.outerIndex = 0)
    (h41 :
      41 ∣ pellRank data.upperKernel allocation.upper_pellKernel) :
    ∃ n A B : Nat,
      0 < n ∧
        Odd n ∧
        pellRank data.upperKernel allocation.upper_pellKernel = n * 41 ∧
        sm2UpperNegativeUnit data.upperKernel
            generator.upperOrbit.rootX generator.upperOrbit.rootY ^ n =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ∧
        A % 8 = 2 ∧
        sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 ∧
        sm2LucasReal A 41 = allocation.y ^ 2 + 1 := by
  obtain ⟨n, hn⟩ := h41
  have hRankFactor :
      pellRank data.upperKernel allocation.upper_pellKernel = n * 41 := by
    simpa [Nat.mul_comm] using hn
  have hRankPos :
      0 < pellRank data.upperKernel allocation.upper_pellKernel :=
    pellRank_pos data.upperKernel allocation.upper_pellKernel
  have hnPos : 0 < n := by
    rw [hRankFactor] at hRankPos
    exact Nat.pos_of_mul_pos_right hRankPos
  have hRankOdd :
      Odd (pellRank data.upperKernel allocation.upper_pellKernel) := by
    rw [Nat.odd_iff]
    have hRankEight := generator.rank_mod_eight_eq_one
    have hmod :=
      Nat.mod_mod_of_dvd
        (pellRank data.upperKernel allocation.upper_pellKernel)
        (by decide : 2 ∣ 8)
    rw [hRankEight] at hmod
    exact hmod.symm
  have hnOdd : Odd n := by
    rw [hRankFactor] at hRankOdd
    exact (Nat.odd_mul.mp hRankOdd).1
  have hnEight : n % 8 = 1 := by
    have hmod := congrArg (fun k : Nat => k % 8) hRankFactor
    rw [generator.rank_mod_eight_eq_one, Nat.mul_mod] at hmod
    norm_num at hmod
    omega
  let A := sm2LucasReal generator.upperOrbit.rootX n
  let B := generator.upperOrbit.rootY *
    sm2LucasCoeff generator.upperOrbit.rootX n
  have hAEight : A % 8 = 2 := by
    have hnFour : n % 4 = 1 := by
      have hmod : n % 8 % 4 = n % 4 :=
        Nat.mod_mod_of_dvd n (by decide : 4 ∣ 8)
      rw [hnEight] at hmod
      exact hmod.symm
    simpa [A, sm2LucasRealResidue, hnFour] using
      (sm2LucasReal_mod_eight
        (n := n) generator.root_real_mod_eight)
  have hcoords :
      sm2UpperNegativeUnit data.upperKernel
          generator.upperOrbit.rootX generator.upperOrbit.rootY ^ n =
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) := by
    simpa [A, B] using
      (sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel)
        (u := generator.upperOrbit.rootX)
        (v := generator.upperOrbit.rootY)
        (n := n)
        generator.upperOrbit.root_equation)
  have hnegative :
      A ^ 2 + 1 = data.upperKernel * B ^ 2 := by
    simpa [A, B] using
      (sm2LucasReal_odd_negative_equation
        (K := data.upperKernel)
        (u := generator.upperOrbit.rootX)
        (v := generator.upperOrbit.rootY)
        (n := n)
        generator.upperOrbit.root_equation hnOdd)
  have hsource :
      sm2UpperSourcePoint data.upperKernel data.center
          (data.upperKernel * data.upperSquarePart) =
        (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 := by
    calc
      sm2UpperSourcePoint data.upperKernel data.center
            (data.upperKernel * data.upperSquarePart) =
          generator.point := by
            simpa [Sm2LowerSquareUpperSourceGenerator.point, hzero] using
              generator.source_power
      _ = sm2UpperNegativeUnit data.upperKernel
          generator.upperOrbit.rootX generator.upperOrbit.rootY ^
            pellRank data.upperKernel allocation.upper_pellKernel := by
            simpa [Sm2LowerSquareUpperSourceGenerator.point] using
              generator.generator_power.symm
      _ = sm2UpperNegativeUnit data.upperKernel
          generator.upperOrbit.rootX generator.upperOrbit.rootY ^
            (n * 41) := by rw [hRankFactor]
      _ = (sm2UpperNegativeUnit data.upperKernel
          generator.upperOrbit.rootX generator.upperOrbit.rootY ^ n) ^ 41 := by
            rw [pow_mul]
      _ = (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 := by
            rw [hcoords]
  have hpowerCoordinates :
      (⟨A, B⟩ : ℤ√(data.upperKernel : Int)) ^ 41 =
        (⟨sm2LucasReal A 41,
            B * sm2LucasCoeff A 41⟩ :
          ℤ√(data.upperKernel : Int)) := by
    change sm2UpperNegativeUnit data.upperKernel A B ^ 41 = _
    exact
      sm2UpperNegativeUnit_pow_coordinates
        (K := data.upperKernel) (u := A) (v := B) (n := 41)
        hnegative
  have hrealInt := congrArg Zsqrtd.re hsource
  rw [hpowerCoordinates] at hrealInt
  change (data.center : Int) = (sm2LucasReal A 41 : Int) at hrealInt
  have hrealCenter : sm2LucasReal A 41 = data.center := by
    exact_mod_cast hrealInt.symm
  have hreal :
      sm2LucasReal A 41 = allocation.y ^ 2 + 1 :=
    hrealCenter.trans allocation.center_eq
  exact
    ⟨n, A, B, hnPos, hnOdd, hRankFactor, hcoords,
      hAEight, hsource, hreal⟩

/-- A complete outer-large packet whose exact outer exponent contains the
selected prime `41` is impossible.  The packet's unrelated existential
prime witness is not used. -/
theorem no_outerLarge_selected_fortyOne
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (packet : generator.OuterLargePacket)
    (h41 : 41 ∣ 2 * generator.outerIndex + 1) :
    False := by
  obtain ⟨m, A, B, hmPos, hmOdd, hmFactor, hcoords,
      hAEight, hsource, hreal⟩ :=
    ss41_outerSelectedSource generator packet.1.1 h41
  exact ss41_shiftedSquare_impossible hAEight hreal

/-- A complete rank-defect packet whose exact Pell rank contains the
selected prime `41` is impossible.  The packet's unrelated existential
prime witness is not used. -/
theorem no_rankDefect_selected_fortyOne
    {data : PairPellCounterexampleData}
    {allocation : Sm2LowerSquareAllocation data}
    (generator : Sm2LowerSquareUpperSourceGenerator allocation)
    (packet : generator.RankDefectPacket)
    (h41 :
      41 ∣ pellRank data.upperKernel allocation.upper_pellKernel) :
    False := by
  obtain ⟨n, A, B, hnPos, hnOdd, hRankFactor, hcoords,
      hAEight, hsource, hreal⟩ :=
    ss41_rankSelectedSource generator packet.1.1 h41
  exact ss41_shiftedSquare_impossible hAEight hreal

#print axioms Ss41LocalLinkCertificate
#print axioms Ss41LocalCertificate
#print axioms ss41_localCertificate
#print axioms ss41_factor13Multiplier
#print axioms ss41_factor13Multiplier_sq
#print axioms ss41_factor13_block_25_21
#print axioms ss41_direct_endpoint_3_1
#print axioms ss41_directedTelescope
#print axioms ss41_coefficientJacobi
#print axioms ss41_shiftedSquare_impossible
#print axioms no_outerLarge_selected_fortyOne
#print axioms no_rankDefect_selected_fortyOne

end Erdos364
