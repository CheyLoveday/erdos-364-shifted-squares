import Erdos364.SquareMiddle.Sm2LowerSquareGeneratorRank

namespace Erdos364

open scoped jacobiSym

/-!
# The outer-`17` shifted-square obstruction

This module transfers the certified arithmetic obstruction for the complete
`OuterSeventeenPacket` into Lean.  The proof is problem-specific: it uses the
signed pseudo-remainder chain for the two explicit integer polynomials and
does not introduce a generic polynomial-Jacobi framework.
-/

private def outer17R0 (A : Int) : Int :=
  65536 * A ^ 17 + 278528 * A ^ 15 + 487424 * A ^ 13 +
    452608 * A ^ 11 + 239360 * A ^ 9 + 71808 * A ^ 7 +
    11424 * A ^ 5 + 816 * A ^ 3 + 17 * A - 1

private def outer17R1 (A : Int) : Int :=
  16384 * A ^ 14 + 49152 * A ^ 12 + 54272 * A ^ 10 +
    26112 * A ^ 8 + 4480 * A ^ 6 - 32 * A ^ 5 -
    208 * A ^ 4 - 32 * A ^ 3 - 80 * A ^ 2 - 4 * A - 3

private def outer17R2 (A : Int) : Int :=
  24576 * A ^ 13 + 76800 * A ^ 11 + 90880 * A ^ 9 +
    128 * A ^ 8 + 50240 * A ^ 7 + 288 * A ^ 6 +
    12784 * A ^ 5 + 176 * A ^ 4 + 1228 * A ^ 3 +
    20 * A ^ 2 + 32 * A - 1

private def outer17R3 (A : Int) : Int :=
  6144 * A ^ 12 + 18944 * A ^ 10 + 256 * A ^ 9 +
    22144 * A ^ 8 + 576 * A ^ 7 + 12128 * A ^ 6 +
    448 * A ^ 5 + 3080 * A ^ 4 + 136 * A ^ 3 +
    304 * A ^ 2 + 10 * A + 9

private def outer17R4 (A : Int) : Int :=
  1024 * A ^ 11 - 1024 * A ^ 10 + 2304 * A ^ 9 -
    2176 * A ^ 8 + 1728 * A ^ 7 - 1504 * A ^ 6 +
    464 * A ^ 5 - 368 * A ^ 4 + 12 * A ^ 3 -
    20 * A ^ 2 - 4 * A - 1

private def outer17R5 (A : Int) : Int :=
  11264 * A ^ 10 - 512 * A ^ 9 + 24832 * A ^ 8 -
    768 * A ^ 7 + 18368 * A ^ 6 - 128 * A ^ 5 +
    5216 * A ^ 4 + 184 * A ^ 3 + 448 * A ^ 2 +
    40 * A + 15

private def outer17R6 (A : Int) : Int :=
  512 * A ^ 9 + 11776 * A ^ 8 - 2048 * A ^ 7 +
    24576 * A ^ 6 - 5152 * A ^ 5 + 16432 * A ^ 4 -
    3088 * A ^ 3 + 3688 * A ^ 2 - 458 * A + 73

private def outer17R7 (A : Int) : Int :=
  8320 * A ^ 8 - 2176 * A ^ 7 + 17344 * A ^ 6 -
    4096 * A ^ 5 + 11576 * A ^ 4 - 2268 * A ^ 3 +
    2590 * A ^ 2 - 322 * A + 51

private def outer17R8 (A : Int) : Int :=
  1792 * A ^ 7 - 2048 * A ^ 6 + 4352 * A ^ 5 -
    3232 * A ^ 4 + 3336 * A ^ 3 - 1200 * A ^ 2 +
    854 * A + 23

private def outer17R9 (A : Int) : Int :=
  128 * A ^ 6 - 160 * A ^ 5 + 216 * A ^ 4 -
    240 * A ^ 3 + 82 * A ^ 2 - 91 * A - 1

private def outer17R10 (A : Int) : Int :=
  64 * A ^ 5 - 8 * A ^ 4 + 104 * A ^ 3 -
    2 * A ^ 2 + 41 * A + 1

private def outer17R11 (A : Int) : Int :=
  40 * A ^ 4 + 8 * A ^ 3 + 18 * A ^ 2 + 3 * A - 5

private def outer17R12 (A : Int) : Int :=
  248 * A ^ 3 + 8 * A ^ 2 + 158 * A - 5

private def outer17R13 (A : Int) : Int :=
  296 * A ^ 2 + 18 * A + 187

private def outer17R14 (A : Int) : Int :=
  10 * A - 3

private def outer17A (k : Nat) : Int :=
  8 * (k : Int) + 2

private def outer17P (r : Int → Int) (k : Nat) : Nat :=
  (r (outer17A k)).toNat

private abbrev outer17P0 := outer17P outer17R0
private abbrev outer17P1 := outer17P outer17R1
private abbrev outer17P2 := outer17P outer17R2
private abbrev outer17P3 := outer17P outer17R3
private abbrev outer17P4 := outer17P outer17R4
private abbrev outer17P5 := outer17P outer17R5
private abbrev outer17P6 := outer17P outer17R6
private abbrev outer17P7 := outer17P outer17R7
private abbrev outer17P8 := outer17P outer17R8
private abbrev outer17P9 := outer17P outer17R9
private abbrev outer17P10 := outer17P outer17R10
private abbrev outer17P11 := outer17P outer17R11
private abbrev outer17P12 := outer17P outer17R12
private abbrev outer17P13 := outer17P outer17R13
private abbrev outer17P14 := outer17P outer17R14

private theorem outer17R_pos (k : Nat) :
    0 < outer17R0 (outer17A k) ∧
      0 < outer17R1 (outer17A k) ∧
      0 < outer17R2 (outer17A k) ∧
      0 < outer17R3 (outer17A k) ∧
      0 < outer17R4 (outer17A k) ∧
      0 < outer17R5 (outer17A k) ∧
      0 < outer17R6 (outer17A k) ∧
      0 < outer17R7 (outer17A k) ∧
      0 < outer17R8 (outer17A k) ∧
      0 < outer17R9 (outer17A k) ∧
      0 < outer17R10 (outer17A k) ∧
      0 < outer17R11 (outer17A k) ∧
      0 < outer17R12 (outer17A k) ∧
      0 < outer17R13 (outer17A k) ∧
      0 < outer17R14 (outer17A k) := by
  simp only [outer17A, outer17R0, outer17R1, outer17R2,
    outer17R3, outer17R4, outer17R5, outer17R6, outer17R7,
    outer17R8, outer17R9, outer17R10, outer17R11, outer17R12,
    outer17R13, outer17R14]
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor
  · ring_nf
    positivity
  constructor <;>
    ring_nf <;>
    positivity

private theorem outer17P_casts (k : Nat) :
    (outer17P0 k : Int) = outer17R0 (outer17A k) ∧
      (outer17P1 k : Int) = outer17R1 (outer17A k) ∧
      (outer17P2 k : Int) = outer17R2 (outer17A k) ∧
      (outer17P3 k : Int) = outer17R3 (outer17A k) ∧
      (outer17P4 k : Int) = outer17R4 (outer17A k) ∧
      (outer17P5 k : Int) = outer17R5 (outer17A k) ∧
      (outer17P6 k : Int) = outer17R6 (outer17A k) ∧
      (outer17P7 k : Int) = outer17R7 (outer17A k) ∧
      (outer17P8 k : Int) = outer17R8 (outer17A k) ∧
      (outer17P9 k : Int) = outer17R9 (outer17A k) ∧
      (outer17P10 k : Int) = outer17R10 (outer17A k) ∧
      (outer17P11 k : Int) = outer17R11 (outer17A k) ∧
      (outer17P12 k : Int) = outer17R12 (outer17A k) ∧
      (outer17P13 k : Int) = outer17R13 (outer17A k) ∧
      (outer17P14 k : Int) = outer17R14 (outer17A k) := by
  rcases outer17R_pos k with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12, h13, h14⟩
  simp only [outer17P0, outer17P1, outer17P2, outer17P3,
    outer17P4, outer17P5, outer17P6, outer17P7, outer17P8,
    outer17P9, outer17P10, outer17P11, outer17P12,
    outer17P13, outer17P14, outer17P,
    Int.toNat_of_nonneg h0.le, Int.toNat_of_nonneg h1.le,
    Int.toNat_of_nonneg h2.le, Int.toNat_of_nonneg h3.le,
    Int.toNat_of_nonneg h4.le, Int.toNat_of_nonneg h5.le,
    Int.toNat_of_nonneg h6.le, Int.toNat_of_nonneg h7.le,
    Int.toNat_of_nonneg h8.le, Int.toNat_of_nonneg h9.le,
    Int.toNat_of_nonneg h10.le, Int.toNat_of_nonneg h11.le,
    Int.toNat_of_nonneg h12.le, Int.toNat_of_nonneg h13.le,
    Int.toNat_of_nonneg h14.le]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 800000 in
private theorem outer17P_mod_eight (k : Nat) :
    outer17P0 k % 8 = 1 ∧
      outer17P1 k % 8 = 5 ∧
      outer17P2 k % 8 = 7 ∧
      outer17P3 k % 8 = 5 ∧
      outer17P4 k % 8 = 7 ∧
      outer17P5 k % 8 = 7 ∧
      outer17P6 k % 8 = 5 ∧
      outer17P7 k % 8 = 7 ∧
      outer17P8 k % 8 = 3 ∧
      outer17P9 k % 8 = 1 ∧
      outer17P10 k % 8 = 3 ∧
      outer17P11 k % 8 = 1 ∧
      outer17P12 k % 8 = 7 ∧
      outer17P13 k % 8 = 7 ∧
      outer17P14 k % 8 = 1 := by
  rcases outer17P_casts k with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12, h13, h14⟩
  have hA : outer17A k ≡ 2 [ZMOD 8] := by
    simp [outer17A, Int.ModEq]
  have hm0 : outer17R0 (outer17A k) ≡ outer17R0 2 [ZMOD 8] := by
    unfold outer17R0
    gcongr
  have hm1 : outer17R1 (outer17A k) ≡ outer17R1 2 [ZMOD 8] := by
    unfold outer17R1
    gcongr
  have hm2 : outer17R2 (outer17A k) ≡ outer17R2 2 [ZMOD 8] := by
    unfold outer17R2
    gcongr
  have hm3 : outer17R3 (outer17A k) ≡ outer17R3 2 [ZMOD 8] := by
    unfold outer17R3
    gcongr
  have hm4 : outer17R4 (outer17A k) ≡ outer17R4 2 [ZMOD 8] := by
    unfold outer17R4
    gcongr
  have hm5 : outer17R5 (outer17A k) ≡ outer17R5 2 [ZMOD 8] := by
    unfold outer17R5
    gcongr
  have hm6 : outer17R6 (outer17A k) ≡ outer17R6 2 [ZMOD 8] := by
    unfold outer17R6
    gcongr
  have hm7 : outer17R7 (outer17A k) ≡ outer17R7 2 [ZMOD 8] := by
    unfold outer17R7
    gcongr
  have hm8 : outer17R8 (outer17A k) ≡ outer17R8 2 [ZMOD 8] := by
    unfold outer17R8
    gcongr
  have hm9 : outer17R9 (outer17A k) ≡ outer17R9 2 [ZMOD 8] := by
    unfold outer17R9
    gcongr
  have hm10 : outer17R10 (outer17A k) ≡ outer17R10 2 [ZMOD 8] := by
    unfold outer17R10
    gcongr
  have hm11 : outer17R11 (outer17A k) ≡ outer17R11 2 [ZMOD 8] := by
    unfold outer17R11
    gcongr
  have hm12 : outer17R12 (outer17A k) ≡ outer17R12 2 [ZMOD 8] := by
    unfold outer17R12
    gcongr
  have hm13 : outer17R13 (outer17A k) ≡ outer17R13 2 [ZMOD 8] := by
    unfold outer17R13
    gcongr
  have hm14 : outer17R14 (outer17A k) ≡ outer17R14 2 [ZMOD 8] := by
    unfold outer17R14
    gcongr
  rw [Int.ModEq] at hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10 hm11 hm12 hm13 hm14
  have hr0 : outer17R0 2 % 8 = 1 := by norm_num [outer17R0]
  have hr1 : outer17R1 2 % 8 = 5 := by norm_num [outer17R1]
  have hr2 : outer17R2 2 % 8 = 7 := by norm_num [outer17R2]
  have hr3 : outer17R3 2 % 8 = 5 := by norm_num [outer17R3]
  have hr4 : outer17R4 2 % 8 = 7 := by norm_num [outer17R4]
  have hr5 : outer17R5 2 % 8 = 7 := by norm_num [outer17R5]
  have hr6 : outer17R6 2 % 8 = 5 := by norm_num [outer17R6]
  have hr7 : outer17R7 2 % 8 = 7 := by norm_num [outer17R7]
  have hr8 : outer17R8 2 % 8 = 3 := by norm_num [outer17R8]
  have hr9 : outer17R9 2 % 8 = 1 := by norm_num [outer17R9]
  have hr10 : outer17R10 2 % 8 = 3 := by norm_num [outer17R10]
  have hr11 : outer17R11 2 % 8 = 1 := by norm_num [outer17R11]
  have hr12 : outer17R12 2 % 8 = 7 := by norm_num [outer17R12]
  have hr13 : outer17R13 2 % 8 = 7 := by norm_num [outer17R13]
  have hr14 : outer17R14 2 % 8 = 1 := by norm_num [outer17R14]
  replace hm0 := hm0.trans hr0
  replace hm1 := hm1.trans hr1
  replace hm2 := hm2.trans hr2
  replace hm3 := hm3.trans hr3
  replace hm4 := hm4.trans hr4
  replace hm5 := hm5.trans hr5
  replace hm6 := hm6.trans hr6
  replace hm7 := hm7.trans hr7
  replace hm8 := hm8.trans hr8
  replace hm9 := hm9.trans hr9
  replace hm10 := hm10.trans hr10
  replace hm11 := hm11.trans hr11
  replace hm12 := hm12.trans hr12
  replace hm13 := hm13.trans hr13
  replace hm14 := hm14.trans hr14
  rw [← h0] at hm0
  rw [← h1] at hm1
  rw [← h2] at hm2
  rw [← h3] at hm3
  rw [← h4] at hm4
  rw [← h5] at hm5
  rw [← h6] at hm6
  rw [← h7] at hm7
  rw [← h8] at hm8
  rw [← h9] at hm9
  rw [← h10] at hm10
  rw [← h11] at hm11
  rw [← h12] at hm12
  rw [← h13] at hm13
  rw [← h14] at hm14
  constructor
  · exact_mod_cast hm0
  constructor
  · exact_mod_cast hm1
  constructor
  · exact_mod_cast hm2
  constructor
  · exact_mod_cast hm3
  constructor
  · exact_mod_cast hm4
  constructor
  · exact_mod_cast hm5
  constructor
  · exact_mod_cast hm6
  constructor
  · exact_mod_cast hm7
  constructor
  · exact_mod_cast hm8
  constructor
  · exact_mod_cast hm9
  constructor
  · exact_mod_cast hm10
  constructor
  · exact_mod_cast hm11
  constructor
  · exact_mod_cast hm12
  constructor
  · exact_mod_cast hm13
  · exact_mod_cast hm14

private theorem outer17_pseudo_remainders (A : Int) :
    outer17R0 A =
        (4 * A ^ 3 + 5 * A) * outer17R1 A + outer17R2 A ∧
      3 * outer17R1 A =
        2 * A * outer17R2 A - outer17R3 A ∧
      outer17R2 A = 4 * A * outer17R3 A + outer17R4 A ∧
      outer17R3 A = (6 * A + 6) * outer17R4 A + outer17R5 A ∧
      242 * outer17R4 A =
        (22 * A - 21) * outer17R5 A + outer17R6 A ∧
      outer17R5 A =
        (22 * A - 507) * outer17R6 A + 726 * outer17R7 A ∧
      4225 * outer17R6 A =
        (260 * A + 6048) * outer17R7 A - outer17R8 A ∧
      98 * outer17R7 A =
        (455 * A + 401) * outer17R8 A + 4225 * outer17R9 A ∧
      2 * outer17R8 A =
        (28 * A + 3) * outer17R9 A + 49 * outer17R10 A ∧
      4 * outer17R9 A =
        (8 * A - 9) * outer17R10 A - outer17R11 A ∧
      25 * outer17R10 A =
        (40 * A - 13) * outer17R11 A + 8 * outer17R12 A ∧
      961 * outer17R11 A =
        (155 * A + 26) * outer17R12 A - 25 * outer17R13 A ∧
      5476 * outer17R12 A =
        (4588 * A - 131) * outer17R13 A + 961 * outer17R14 A ∧
      25 * outer17R13 A =
        (740 * A + 267) * outer17R14 A + 5476 := by
  simp only [outer17R0, outer17R1, outer17R2, outer17R3,
    outer17R4, outer17R5, outer17R6, outer17R7,
    outer17R8, outer17R9, outer17R10, outer17R11,
    outer17R12, outer17R13, outer17R14]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private def outer17NatA (k : Nat) : Nat :=
  8 * k + 2

private def outer17L (k : Nat) : Nat :=
  16 * k + 5

private def outer17H (k : Nat) : Nat :=
  3200 * k ^ 2 + 1600 * k + 193

private def outer17M (k : Nat) : Nat :=
  2060 * k + 409

private def outer17S (k : Nat) : Nat :=
  outer17L k * outer17H k

private def outer17U (k : Nat) : Nat :=
  let A := outer17NatA k
  160 * A ^ 4 + 28 * A ^ 3 + 150 * A ^ 2 + 62 * A + 3

private def outer17E (k : Nat) : Nat :=
  163840 * k ^ 3 + 116736 * k ^ 2 + 29184 * k + 2488

private def outer17E2 (k : Nat) : Nat :=
  let A := outer17NatA k
  100 * A ^ 2 + 20 * A + 59

private def outer17E3 (k : Nat) : Nat :=
  16480 * k + 4968

private theorem outer17_bottom_identities (k : Nat) :
    outer17S k * outer17P10 k =
        outer17U k * outer17P11 k + 8 ∧
      outer17E k * outer17L k =
        16 * outer17P11 k + 8 ∧
      125 * outer17P11 k =
        outer17E2 k * outer17H k + 2 * outer17M k ∧
      103 ^ 2 * outer17H k =
        outer17E3 k * outer17M k + 125 ^ 2 := by
  rcases outer17P_casts k with
    ⟨_, _, _, _, _, _, _, _, _, _, h10, h11, _, _, _⟩
  constructor
  · have hi :
        (outer17S k : Int) * (outer17P10 k : Int) =
          (outer17U k : Int) * (outer17P11 k : Int) + 8 := by
      rw [h10, h11]
      simp only [outer17S, outer17L, outer17H, outer17U,
        outer17NatA, outer17A, outer17R10, outer17R11]
      push_cast
      ring
    exact_mod_cast hi
  constructor
  · have hi :
        (outer17E k : Int) * (outer17L k : Int) =
          16 * (outer17P11 k : Int) + 8 := by
      rw [h11]
      simp only [outer17E, outer17L, outer17A, outer17R11]
      push_cast
      ring
    exact_mod_cast hi
  constructor
  · have hi :
        125 * (outer17P11 k : Int) =
          (outer17E2 k : Int) * (outer17H k : Int) +
            2 * (outer17M k : Int) := by
      rw [h11]
      simp only [outer17E2, outer17H, outer17M, outer17NatA,
        outer17A, outer17R11]
      push_cast
      ring
    exact_mod_cast hi
  · simp only [outer17H, outer17E3, outer17M]
    ring

private theorem outer17_bottom_moduli (k : Nat) :
    outer17L k % 8 = 5 ∧
      outer17H k % 8 = 1 ∧
      outer17H k % 5 = 3 ∧
      outer17M k % 4 = 1 ∧
      outer17M k % 5 = 4 ∧
      outer17M k % 103 = 100 := by
  norm_num [outer17L, outer17H, outer17M, Nat.add_mod,
    Nat.mul_mod]

private theorem outer17P10_coprime_P11 (k : Nat) :
    Nat.Coprime (outer17P10 k) (outer17P11 k) := by
  rcases outer17_bottom_identities k with ⟨hid, _, _, _⟩
  rcases outer17P_mod_eight k with
    ⟨_, _, _, _, _, _, _, _, _, _, _, h11, _, _, _⟩
  apply Nat.coprime_of_dvd
  intro p hp hp10 hp11
  have hpLeft : p ∣ outer17S k * outer17P10 k :=
    dvd_mul_of_dvd_right hp10 _
  have hpFirst : p ∣ outer17U k * outer17P11 k :=
    dvd_mul_of_dvd_right hp11 _
  have hpEight : p ∣ 8 := by
    apply (Nat.dvd_add_iff_left hpFirst).mpr
    rw [add_comm, ← hid]
    exact hpLeft
  have hpPow : p ∣ 2 ^ 3 := by
    norm_num
    exact hpEight
  have hpTwo : p ∣ 2 :=
    hp.dvd_of_dvd_pow hpPow
  have hpEq : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpTwo
  subst p
  rcases hp11 with ⟨q, hq⟩
  omega

set_option maxHeartbeats 800000 in
private theorem outer17_bottom_jacobi (k : Nat) :
    jacobiSym (outer17P11 k : Int) (outer17P10 k) = 1 := by
  rcases outer17_bottom_identities k with
    ⟨hSP, hEL, hEH, hEM⟩
  rcases outer17_bottom_moduli k with
    ⟨hL8, hH8, hH5, hM4, hM5, hM103⟩
  rcases outer17P_mod_eight k with
    ⟨_, _, _, _, _, _, _, _, _, _, hP10, hP11, _, _, _⟩
  have hL4 : outer17L k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17L k) (by decide : 4 ∣ 8)
    rw [hL8] at hm
    omega
  have hH4 : outer17H k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17H k) (by decide : 4 ∣ 8)
    rw [hH8] at hm
    omega
  have hP104 : outer17P10 k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P10 k) (by decide : 4 ∣ 8)
    rw [hP10] at hm
    omega
  have hP114 : outer17P11 k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P11 k) (by decide : 4 ∣ 8)
    rw [hP11] at hm
    omega
  have hLOdd : Odd (outer17L k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hL4)
  have hHOdd : Odd (outer17H k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hH4)
  have hMOdd : Odd (outer17M k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hM4)
  have hP10Odd : Odd (outer17P10 k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hP104)
  have hP11Odd : Odd (outer17P11 k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hP114)
  have h5M : Nat.Coprime 5 (outer17M k) := by
    rw [Nat.Coprime, Nat.gcd_rec, hM5]
    norm_num
  have h103M : Nat.Coprime 103 (outer17M k) := by
    rw [Nat.Coprime, Nat.gcd_rec, hM103]
    norm_num
  have h125M : Nat.Coprime 125 (outer17M k) := by
    simpa using h5M.pow_left 3
  have h103MInt :
      Int.gcd (103 : Int) (outer17M k) = 1 := by
    change Int.gcd ((103 : Nat) : Int)
      ((outer17M k : Nat) : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact h103M.gcd_eq_one
  have h125MInt :
      Int.gcd (125 : Int) (outer17M k) = 1 := by
    change Int.gcd ((125 : Nat) : Int)
      ((outer17M k : Nat) : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact h125M.gcd_eq_one
  have hJL :
      jacobiSym (outer17L k : Int) (outer17P11 k) = -1 := by
    have hELInt :
        (outer17E k : Int) * outer17L k =
          16 * (outer17P11 k : Int) + 8 := by
      exact_mod_cast hEL
    have hmod :
        (16 * (outer17P11 k : Int)) ≡ -8
          [ZMOD (outer17L k : Int)] := by
      rw [Int.modEq_iff_dvd]
      use -(outer17E k : Int)
      calc
        (-8 : Int) - 16 * outer17P11 k =
            -((outer17E k : Int) * outer17L k) := by
              rw [hELInt]
              ring
        _ = (outer17L k : Int) * -(outer17E k : Int) := by
          ring
    have hJ16 :
        jacobiSym (16 : Int) (outer17L k) = 1 := by
      calc
        jacobiSym (16 : Int) (outer17L k) =
            jacobiSym ((4 : Int) * 4) (outer17L k) := by
              norm_num
        _ = 1 := by
          rw [jacobiSym.mul_left, jacobiSym.at_four hLOdd]
          norm_num
    have hJnegEight :
        jacobiSym (-8 : Int) (outer17L k) = -1 := by
      calc
        jacobiSym (-8 : Int) (outer17L k) =
            jacobiSym ((-2 : Int) * 4) (outer17L k) := by
              norm_num
        _ = -1 := by
          rw [jacobiSym.mul_left, jacobiSym.at_neg_two hLOdd,
            jacobiSym.at_four hLOdd, mul_one,
            ZMod.χ₈'_nat_eq_if_mod_eight]
          simp [Nat.odd_iff.mp hLOdd, hL8]
    calc
      jacobiSym (outer17L k : Int) (outer17P11 k) =
          jacobiSym (outer17P11 k : Int) (outer17L k) :=
        jacobiSym.quadratic_reciprocity_one_mod_four
          hL4 hP11Odd
      _ = -1 := by
        have hs :=
          jacobiSym.mod_left' hmod
        rw [jacobiSym.mul_left, hJ16, one_mul, hJnegEight] at hs
        exact hs
  have hJHM :
      jacobiSym (outer17H k : Int) (outer17M k) = 1 := by
    have hEMInt :
        (103 : Int) ^ 2 * outer17H k =
          (outer17E3 k : Int) * outer17M k + 125 ^ 2 := by
      exact_mod_cast hEM
    have hmod :
        ((103 : Int) ^ 2 * outer17H k) ≡ (125 : Int) ^ 2
          [ZMOD (outer17M k : Int)] := by
      rw [Int.modEq_iff_dvd]
      use -(outer17E3 k : Int)
      linear_combination -hEMInt
    have hs := jacobiSym.mod_left' hmod
    rw [jacobiSym.mul_left, jacobiSym.sq_one' h103MInt,
      one_mul, jacobiSym.sq_one' h125MInt] at hs
    exact hs
  have hJMH :
      jacobiSym (outer17M k : Int) (outer17H k) = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
      hM4 hHOdd]
    exact hJHM
  have hJFiveH :
      jacobiSym (5 : Int) (outer17H k) = -1 := by
    have hmod :
        ((outer17H k : Int) % 5) = ((3 : Int) % 5) := by
      exact_mod_cast hH5
    calc
      jacobiSym (5 : Int) (outer17H k) =
          jacobiSym (outer17H k : Int) 5 :=
        jacobiSym.quadratic_reciprocity_one_mod_four
          (by decide) hHOdd
      _ = jacobiSym (3 : Int) 5 :=
        jacobiSym.mod_left' hmod
      _ = -1 := by norm_num
  have hJ125H :
      jacobiSym (125 : Int) (outer17H k) = -1 := by
    calc
      jacobiSym (125 : Int) (outer17H k) =
          jacobiSym ((5 : Int) * 5 * 5) (outer17H k) := by
            norm_num
      _ = -1 := by
        rw [jacobiSym.mul_left, jacobiSym.mul_left, hJFiveH]
        norm_num
  have hJTwoH :
      jacobiSym (2 : Int) (outer17H k) = 1 := by
    rw [jacobiSym.at_two hHOdd, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [Nat.odd_iff.mp hHOdd, hH8]
  have hJH :
      jacobiSym (outer17H k : Int) (outer17P11 k) = -1 := by
    have hEHInt :
        125 * (outer17P11 k : Int) =
          (outer17E2 k : Int) * outer17H k +
            2 * (outer17M k : Int) := by
      exact_mod_cast hEH
    have hmod :
        (125 * (outer17P11 k : Int)) ≡
          2 * (outer17M k : Int)
          [ZMOD (outer17H k : Int)] := by
      rw [Int.modEq_iff_dvd]
      use -(outer17E2 k : Int)
      linear_combination -hEHInt
    have hs := jacobiSym.mod_left' hmod
    rw [jacobiSym.mul_left, hJ125H,
      jacobiSym.mul_left, hJTwoH, hJMH] at hs
    norm_num at hs
    rw [jacobiSym.quadratic_reciprocity_one_mod_four
      hH4 hP11Odd]
    linarith
  have hJS :
      jacobiSym (outer17S k : Int) (outer17P11 k) = 1 := by
    change
      jacobiSym
        (((outer17L k * outer17H k : Nat) : Int))
        (outer17P11 k) = 1
    rw [Nat.cast_mul, jacobiSym.mul_left, hJL, hJH]
    norm_num
  have hJEight :
      jacobiSym (8 : Int) (outer17P11 k) = 1 := by
    calc
      jacobiSym (8 : Int) (outer17P11 k) =
          jacobiSym ((2 : Int) * 4) (outer17P11 k) := by
            norm_num
      _ = 1 := by
        rw [jacobiSym.mul_left, jacobiSym.at_two hP11Odd,
          jacobiSym.at_four hP11Odd,
          ZMod.χ₈_nat_eq_if_mod_eight]
        simp [Nat.odd_iff.mp hP11Odd, hP11]
  have hJP10 :
      jacobiSym (outer17P10 k : Int) (outer17P11 k) = 1 := by
    have hSPInt :
        (outer17S k : Int) * outer17P10 k =
          (outer17U k : Int) * outer17P11 k + 8 := by
      exact_mod_cast hSP
    have hmod :
        ((outer17S k : Int) * outer17P10 k) ≡ 8
          [ZMOD (outer17P11 k : Int)] := by
      rw [Int.modEq_iff_dvd]
      use -(outer17U k : Int)
      linear_combination -hSPInt
    have hs := jacobiSym.mod_left' hmod
    rw [jacobiSym.mul_left, hJS, one_mul, hJEight] at hs
    exact hs
  rw [jacobiSym.quadratic_reciprocity_one_mod_four
    hP114 hP10Odd]
  exact hJP10

private theorem outer17_mod_four_cancel_odd
    {g m n : Nat} (hg : Odd g)
    (hm : (g * m) % 4 = 3) (hn : (g * n) % 4 = 3) :
    m % 4 = n % 4 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hg) with hg1 | hg3
  · rw [Nat.mul_mod, hg1] at hm hn
    omega
  · rw [Nat.mul_mod, hg3] at hm hn
    omega

-- File-private, outer-`17` transfer machinery.  Factoring the common odd
-- divisor keeps the specialization valid when a Jacobi value is zero and
-- avoids division by any pseudo-remainder coefficient.
private theorem outer17_middle_coprime_transfer
    {X Y x y c d : Nat}
    (hcOdd : Odd c) (hYOdd : Odd Y) (hyOdd : Odd y)
    (hcY : Nat.Coprime c Y) (hcy : Nat.Coprime c y)
    (hcY4 : c % 4 = Y % 4) (hcy4 : c % 4 = y % 4)
    (hinv : Int.ModEq Y ((c : Int) * X) (-(y : Int)))
    (hforwardY : Int.ModEq y ((4 : Int) * Y) ((c : Int) * x))
    (hforwardC : Int.ModEq c ((4 : Int) * Y) ((d : Int) * y)) :
    jacobiSym (X : Int) Y =
      jacobiSym (d : Int) c * jacobiSym (x : Int) y := by
  have hcYInt : Int.gcd (c : Int) Y = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcY.gcd_eq_one
  have hcyInt : Int.gcd (c : Int) y = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcy.gcd_eq_one
  have hycInt : Int.gcd (y : Int) c = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_comm.mp hcy).gcd_eq_one
  have hnegSwap :
      jacobiSym (-(y : Int)) Y = jacobiSym (Y : Int) y := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hyOdd) with
      hy1 | hy3
    · have hY1 : Y % 4 = 1 := by omega
      rw [jacobiSym.neg _ hYOdd,
        ZMod.χ₄_nat_one_mod_four hY1, one_mul]
      exact
        jacobiSym.quadratic_reciprocity_one_mod_four hy1 hYOdd
    · have hY3 : Y % 4 = 3 := by omega
      rw [jacobiSym.neg _ hYOdd,
        ZMod.χ₄_nat_three_mod_four hY3, neg_one_mul]
      have hqr :=
        jacobiSym.quadratic_reciprocity_three_mod_four hy3 hY3
      omega
  have hleft :
      jacobiSym (c : Int) Y * jacobiSym (X : Int) Y =
        jacobiSym (Y : Int) y := by
    calc
      jacobiSym (c : Int) Y * jacobiSym (X : Int) Y =
          jacobiSym ((c : Int) * X) Y := by
            rw [jacobiSym.mul_left]
      _ = jacobiSym (-(y : Int)) Y :=
        jacobiSym.mod_left' hinv.eq
      _ = jacobiSym (Y : Int) y := hnegSwap
  have hYy :
      jacobiSym (Y : Int) y =
        jacobiSym (c : Int) y * jacobiSym (x : Int) y := by
    calc
      jacobiSym (Y : Int) y =
          jacobiSym ((4 : Int) * Y) y := by
            rw [jacobiSym.mul_left, jacobiSym.at_four hyOdd,
              one_mul]
      _ = jacobiSym ((c : Int) * x) y :=
        jacobiSym.mod_left' hforwardY.eq
      _ = jacobiSym (c : Int) y * jacobiSym (x : Int) y := by
        rw [jacobiSym.mul_left]
  have hYc :
      jacobiSym (Y : Int) c =
        jacobiSym (d : Int) c * jacobiSym (y : Int) c := by
    calc
      jacobiSym (Y : Int) c =
          jacobiSym ((4 : Int) * Y) c := by
            rw [jacobiSym.mul_left, jacobiSym.at_four hcOdd,
              one_mul]
      _ = jacobiSym ((d : Int) * y) c :=
        jacobiSym.mod_left' hforwardC.eq
      _ = jacobiSym (d : Int) c * jacobiSym (y : Int) c := by
        rw [jacobiSym.mul_left]
  have hcoeff :
      jacobiSym (c : Int) Y * jacobiSym (c : Int) y =
        jacobiSym (d : Int) c := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hcOdd) with
      hc1 | hc3
    · have hY1 : Y % 4 = 1 := by omega
      have hy1 : y % 4 = 1 := by omega
      rw [jacobiSym.quadratic_reciprocity_one_mod_four
          hc1 hYOdd,
        jacobiSym.quadratic_reciprocity_one_mod_four
          hc1 hyOdd,
        hYc, mul_assoc, ← pow_two, jacobiSym.sq_one hycInt,
        mul_one]
    · have hY3 : Y % 4 = 3 := by omega
      have hy3 : y % 4 = 3 := by omega
      rw [jacobiSym.quadratic_reciprocity_three_mod_four
          hc3 hY3,
        jacobiSym.quadratic_reciprocity_three_mod_four
          hc3 hy3,
        hYc]
      calc
        -(jacobiSym (d : Int) c * jacobiSym (y : Int) c) *
              -jacobiSym (y : Int) c =
            jacobiSym (d : Int) c *
              jacobiSym (y : Int) c ^ 2 := by
                ring
        _ = jacobiSym (d : Int) c := by
          rw [jacobiSym.sq_one hycInt, mul_one]
  have hcYSq : jacobiSym (c : Int) Y ^ 2 = 1 :=
    jacobiSym.sq_one hcYInt
  calc
    jacobiSym (X : Int) Y =
        jacobiSym (c : Int) Y ^ 2 * jacobiSym (X : Int) Y := by
          rw [hcYSq, one_mul]
    _ = jacobiSym (c : Int) Y *
          (jacobiSym (c : Int) Y * jacobiSym (X : Int) Y) := by
            ring
    _ = jacobiSym (c : Int) Y * jacobiSym (Y : Int) y := by
      rw [hleft]
    _ = jacobiSym (c : Int) Y *
          (jacobiSym (c : Int) y * jacobiSym (x : Int) y) := by
            rw [hYy]
    _ = (jacobiSym (c : Int) Y * jacobiSym (c : Int) y) *
          jacobiSym (x : Int) y := by
            ring
    _ = jacobiSym (d : Int) c * jacobiSym (x : Int) y := by
      rw [hcoeff]

private theorem outer17_middle_factor_transfer
    {X Y x y C d g c Y' y' : Nat}
    (hC : C = g * c) (hY : Y = g * Y') (hy : y = g * y')
    (hgOdd : Odd g) (hcOdd : Odd c)
    (hY'Odd : Odd Y') (hy'Odd : Odd y')
    (hcY' : Nat.Coprime c Y') (hcy' : Nat.Coprime c y')
    (hcY4 : c % 4 = Y' % 4) (hcy4 : c % 4 = y' % 4)
    (hdg : Nat.Coprime d g)
    (hinv : Int.ModEq Y' ((c : Int) * X) (-(y' : Int)))
    (hforwardY :
      Int.ModEq y' ((4 : Int) * Y') ((c : Int) * x))
    (hforwardC :
      Int.ModEq c ((4 : Int) * Y') ((d : Int) * y'))
    (hcross : Int.ModEq g (x : Int) ((d : Int) * X)) :
    jacobiSym (X : Int) Y =
      jacobiSym (d : Int) C * jacobiSym (x : Int) y := by
  have hbase :=
    outer17_middle_coprime_transfer hcOdd hY'Odd hy'Odd
      hcY' hcy' hcY4 hcy4 hinv hforwardY hforwardC
  have hdgInt : Int.gcd (d : Int) g = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hdg.gcd_eq_one
  have hdgSq : jacobiSym (d : Int) g ^ 2 = 1 :=
    jacobiSym.sq_one hdgInt
  have hcrossJ :
      jacobiSym (x : Int) g =
        jacobiSym (d : Int) g * jacobiSym (X : Int) g := by
    calc
      jacobiSym (x : Int) g =
          jacobiSym ((d : Int) * X) g :=
        jacobiSym.mod_left' hcross.eq
      _ = jacobiSym (d : Int) g * jacobiSym (X : Int) g := by
        rw [jacobiSym.mul_left]
  rw [hY, hC, hy,
    jacobiSym.mul_right' _ hgOdd.pos.ne' hY'Odd.pos.ne',
    jacobiSym.mul_right' _ hgOdd.pos.ne' hcOdd.pos.ne',
    jacobiSym.mul_right' _ hgOdd.pos.ne' hy'Odd.pos.ne']
  rw [hbase, hcrossJ]
  calc
    jacobiSym (X : Int) g *
          (jacobiSym (d : Int) c * jacobiSym (x : Int) y') =
        jacobiSym (d : Int) g ^ 2 * jacobiSym (X : Int) g *
          (jacobiSym (d : Int) c * jacobiSym (x : Int) y') := by
            rw [hdgSq, one_mul]
    _ = (jacobiSym (d : Int) g * jacobiSym (d : Int) c) *
          ((jacobiSym (d : Int) g * jacobiSym (X : Int) g) *
            jacobiSym (x : Int) y') := by
              ring

private theorem outer17_middle_det_two_transfer
    {X Y x y a b C d : Nat}
    (hC4 : C % 4 = 3) (hY4 : Y % 4 = 3)
    (hy4 : y % 4 = 3)
    (hforward : 4 * Y = C * x + d * y)
    (hinvX : x + 2 * b * Y = d * X)
    (hinvY : y + C * X = 2 * a * Y)
    (hdet : a * d = b * C + 2) :
    jacobiSym (X : Int) Y =
      jacobiSym (d : Int) C * jacobiSym (x : Int) y := by
  let g := C.gcd y
  let c := C / g
  let Y' := Y / g
  let y' := y / g
  have hCOdd : Odd C := Nat.odd_iff.mpr (by omega)
  have hYOdd : Odd Y := Nat.odd_iff.mpr (by omega)
  have hyOdd : Odd y := Nat.odd_iff.mpr (by omega)
  have hCpos : 0 < C := by omega
  have hgpos : 0 < g :=
    Nat.gcd_pos_of_pos_left y hCpos
  have hgOdd : Odd g :=
    Odd.of_dvd_nat hCOdd (Nat.gcd_dvd_left C y)
  have hCfac : C = g * c := by
    dsimp [g, c]
    rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left C y)]
  have hyfac : y = g * y' := by
    dsimp [g, y']
    rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right C y)]
  have hgY : g ∣ Y := by
    have hgCx : g ∣ C * x :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_left C y) x
    have hgdy : g ∣ d * y :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right C y) d
    have hg4Y : g ∣ 4 * Y := by
      rw [hforward]
      exact Nat.dvd_add hgCx hgdy
    have hg4 : Nat.Coprime g 4 := by
      simpa [show (4 : Nat) = 2 ^ 2 by decide] using
        hgOdd.coprime_two_right.pow_right 2
    exact hg4.dvd_of_dvd_mul_left hg4Y
  have hYfac : Y = g * Y' := by
    dsimp [Y']
    rw [mul_comm, Nat.div_mul_cancel hgY]
  have hcOdd : Odd c := by
    rw [hCfac] at hCOdd
    exact (Nat.odd_mul.mp hCOdd).2
  have hY'Odd : Odd Y' := by
    rw [hYfac] at hYOdd
    exact (Nat.odd_mul.mp hYOdd).2
  have hy'Odd : Odd y' := by
    rw [hyfac] at hyOdd
    exact (Nat.odd_mul.mp hyOdd).2
  have hcy' : Nat.Coprime c y' := by
    dsimp [c, y', g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hforward' : 4 * Y' = c * x + d * y' := by
    apply Nat.mul_left_cancel hgpos
    calc
      g * (4 * Y') = 4 * Y := by
        rw [hYfac]
        ring
      _ = C * x + d * y := hforward
      _ = g * (c * x + d * y') := by
        rw [hCfac, hyfac]
        ring
  have hinvY' : y' + c * X = 2 * a * Y' := by
    apply Nat.mul_left_cancel hgpos
    calc
      g * (y' + c * X) = y + C * X := by
        rw [hCfac, hyfac]
        ring
      _ = 2 * a * Y := hinvY
      _ = g * (2 * a * Y') := by
        rw [hYfac]
        ring
  have hcY' : Nat.Coprime c Y' := by
    apply Nat.coprime_of_dvd'
    intro p hp hpc hpY'
    have hpcX : p ∣ c * X :=
      dvd_mul_of_dvd_left hpc X
    have hpRhs : p ∣ 2 * a * Y' :=
      dvd_mul_of_dvd_right hpY' (2 * a)
    have hpSum : p ∣ y' + c * X := by
      rw [hinvY']
      exact hpRhs
    have hpy' : p ∣ y' :=
      (Nat.dvd_add_iff_left hpcX).mpr hpSum
    rw [← hcy'.gcd_eq_one]
    exact Nat.dvd_gcd hpc hpy'
  have hcY4 : c % 4 = Y' % 4 := by
    apply outer17_mod_four_cancel_odd hgOdd
    · rwa [← hCfac]
    · rwa [← hYfac]
  have hcy4 : c % 4 = y' % 4 := by
    apply outer17_mod_four_cancel_odd hgOdd
    · rwa [← hCfac]
    · rwa [← hyfac]
  have hdg : Nat.Coprime d g := by
    apply Nat.coprime_of_dvd'
    intro p hp hpd hpg
    have hpC : p ∣ C :=
      hpg.trans (Nat.gcd_dvd_left C y)
    have hpad : p ∣ a * d :=
      dvd_mul_of_dvd_right hpd a
    have hpbC : p ∣ b * C :=
      dvd_mul_of_dvd_right hpC b
    have hp2 : p ∣ 2 := by
      have hpSum : p ∣ b * C + 2 := by
        rw [← hdet]
        exact hpad
      exact (Nat.dvd_add_iff_right hpbC).mpr hpSum
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with hp1 | hp2eq
    · exact hp1 ▸ dvd_rfl
    · subst p
      have hgEven : g % 2 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp hpg
      have hgOddMod : g % 2 = 1 :=
        Nat.odd_iff.mp hgOdd
      omega
  have hinvMod :
      Int.ModEq Y' ((c : Int) * X) (-(y' : Int)) := by
    have hinvYInt :
        (y' : Int) + (c : Int) * X = 2 * (a : Int) * Y' := by
      exact_mod_cast hinvY'
    apply Int.modEq_of_dvd
    use -(2 * (a : Int))
    linear_combination -hinvYInt
  have hforwardInt :
      (4 : Int) * Y' = (c : Int) * x + (d : Int) * y' := by
    exact_mod_cast hforward'
  have hforwardYMod :
      Int.ModEq y' ((4 : Int) * Y') ((c : Int) * x) := by
    apply Int.modEq_of_dvd
    use -(d : Int)
    linear_combination -hforwardInt
  have hforwardCMod :
      Int.ModEq c ((4 : Int) * Y') ((d : Int) * y') := by
    apply Int.modEq_of_dvd
    use -(x : Int)
    linear_combination -hforwardInt
  have hcross : Int.ModEq g (x : Int) ((d : Int) * X) := by
    have hinvXInt :
        (x : Int) + 2 * (b : Int) * Y = (d : Int) * X := by
      exact_mod_cast hinvX
    have hYfacInt : (Y : Int) = (g : Int) * Y' := by
      exact_mod_cast hYfac
    apply Int.modEq_of_dvd
    use 2 * (b : Int) * Y'
    linear_combination
      -hinvXInt + 2 * (b : Int) * hYfacInt
  exact
    outer17_middle_factor_transfer hCfac hYfac hyfac hgOdd
      hcOdd hY'Odd hy'Odd hcY' hcy' hcY4 hcy4 hdg hinvMod
      hforwardYMod hforwardCMod hcross

private def outer17MiddleA (k : Nat) : Nat :=
  4096 * k ^ 3 + 15488 * k ^ 2 + 8496 * k + 1361

private def outer17MiddleB (k : Nat) : Nat :=
  896 * k ^ 2 + 3152 * k + 1019

private def outer17MiddleC (k : Nat) : Nat :=
  16640 * k ^ 2 + 10376 * k + 1751

private def outer17MiddleD (k : Nat) : Nat :=
  3640 * k + 1311

private def outer17MiddleQ (k : Nat) : Nat :=
  224 * k + 59

private theorem outer17_middle_identities (k : Nat) :
    4 * outer17P7 k =
        outer17MiddleC k * outer17P9 k +
          outer17MiddleD k * outer17P10 k ∧
      outer17P9 k +
          2 * outer17MiddleB k * outer17P7 k =
        outer17MiddleD k * outer17P6 k ∧
      outer17P10 k +
          outer17MiddleC k * outer17P6 k =
        2 * outer17MiddleA k * outer17P7 k ∧
      outer17MiddleA k * outer17MiddleD k =
        outer17MiddleB k * outer17MiddleC k + 2 ∧
      49 * outer17MiddleC k =
        outer17MiddleQ k * outer17MiddleD k + 2 * 65 ^ 2 := by
  rcases outer17P_casts k with
    ⟨_, _, _, _, _, _, h6, h7, _, h9, h10, _, _, _, _⟩
  constructor
  · have hi :
        4 * (outer17P7 k : Int) =
          (outer17MiddleC k : Int) * outer17P9 k +
            (outer17MiddleD k : Int) * outer17P10 k := by
      rw [h7, h9, h10]
      simp only [outer17MiddleC, outer17MiddleD, outer17A,
        outer17R7, outer17R9, outer17R10]
      push_cast
      ring
    exact_mod_cast hi
  constructor
  · have hi :
        (outer17P9 k : Int) +
            2 * (outer17MiddleB k : Int) * outer17P7 k =
          (outer17MiddleD k : Int) * outer17P6 k := by
      rw [h6, h7, h9]
      simp only [outer17MiddleB, outer17MiddleD, outer17A,
        outer17R6, outer17R7, outer17R9]
      push_cast
      ring
    exact_mod_cast hi
  constructor
  · have hi :
        (outer17P10 k : Int) +
            (outer17MiddleC k : Int) * outer17P6 k =
          2 * (outer17MiddleA k : Int) * outer17P7 k := by
      rw [h6, h7, h10]
      simp only [outer17MiddleA, outer17MiddleC, outer17A,
        outer17R6, outer17R7, outer17R10]
      push_cast
      ring
    exact_mod_cast hi
  constructor
  · simp only [outer17MiddleA, outer17MiddleB,
      outer17MiddleC, outer17MiddleD]
    ring
  · simp only [outer17MiddleC, outer17MiddleD, outer17MiddleQ]
    ring

private theorem outer17_middle_moduli (k : Nat) :
    outer17MiddleC k % 4 = 3 ∧
      outer17MiddleD k % 4 = 3 ∧
      outer17MiddleD k % 8 = 7 ∧
      outer17MiddleD k % 7 = 2 ∧
      outer17MiddleD k % 5 = 1 ∧
      outer17MiddleD k % 13 = 11 := by
  norm_num [outer17MiddleC, outer17MiddleD, Nat.add_mod,
    Nat.mul_mod]

private theorem outer17_middle_multiplier (k : Nat) :
    jacobiSym (outer17MiddleD k : Int) (outer17MiddleC k) =
      -1 := by
  rcases outer17_middle_identities k with
    ⟨_, _, _, _, hmult⟩
  rcases outer17_middle_moduli k with
    ⟨hC4, hD4, hD8, hD7, hD5, hD13⟩
  have hDOdd : Odd (outer17MiddleD k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hD4)
  have hCOdd : Odd (outer17MiddleC k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hC4)
  have h7D : Nat.Coprime 7 (outer17MiddleD k) := by
    rw [Nat.Coprime, Nat.gcd_rec, hD7]
    norm_num
  have h5D : Nat.Coprime 5 (outer17MiddleD k) := by
    rw [Nat.Coprime, Nat.gcd_rec, hD5]
    norm_num
  have h13D : Nat.Coprime 13 (outer17MiddleD k) := by
    rw [Nat.Coprime, Nat.gcd_rec, hD13]
    norm_num
  have h65D : Nat.Coprime 65 (outer17MiddleD k) := by
    exact Nat.Coprime.mul_left h5D h13D
  have h7DInt :
      Int.gcd (7 : Int) (outer17MiddleD k) = 1 := by
    change Int.gcd ((7 : Nat) : Int)
      ((outer17MiddleD k : Nat) : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact h7D.gcd_eq_one
  have h65DInt :
      Int.gcd (65 : Int) (outer17MiddleD k) = 1 := by
    change Int.gcd ((65 : Nat) : Int)
      ((outer17MiddleD k : Nat) : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact h65D.gcd_eq_one
  have hmultInt :
      49 * (outer17MiddleC k : Int) =
        (outer17MiddleQ k : Int) * outer17MiddleD k +
          2 * (65 : Int) ^ 2 := by
    exact_mod_cast hmult
  have hmod :
      (49 * (outer17MiddleC k : Int)) ≡ 2 * (65 : Int) ^ 2
        [ZMOD (outer17MiddleD k : Int)] := by
    apply Int.modEq_of_dvd
    use -(outer17MiddleQ k : Int)
    linear_combination -hmultInt
  have hJTwoD :
      jacobiSym (2 : Int) (outer17MiddleD k) = 1 := by
    rw [jacobiSym.at_two hDOdd, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [Nat.odd_iff.mp hDOdd, hD8]
  have hJC :
      jacobiSym (outer17MiddleC k : Int)
        (outer17MiddleD k) = 1 := by
    have hs := jacobiSym.mod_left' hmod
    rw [show (49 : Int) = (7 : Int) ^ 2 by norm_num,
      jacobiSym.mul_left, jacobiSym.sq_one' h7DInt, one_mul,
      jacobiSym.mul_left, hJTwoD,
      jacobiSym.sq_one' h65DInt, one_mul] at hs
    exact hs
  have hqr :=
    jacobiSym.quadratic_reciprocity_three_mod_four hC4 hD4
  rw [hJC] at hqr
  linarith

private theorem outer17_middle_jacobi (k : Nat) :
    jacobiSym (outer17P6 k : Int) (outer17P7 k) =
      -jacobiSym (outer17P9 k : Int) (outer17P10 k) := by
  rcases outer17_middle_identities k with
    ⟨hforward, hinvX, hinvY, hdet, _⟩
  rcases outer17P_mod_eight k with
    ⟨_, _, _, _, _, _, _, hP7, _, _, hP10, _, _, _, _⟩
  rcases outer17_middle_moduli k with ⟨hC4, _, _, _, _, _⟩
  have hP74 : outer17P7 k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P7 k) (by decide : 4 ∣ 8)
    rw [hP7] at hm
    omega
  have hP104 : outer17P10 k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P10 k) (by decide : 4 ∣ 8)
    rw [hP10] at hm
    omega
  have htransfer :=
    outer17_middle_det_two_transfer hC4 hP74 hP104
      hforward hinvX hinvY hdet
  rw [htransfer, outer17_middle_multiplier k]
  ring

private def outer17TopC (k : Nat) : Nat :=
  90112 * k ^ 3 + 68096 * k ^ 2 + 18448 * k + 1757

private def outer17TopB (k : Nat) : Nat :=
  1081344 * k ^ 4 + 1087488 * k ^ 3 +
    423552 * k ^ 2 + 75360 * k + 5107

private def outer17TopS (k : Nat) : Nat :=
  528 * k ^ 2 + 267 * k + 41

private def outer17TopL (k : Nat) : Nat :=
  176 * k + 23

private def outer17TopA (k : Nat) : Nat :=
  9 * outer17TopC k

private def outer17TopBeta (k : Nat) : Nat :=
  4 * outer17TopB k

private theorem outer17_top_multiplier_identities (k : Nat) :
    outer17TopB k + 4 * outer17TopS k =
        (12 * k + 3) * outer17TopC k ∧
      3 * outer17TopC k =
        (512 * k + 128) * outer17TopS k + outer17TopL k ∧
      8 * outer17TopS k =
        (24 * k + 9) * outer17TopL k + 121 := by
  simp only [outer17TopB, outer17TopS, outer17TopC,
    outer17TopL]
  constructor
  · ring
  constructor <;> ring

private theorem outer17_top_multiplier_moduli (k : Nat) :
    outer17TopC k % 8 = 5 ∧
      outer17TopBeta k % 3 = 1 ∧
      outer17TopS k % 3 = 2 ∧
      outer17TopL k % 8 = 7 ∧
      outer17TopL k % 11 = 1 := by
  norm_num [outer17TopC, outer17TopB, outer17TopBeta,
    outer17TopS, outer17TopL, Nat.add_mod, Nat.mul_mod]

set_option maxHeartbeats 800000 in
private theorem outer17_top_multiplier (k : Nat) :
    jacobiSym (-(outer17TopBeta k : Int)) (outer17TopA k) =
      -1 := by
  rcases outer17_top_multiplier_identities k with
    ⟨hBS, hCS, hSL⟩
  rcases outer17_top_multiplier_moduli k with
    ⟨hC8, hBeta3, hS3, hL8, hL11⟩
  have hC4 : outer17TopC k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17TopC k) (by decide : 4 ∣ 8)
    rw [hC8] at hm
    omega
  have hL4 : outer17TopL k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17TopL k) (by decide : 4 ∣ 8)
    rw [hL8] at hm
    omega
  have hCOdd : Odd (outer17TopC k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hC4)
  have hLOdd : Odd (outer17TopL k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hL4)
  have hCpos : 0 < outer17TopC k := by
    simp only [outer17TopC]
    positivity
  have hSpos : 0 < outer17TopS k := by
    simp only [outer17TopS]
    positivity
  have hLpos : 0 < outer17TopL k := by
    simp only [outer17TopL]
    positivity
  have h11L : Nat.Coprime 11 (outer17TopL k) := by
    rw [Nat.Coprime, Nat.gcd_rec, hL11]
    norm_num
  have h11LInt :
      Int.gcd (11 : Int) (outer17TopL k) = 1 := by
    change Int.gcd ((11 : Nat) : Int)
      ((outer17TopL k : Nat) : Int) = 1
    rw [Int.gcd_natCast_natCast]
    exact h11L.gcd_eq_one
  have hJEightL :
      jacobiSym (8 : Int) (outer17TopL k) = 1 := by
    calc
      jacobiSym (8 : Int) (outer17TopL k) =
          jacobiSym ((2 : Int) * 4) (outer17TopL k) := by
            norm_num
      _ = 1 := by
        rw [jacobiSym.mul_left, jacobiSym.at_two hLOdd,
          jacobiSym.at_four hLOdd,
          ZMod.χ₈_nat_eq_if_mod_eight]
        simp [Nat.odd_iff.mp hLOdd, hL8]
  have hJ121L :
      jacobiSym (121 : Int) (outer17TopL k) = 1 := by
    calc
      jacobiSym (121 : Int) (outer17TopL k) =
          jacobiSym ((11 : Int) ^ 2) (outer17TopL k) := by
            norm_num
      _ = 1 := jacobiSym.sq_one' h11LInt
  have hJSL :
      jacobiSym (outer17TopS k : Int) (outer17TopL k) = 1 := by
    have hSLInt :
        8 * (outer17TopS k : Int) =
          (24 * (k : Int) + 9) * outer17TopL k + 121 := by
      exact_mod_cast hSL
    have hmod :
        (8 * (outer17TopS k : Int)) ≡ 121
          [ZMOD (outer17TopL k : Int)] := by
      apply Int.modEq_of_dvd
      use -(24 * (k : Int) + 9)
      linear_combination -hSLInt
    have hs := jacobiSym.mod_left' hmod
    rw [jacobiSym.mul_left, hJEightL, one_mul, hJ121L] at hs
    exact hs
  have hJS3 :
      jacobiSym (outer17TopS k : Int) 3 = -1 := by
    have hmod :
        ((outer17TopS k : Int) % 3) = ((2 : Int) % 3) := by
      exact_mod_cast hS3
    calc
      jacobiSym (outer17TopS k : Int) 3 =
          jacobiSym (2 : Int) 3 :=
        jacobiSym.mod_left' hmod
      _ = -1 := by norm_num
  have hLlt : outer17TopL k < 4 * outer17TopS k := by
    simp only [outer17TopL, outer17TopS]
    nlinarith
  have hCSform :
      3 * outer17TopC k =
        (128 * k + 32) * (4 * outer17TopS k) +
          outer17TopL k := by
    calc
      3 * outer17TopC k =
          (512 * k + 128) * outer17TopS k +
            outer17TopL k := hCS
      _ = (128 * k + 32) * (4 * outer17TopS k) +
          outer17TopL k := by ring
  have hrem :
      (3 * outer17TopC k) % (4 * outer17TopS k) =
        outer17TopL k := by
    rw [hCSform]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hLlt]
  have hJden :
      jacobiSym (outer17TopS k : Int) (3 * outer17TopC k) =
        jacobiSym (outer17TopS k : Int) (outer17TopL k) := by
    rw [jacobiSym.mod_right' (outer17TopS k)
        (Odd.mul (by decide) hCOdd),
      hrem,
      jacobiSym.mod_right' (outer17TopS k) hLOdd,
      Nat.mod_eq_of_lt hLlt]
  have hJSC :
      jacobiSym (outer17TopS k : Int) (outer17TopC k) =
        -1 := by
    have hmul :=
      jacobiSym.mul_right' (outer17TopS k : Int)
        (by decide : (3 : Nat) ≠ 0) hCpos.ne'
    rw [hmul, hJS3, hJSL] at hJden
    norm_num at hJden
    linarith
  have hBSInt :
      (outer17TopB k : Int) + 4 * outer17TopS k =
        (12 * (k : Int) + 3) * outer17TopC k := by
    exact_mod_cast hBS
  have hmodBC :
      (-(outer17TopBeta k : Int)) ≡
        16 * (outer17TopS k : Int)
        [ZMOD (outer17TopC k : Int)] := by
    apply Int.modEq_of_dvd
    use 4 * (12 * (k : Int) + 3)
    simp only [outer17TopBeta]
    push_cast
    linear_combination 4 * hBSInt
  have hJnegBetaC :
      jacobiSym (-(outer17TopBeta k : Int)) (outer17TopC k) =
        -1 := by
    calc
      jacobiSym (-(outer17TopBeta k : Int)) (outer17TopC k) =
          jacobiSym (16 * (outer17TopS k : Int))
            (outer17TopC k) :=
        jacobiSym.mod_left' hmodBC.eq
      _ = jacobiSym (16 : Int) (outer17TopC k) *
          jacobiSym (outer17TopS k : Int) (outer17TopC k) := by
            rw [jacobiSym.mul_left]
      _ = -1 := by
        rw [show (16 : Int) = (4 : Int) * 4 by norm_num,
          jacobiSym.mul_left, jacobiSym.at_four hCOdd, hJSC]
        norm_num
  have hJnegBeta3 :
      jacobiSym (-(outer17TopBeta k : Int)) 3 = -1 := by
    have hBeta3Int :
        ((outer17TopBeta k : Int) % 3) = 1 := by
      exact_mod_cast hBeta3
    have hmod :
        ((-(outer17TopBeta k : Int)) % 3) = ((2 : Int) % 3) := by
      omega
    calc
      jacobiSym (-(outer17TopBeta k : Int)) 3 =
          jacobiSym (2 : Int) 3 :=
        jacobiSym.mod_left' hmod
      _ = -1 := by norm_num
  have hJnegBetaNine :
      jacobiSym (-(outer17TopBeta k : Int)) 9 = 1 := by
    calc
      jacobiSym (-(outer17TopBeta k : Int)) 9 =
          jacobiSym (-(outer17TopBeta k : Int)) (3 ^ 2) := by
            norm_num
      _ = jacobiSym (-(outer17TopBeta k : Int)) 3 ^ 2 :=
        jacobiSym.pow_right _ _ _
      _ = 1 := by rw [hJnegBeta3]; norm_num
  change
    jacobiSym (-(outer17TopBeta k : Int))
      (9 * outer17TopC k) = -1
  rw [jacobiSym.mul_right' _
      (by decide : (9 : Nat) ≠ 0) hCpos.ne',
    hJnegBetaNine, hJnegBetaC, one_mul]

private def outer17TopLowerLeft (k : Nat) : Int :=
  -196608 * (k : Int) ^ 4 + 368640 * (k : Int) ^ 3 +
    350592 * (k : Int) ^ 2 + 102048 * k + 10084

private def outer17TopLowerRight (k : Nat) : Int :=
  1048576 * (k : Int) ^ 5 - 1703936 * (k : Int) ^ 4 -
    2363392 * (k : Int) ^ 3 - 1007360 * (k : Int) ^ 2 -
    187280 * k - 13027

private theorem outer17_top_matrix_identities (k : Nat) :
    (outer17P6 k : Int) =
        (outer17TopA k : Int) * outer17P1 k -
          (outer17TopBeta k : Int) * outer17P2 k ∧
      (outer17P7 k : Int) =
        outer17TopLowerLeft k * outer17P1 k +
          outer17TopLowerRight k * outer17P2 k ∧
      (outer17TopA k : Int) * outer17TopLowerRight k -
          (-(outer17TopBeta k : Int)) *
            outer17TopLowerLeft k = 1 := by
  rcases outer17P_casts k with
    ⟨_, h1, h2, _, _, _, h6, h7, _, _, _, _, _, _, _⟩
  constructor
  · rw [h1, h2, h6]
    simp only [outer17TopA, outer17TopC, outer17TopBeta,
      outer17TopB, outer17A, outer17R1, outer17R2, outer17R6]
    push_cast
    ring
  constructor
  · rw [h1, h2, h7]
    simp only [outer17TopLowerLeft, outer17TopLowerRight,
      outer17A, outer17R1, outer17R2, outer17R7]
    ring
  · simp only [outer17TopA, outer17TopC, outer17TopBeta,
      outer17TopB, outer17TopLowerLeft, outer17TopLowerRight]
    push_cast
    ring

private theorem outer17_top_coefficient_moduli (k : Nat) :
    outer17TopA k % 4 = 1 ∧
      (-(outer17TopBeta k : Int)) % 4 = 0 ∧
      outer17TopLowerLeft k % 4 = 0 ∧
      outer17TopLowerRight k % 4 = 1 := by
  constructor
  · norm_num [outer17TopA, outer17TopC, Nat.add_mod,
      Nat.mul_mod]
  constructor
  · simp [outer17TopBeta]
  constructor
  · have hc :
        outer17TopLowerLeft k =
          4 * (-49152 * (k : Int) ^ 4 +
            92160 * (k : Int) ^ 3 +
            87648 * (k : Int) ^ 2 + 25512 * k + 2521) := by
          simp only [outer17TopLowerLeft]
          ring
    rw [hc]
    simp
  · have hd :
        outer17TopLowerRight k =
          4 * (262144 * (k : Int) ^ 5 -
            425984 * (k : Int) ^ 4 -
            590848 * (k : Int) ^ 3 -
            251840 * (k : Int) ^ 2 -
            46820 * k - 3257) + 1 := by
          simp only [outer17TopLowerRight]
          ring
    rw [hd]
    simp

-- This file-private transfer is specialized immediately to the exact
-- outer-`17` unimodular matrix.  The GCD split is what preserves the
-- non-coprime Jacobi cases without introducing a generic public framework.
private theorem outer17_top_unimodular_transfer
    {X Y x y a : Nat} {b c d : Int}
    (ha4 : a % 4 = 1) (hX4 : X % 4 = 1)
    (hx4 : x % 4 = 1) (hY4 : Y % 4 = 3)
    (hy4 : y % 4 = 3)
    (hforwardX :
      (X : Int) = (a : Int) * x + b * y)
    (hforwardY :
      (Y : Int) = c * x + d * y)
    (hdet : (a : Int) * d - b * c = 1) :
    jacobiSym (X : Int) Y =
      jacobiSym b a * jacobiSym (x : Int) y := by
  let g := a.gcd y
  let a' := a / g
  let y' := y / g
  let X' := X / g
  have haOdd : Odd a :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one ha4)
  have hXOdd : Odd X :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hX4)
  have hxOdd : Odd x :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hx4)
  have hYOdd : Odd Y :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hY4)
  have hyOdd : Odd y :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hy4)
  have hapos : 0 < a := haOdd.pos
  have hgpos : 0 < g :=
    Nat.gcd_pos_of_pos_left y hapos
  have hgOdd : Odd g :=
    Odd.of_dvd_nat haOdd (Nat.gcd_dvd_left a y)
  have hafac : a = g * a' := by
    dsimp [g, a']
    rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left a y)]
  have hyfac : y = g * y' := by
    dsimp [g, y']
    rw [mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right a y)]
  have hgX : g ∣ X := by
    apply Int.natCast_dvd_natCast.mp
    rw [hforwardX]
    exact dvd_add
      (dvd_mul_of_dvd_left
        (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a y)) _)
      (dvd_mul_of_dvd_right
        (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a y)) _)
  have hXfac : X = g * X' := by
    dsimp [X']
    rw [mul_comm, Nat.div_mul_cancel hgX]
  have ha'Odd : Odd a' := by
    rw [hafac] at haOdd
    exact (Nat.odd_mul.mp haOdd).2
  have hy'Odd : Odd y' := by
    rw [hyfac] at hyOdd
    exact (Nat.odd_mul.mp hyOdd).2
  have hX'Odd : Odd X' := by
    rw [hXfac] at hXOdd
    exact (Nat.odd_mul.mp hXOdd).2
  have hay' : Nat.Coprime a' y' := by
    dsimp [a', y', g]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hab : Nat.Coprime b.natAbs a := by
    apply Nat.coprime_of_dvd'
    intro p _ hpb hpa
    have hpbInt : (p : Int) ∣ b := by
      apply Int.dvd_natAbs.mp
      exact Int.natCast_dvd_natCast.mpr hpb
    have hpaInt : (p : Int) ∣ (a : Int) :=
      Int.natCast_dvd_natCast.mpr hpa
    have hpOne : (p : Int) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub
        (dvd_mul_of_dvd_left hpaInt d)
        (dvd_mul_of_dvd_left hpbInt c)
    have hpNat : p ∣ 1 := by
      exact_mod_cast hpOne
    exact hpNat
  have hbg : Nat.Coprime b.natAbs g :=
    hab.of_dvd_right (Nat.gcd_dvd_left a y)
  have hba' : Nat.Coprime b.natAbs a' := by
    apply hab.of_dvd_right
    use g
    rw [hafac]
    ring
  have hInv :
      (a : Int) * Y - c * X = y := by
    rw [hforwardX, hforwardY]
    linear_combination (y : Int) * hdet
  have hXred :
      (X' : Int) = (a' : Int) * x + b * y' := by
    have hfacXInt : (X : Int) = (g : Int) * X' := by
      exact_mod_cast hXfac
    have hfacaInt : (a : Int) = (g : Int) * a' := by
      exact_mod_cast hafac
    have hfacyInt : (y : Int) = (g : Int) * y' := by
      exact_mod_cast hyfac
    have hgInt : (g : Int) ≠ 0 := by exact_mod_cast hgpos.ne'
    apply mul_left_cancel₀ hgInt
    rw [← hfacXInt, hforwardX, hfacaInt, hfacyInt]
    ring
  have hInvRed :
      (a' : Int) * Y - c * X' = y' := by
    have hfacXInt : (X : Int) = (g : Int) * X' := by
      exact_mod_cast hXfac
    have hfacaInt : (a : Int) = (g : Int) * a' := by
      exact_mod_cast hafac
    have hfacyInt : (y : Int) = (g : Int) * y' := by
      exact_mod_cast hyfac
    have hgInt : (g : Int) ≠ 0 := by exact_mod_cast hgpos.ne'
    apply mul_left_cancel₀ hgInt
    calc
      (g : Int) * ((a' : Int) * Y - c * X') =
          (a : Int) * Y - c * X := by
            rw [hfacaInt, hfacXInt]
            ring
      _ = y := hInv
      _ = (g : Int) * y' := hfacyInt
  have ha'X' : Nat.Coprime a' X' := by
    apply Nat.coprime_of_dvd'
    intro p _ hpa' hpX'
    have hpa'Int : (p : Int) ∣ (a' : Int) :=
      Int.natCast_dvd_natCast.mpr hpa'
    have hpX'Int : (p : Int) ∣ (X' : Int) :=
      Int.natCast_dvd_natCast.mpr hpX'
    have hpy'Int : (p : Int) ∣ (y' : Int) := by
      rw [← hInvRed]
      exact dvd_sub
        (dvd_mul_of_dvd_left hpa'Int _)
        (dvd_mul_of_dvd_right hpX'Int _)
    have hpy' : p ∣ y' :=
      Int.natCast_dvd_natCast.mp hpy'Int
    rw [← hay'.gcd_eq_one]
    exact Nat.dvd_gcd hpa' hpy'
  have ha'X'Int :
      Int.gcd (a' : Int) X' = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ha'X'.gcd_eq_one
  have hay'Int :
      Int.gcd (a' : Int) y' = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hay'.gcd_eq_one
  have hy'a'Int :
      Int.gcd (y' : Int) a' = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hay'.symm.gcd_eq_one
  have hba'Int :
      Int.gcd b a' = 1 := by
    rw [Int.gcd_def, Int.natAbs_natCast]
    exact hba'.gcd_eq_one
  have hbgInt :
      Int.gcd b g = 1 := by
    rw [Int.gcd_def, Int.natAbs_natCast]
    exact hbg.gcd_eq_one
  have hleft :
      jacobiSym (a' : Int) X' * jacobiSym (Y : Int) X' =
        jacobiSym (y' : Int) X' := by
    calc
      jacobiSym (a' : Int) X' * jacobiSym (Y : Int) X' =
          jacobiSym ((a' : Int) * Y) X' := by
            rw [jacobiSym.mul_left]
      _ = jacobiSym (y' : Int) X' := by
        have hmod :
            Int.ModEq (X' : Int) ((a' : Int) * Y) y' := by
          rw [Int.modEq_iff_dvd]
          use -c
          rw [← hInvRed]
          ring
        exact jacobiSym.mod_left' hmod.eq
  have hleftSolved :
      jacobiSym (Y : Int) X' =
        jacobiSym (a' : Int) X' *
          jacobiSym (y' : Int) X' := by
    have hsquare :=
      jacobiSym.sq_one ha'X'Int
    calc
      jacobiSym (Y : Int) X' =
          jacobiSym (a' : Int) X' ^ 2 *
            jacobiSym (Y : Int) X' := by rw [hsquare, one_mul]
      _ = jacobiSym (a' : Int) X' *
            (jacobiSym (a' : Int) X' *
              jacobiSym (Y : Int) X') := by ring
      _ = jacobiSym (a' : Int) X' *
            jacobiSym (y' : Int) X' := by rw [hleft]
  have hXy :
      jacobiSym (X' : Int) y' =
        jacobiSym (a' : Int) y' *
          jacobiSym (x : Int) y' := by
    calc
      jacobiSym (X' : Int) y' =
          jacobiSym ((a' : Int) * x) y' := by
            have hmod :
                Int.ModEq (y' : Int) X' ((a' : Int) * x) := by
              rw [Int.modEq_iff_dvd]
              use -b
              rw [hXred]
              ring
            exact jacobiSym.mod_left' hmod.eq
      _ = jacobiSym (a' : Int) y' *
          jacobiSym (x : Int) y' := by
            rw [jacobiSym.mul_left]
  have hcoeff :
      jacobiSym (X' : Int) a' * jacobiSym (y' : Int) a' =
        jacobiSym b a' := by
    have hmod :
        ((X' : Int) * y') ≡ b * (y' : Int) ^ 2
          [ZMOD (a' : Int)] := by
      rw [Int.modEq_iff_dvd]
      use -(x : Int) * y'
      linear_combination -(y' : Int) * hXred
    have hs := jacobiSym.mod_left' hmod
    rw [jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.sq_one' hy'a'Int, mul_one] at hs
    exact hs
  have hgCase :
      (g % 4 = 1 ∧ a' % 4 = 1 ∧ X' % 4 = 1 ∧ y' % 4 = 3) ∨
      (g % 4 = 3 ∧ a' % 4 = 3 ∧ X' % 4 = 3 ∧ y' % 4 = 1) := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hgOdd) with
      hg1 | hg3
    · left
      refine ⟨hg1, ?_, ?_, ?_⟩
      · rw [hafac, Nat.mul_mod, hg1] at ha4
        omega
      · rw [hXfac, Nat.mul_mod, hg1] at hX4
        omega
      · rw [hyfac, Nat.mul_mod, hg1] at hy4
        omega
    · right
      refine ⟨hg3, ?_, ?_, ?_⟩
      · rw [hafac, Nat.mul_mod, hg3] at ha4
        omega
      · rw [hXfac, Nat.mul_mod, hg3] at hX4
        omega
      · rw [hyfac, Nat.mul_mod, hg3] at hy4
        omega
  have hbase :
      jacobiSym (X' : Int) Y =
        jacobiSym b a' * jacobiSym (x : Int) y' := by
    rcases hgCase with hcase | hcase
    · rcases hcase with ⟨_, ha'4, hX'4, hy'4⟩
      calc
        jacobiSym (X' : Int) Y =
            jacobiSym (Y : Int) X' :=
          jacobiSym.quadratic_reciprocity_one_mod_four
            hX'4 hYOdd
        _ = jacobiSym (a' : Int) X' *
            jacobiSym (y' : Int) X' := hleftSolved
        _ = jacobiSym (X' : Int) a' *
            jacobiSym (X' : Int) y' := by
              rw [jacobiSym.quadratic_reciprocity_one_mod_four
                    ha'4 hX'Odd,
                ← jacobiSym.quadratic_reciprocity_one_mod_four
                    hX'4 hy'Odd]
        _ = jacobiSym (X' : Int) a' *
            (jacobiSym (a' : Int) y' *
              jacobiSym (x : Int) y') := by rw [hXy]
        _ = (jacobiSym (X' : Int) a' *
              jacobiSym (y' : Int) a') *
            jacobiSym (x : Int) y' := by
              rw [jacobiSym.quadratic_reciprocity_one_mod_four
                    ha'4 hy'Odd]
              ring
        _ = jacobiSym b a' * jacobiSym (x : Int) y' := by
          rw [hcoeff]
    · rcases hcase with ⟨_, ha'4, hX'4, hy'4⟩
      have hswapXY :=
        jacobiSym.quadratic_reciprocity_three_mod_four
          hX'4 hY4
      calc
        jacobiSym (X' : Int) Y =
            -jacobiSym (Y : Int) X' := hswapXY
        _ = -(jacobiSym (a' : Int) X' *
            jacobiSym (y' : Int) X') := by rw [hleftSolved]
        _ = jacobiSym (X' : Int) a' *
            jacobiSym (y' : Int) X' := by
              rw [jacobiSym.quadratic_reciprocity_three_mod_four
                    ha'4 hX'4]
              ring
        _ = jacobiSym (X' : Int) a' *
            jacobiSym (X' : Int) y' := by
              rw [jacobiSym.quadratic_reciprocity_one_mod_four
                    hy'4 hX'Odd]
        _ = jacobiSym (X' : Int) a' *
            (jacobiSym (a' : Int) y' *
              jacobiSym (x : Int) y') := by rw [hXy]
        _ = (jacobiSym (X' : Int) a' *
              jacobiSym (y' : Int) a') *
            jacobiSym (x : Int) y' := by
              rw [← jacobiSym.quadratic_reciprocity_one_mod_four
                    hy'4 ha'Odd]
              ring
        _ = jacobiSym b a' * jacobiSym (x : Int) y' := by
          rw [hcoeff]
  have hYmodG :
      Int.ModEq g (Y : Int) (c * x) := by
    rw [Int.modEq_iff_dvd]
    use -(d * (y' : Int))
    have hyfacInt : (y : Int) = (g : Int) * y' := by
      exact_mod_cast hyfac
    rw [hforwardY, hyfacInt]
    ring
  have hbcmod :
      Int.ModEq g (b * c) (-1) := by
    rw [Int.modEq_iff_dvd]
    use -((a' : Int) * d)
    have hafacInt : (a : Int) = (g : Int) * a' := by
      exact_mod_cast hafac
    rw [hafacInt] at hdet
    linear_combination hdet
  have hcG :
      jacobiSym c g =
        jacobiSym (-1 : Int) g * jacobiSym b g := by
    have hs := jacobiSym.mod_left' hbcmod
    rw [jacobiSym.mul_left] at hs
    have hbSq := jacobiSym.sq_one hbgInt
    calc
      jacobiSym c g =
          jacobiSym b g ^ 2 * jacobiSym c g := by
            rw [hbSq, one_mul]
      _ = jacobiSym b g *
          (jacobiSym b g * jacobiSym c g) := by ring
      _ = jacobiSym b g * jacobiSym (-1 : Int) g := by rw [hs]
      _ = jacobiSym (-1 : Int) g * jacobiSym b g := by ring
  have hcorr :
      jacobiSym (g : Int) Y =
        jacobiSym b g * jacobiSym (x : Int) g := by
    have hYG :
        jacobiSym (Y : Int) g =
          jacobiSym c g * jacobiSym (x : Int) g := by
      calc
        jacobiSym (Y : Int) g =
            jacobiSym (c * x) g :=
          jacobiSym.mod_left' hYmodG.eq
        _ = jacobiSym c g * jacobiSym (x : Int) g := by
          rw [jacobiSym.mul_left]
    rcases hgCase with hcase | hcase
    · rcases hcase with ⟨hg4, _, _, _⟩
      rw [jacobiSym.quadratic_reciprocity_one_mod_four
            hg4 hYOdd,
        hYG, hcG, jacobiSym.at_neg_one hgOdd,
        ZMod.χ₄_nat_one_mod_four hg4, one_mul]
    · rcases hcase with ⟨hg4, _, _, _⟩
      have hswap :=
        jacobiSym.quadratic_reciprocity_three_mod_four
          hg4 hY4
      rw [hYG, hcG, jacobiSym.at_neg_one hgOdd,
        ZMod.χ₄_nat_three_mod_four hg4, neg_one_mul] at hswap
      linarith
  have hg_ne : g ≠ 0 := hgpos.ne'
  have ha'_ne : a' ≠ 0 := ha'Odd.pos.ne'
  have hy'_ne : y' ≠ 0 := hy'Odd.pos.ne'
  calc
    jacobiSym (X : Int) Y =
        jacobiSym (g : Int) Y * jacobiSym (X' : Int) Y := by
          rw [hXfac, Nat.cast_mul, jacobiSym.mul_left]
    _ = (jacobiSym b g * jacobiSym (x : Int) g) *
          (jacobiSym b a' * jacobiSym (x : Int) y') := by
            rw [hcorr, hbase]
    _ = (jacobiSym b g * jacobiSym b a') *
          (jacobiSym (x : Int) g * jacobiSym (x : Int) y') := by
            ring
    _ = jacobiSym b a * jacobiSym (x : Int) y := by
      rw [hafac, hyfac,
        jacobiSym.mul_right' b hg_ne ha'_ne,
        jacobiSym.mul_right' (x : Int) hg_ne hy'_ne]

private theorem outer17_top_jacobi (k : Nat) :
    jacobiSym (outer17P6 k : Int) (outer17P7 k) =
      -jacobiSym (outer17P1 k : Int) (outer17P2 k) := by
  rcases outer17_top_matrix_identities k with ⟨hX, hY, hdet⟩
  rcases outer17P_mod_eight k with
    ⟨_, hP1, hP2, _, _, _, hP6, hP7, _, _, _, _, _, _, _⟩
  rcases outer17_top_coefficient_moduli k with ⟨hA4, _, _, _⟩
  have hP14 : outer17P1 k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P1 k) (by decide : 4 ∣ 8)
    rw [hP1] at hm
    omega
  have hP24 : outer17P2 k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P2 k) (by decide : 4 ∣ 8)
    rw [hP2] at hm
    omega
  have hP64 : outer17P6 k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P6 k) (by decide : 4 ∣ 8)
    rw [hP6] at hm
    omega
  have hP74 : outer17P7 k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P7 k) (by decide : 4 ∣ 8)
    rw [hP7] at hm
    omega
  have htransfer :=
    outer17_top_unimodular_transfer hA4 hP64 hP14 hP74 hP24
      (b := -(outer17TopBeta k : Int))
      (c := outer17TopLowerLeft k) (d := outer17TopLowerRight k)
      (by rw [hX]; ring) hY hdet
  rw [htransfer, outer17_top_multiplier k]
  ring

private theorem outer17_main_jacobi (k : Nat) :
    jacobiSym (outer17P1 k : Int) (outer17P0 k) = -1 := by
  rcases outer17_pseudo_remainders (outer17A k) with
    ⟨hfirst, _, _, _, _, _, _, _, _, hlast, _, _, _, _⟩
  rcases outer17P_casts k with
    ⟨h0, h1, h2, _, _, _, _, _, _, h9, h10, h11, _, _, _⟩
  rcases outer17P_mod_eight k with
    ⟨hP0, hP1, hP2, _, _, _, _, _, _, _, hP10, _,
      _, _, _⟩
  have hP04 : outer17P0 k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P0 k) (by decide : 4 ∣ 8)
    rw [hP0] at hm
    omega
  have hP14 : outer17P1 k % 4 = 1 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P1 k) (by decide : 4 ∣ 8)
    rw [hP1] at hm
    omega
  have hP24 : outer17P2 k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P2 k) (by decide : 4 ∣ 8)
    rw [hP2] at hm
    omega
  have hP104 : outer17P10 k % 4 = 3 := by
    have hm :=
      Nat.mod_mod_of_dvd (outer17P10 k) (by decide : 4 ∣ 8)
    rw [hP10] at hm
    omega
  have hP0Odd : Odd (outer17P0 k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_one hP04)
  have hP2Odd : Odd (outer17P2 k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hP24)
  have hP10Odd : Odd (outer17P10 k) :=
    (Nat.odd_iff).mpr (Nat.odd_of_mod_four_eq_three hP104)
  have hfirstInt :
      (outer17P0 k : Int) =
        (4 * outer17A k ^ 3 + 5 * outer17A k) *
            outer17P1 k +
          outer17P2 k := by
    rw [h0, h1, h2]
    exact hfirst
  have hlastInt :
      4 * (outer17P9 k : Int) =
        (8 * outer17A k - 9) * outer17P10 k -
          outer17P11 k := by
    rw [h9, h10, h11]
    exact hlast
  have hfirstMod :
      (outer17P0 k : Int) ≡ (outer17P2 k : Int)
        [ZMOD (outer17P1 k : Int)] := by
    apply Int.modEq_of_dvd
    use -(4 * outer17A k ^ 3 + 5 * outer17A k)
    linear_combination -hfirstInt
  have hlastMod :
      (4 * (outer17P9 k : Int)) ≡ -(outer17P11 k : Int)
        [ZMOD (outer17P10 k : Int)] := by
    apply Int.modEq_of_dvd
    use -(8 * outer17A k - 9)
    linear_combination -hlastInt
  have hstart :
      jacobiSym (outer17P1 k : Int) (outer17P0 k) =
        jacobiSym (outer17P1 k : Int) (outer17P2 k) := by
    calc
      jacobiSym (outer17P1 k : Int) (outer17P0 k) =
          jacobiSym (outer17P0 k : Int) (outer17P1 k) :=
        jacobiSym.quadratic_reciprocity_one_mod_four
          hP14 hP0Odd
      _ = jacobiSym (outer17P2 k : Int) (outer17P1 k) :=
        jacobiSym.mod_left' hfirstMod.eq
      _ = jacobiSym (outer17P1 k : Int) (outer17P2 k) :=
        jacobiSym.quadratic_reciprocity_one_mod_four'
          hP2Odd hP14
  have hP9P10 :
      jacobiSym (outer17P9 k : Int) (outer17P10 k) = -1 := by
    calc
      jacobiSym (outer17P9 k : Int) (outer17P10 k) =
          jacobiSym (4 * (outer17P9 k : Int))
            (outer17P10 k) := by
              symm
              rw [jacobiSym.mul_left,
                jacobiSym.at_four hP10Odd, one_mul]
      _ = jacobiSym (-(outer17P11 k : Int))
            (outer17P10 k) :=
        jacobiSym.mod_left' hlastMod.eq
      _ = -jacobiSym (outer17P11 k : Int)
            (outer17P10 k) := by
        rw [jacobiSym.neg _ hP10Odd,
          ZMod.χ₄_nat_three_mod_four hP104, neg_one_mul]
      _ = -1 := by rw [outer17_bottom_jacobi k]
  have hP6P7 :
      jacobiSym (outer17P6 k : Int) (outer17P7 k) = 1 := by
    rw [outer17_middle_jacobi k, hP9P10]
    norm_num
  have hP1P2 :
      jacobiSym (outer17P1 k : Int) (outer17P2 k) = -1 := by
    have htop := outer17_top_jacobi k
    rw [hP6P7] at htop
    linarith
  rw [hstart, hP1P2]

/-- The degree-`17` intermediate real coordinate cannot be one more than a
square in the source-forced residue class `A = 2 mod 8`. -/
theorem no_sm2LucasReal_seventeen_square_of_mod_eight_two
    {A y : Nat}
    (hA : A % 8 = 2)
    (hreal : sm2LucasReal A 17 = y ^ 2 + 1) :
    False := by
  let k := A / 8
  have hAk : A = outer17NatA k := by
    dsimp [k, outer17NatA]
    have hdiv := Nat.mod_add_div A 8
    omega
  rw [hAk] at hreal
  have hpolyInt :
      (sm2LucasReal (outer17NatA k) 17 : Int) =
        (outer17P0 k : Int) + 1 := by
    rcases outer17P_casts k with ⟨h0, _⟩
    rw [h0]
    simp only [sm2LucasReal, outer17NatA, outer17A, outer17R0]
    push_cast
    ring
  have hpoly :
      sm2LucasReal (outer17NatA k) 17 = outer17P0 k + 1 := by
    exact_mod_cast hpolyInt
  have hsquare : outer17P0 k = y ^ 2 := by
    omega
  have hj := outer17_main_jacobi k
  rw [hsquare, jacobiSym.pow_right] at hj
  rcases jacobiSym.trichotomy (outer17P1 k : Int) y with
    hzero | hone | hneg
  · rw [hzero] at hj
    norm_num at hj
  · rw [hone] at hj
    norm_num at hj
  · rw [hneg] at hj
    norm_num at hj

/-- Every complete outer-`17` source packet is impossible. -/
theorem noSm2OuterSeventeenBlocks :
    NoSm2OuterSeventeenBlocks := by
  intro data allocation generator packet
  rcases packet.2 with
    ⟨m, A, B, hmPos, hmOdd, hmEight, hAEight, hANine,
      hphase, hclasses, hmFactor, hBdef, hcoords, hnegative,
      hkernel, hsource, hreal, hsuccessor, hD17, hK17,
      hR17, hy17, hz17, hQ17, hB17, hV17⟩
  exact
    no_sm2LucasReal_seventeen_square_of_mod_eight_two
      hAEight hreal

end Erdos364
