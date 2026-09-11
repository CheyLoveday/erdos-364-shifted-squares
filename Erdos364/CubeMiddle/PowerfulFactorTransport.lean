import Erdos364.Foundations.PowerfulFactorTransport

namespace Erdos364

/-- A number containing exactly one factor of `3` cannot be powerful. -/
theorem not_powerfulPos_of_three_dvd_not_nine {B : Nat}
    (h3B : 3 ∣ B)
    (h9B : ¬ 9 ∣ B) :
    ¬ PowerfulPos B := by
  intro hB
  apply h9B
  simpa using hB.2 3 Nat.prime_three h3B

/-- Normalize a gcd-`3` pair whose right factor contains exactly one `3`.
Transfer the unique factor `3` from the right factor into the left factor,
mapping `(A, 3 * C)` to `(3 * A, C)` with the same product. -/
theorem normalized_coprime_factors_of_gcd_three {A B : Nat}
    (hgcd : Nat.gcd A B = 3)
    (h3B : 3 ∣ B)
    (h9B : ¬ 9 ∣ B) :
    ∃ C : Nat,
      B = 3 * C ∧
        Nat.Coprime (3 * A) C := by
  obtain ⟨C, hB⟩ := h3B
  have h3C : ¬ 3 ∣ C := by
    rintro ⟨k, hk⟩
    apply h9B
    refine ⟨k, ?_⟩
    rw [hB, hk]
    ring
  have hAC : Nat.Coprime A C := by
    have hdA := Nat.gcd_dvd_left A C
    have hdC := Nat.gcd_dvd_right A C
    have hC_dvd_B : C ∣ B := ⟨3, by rw [hB]; ring⟩
    have hdB : Nat.gcd A C ∣ B := dvd_trans hdC hC_dvd_B
    have hd3 : Nat.gcd A C ∣ 3 := by
      rw [← hgcd]
      exact Nat.dvd_gcd hdA hdB
    have hle := Nat.le_of_dvd (by norm_num : 0 < 3) hd3
    rcases (by omega : Nat.gcd A C = 0 ∨ Nat.gcd A C = 1 ∨
        Nat.gcd A C = 2 ∨ Nat.gcd A C = 3) with hg | hg | hg | hg
    · obtain ⟨k, hk⟩ := hd3
      rw [hg] at hk
      omega
    · exact hg
    · obtain ⟨k, hk⟩ := hd3
      rw [hg] at hk
      omega
    · exfalso
      rw [hg] at hdC
      exact h3C hdC
  have h3copC : Nat.Coprime 3 C :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr h3C
  have hnormalized_coprime : Nat.Coprime (3 * A) C :=
    Nat.Coprime.mul_left h3copC hAC
  exact ⟨C, hB, hnormalized_coprime⟩

/-- If the original gcd-`3` product is powerful, both normalized coprime factors are powerful. -/
theorem powerfulPos_normalized_factors_of_gcd_three {A B : Nat}
    (hgcd : Nat.gcd A B = 3)
    (h3B : 3 ∣ B)
    (h9B : ¬ 9 ∣ B)
    (hAB : PowerfulPos (A * B)) :
    ∃ C : Nat,
      B = 3 * C ∧
        Nat.Coprime (3 * A) C ∧
          PowerfulPos (3 * A) ∧ PowerfulPos C := by
  obtain ⟨C, hB, hnormalized_coprime⟩ :=
    normalized_coprime_factors_of_gcd_three hgcd h3B h9B
  have hproduct : (3 * A) * C = A * B := by
    rw [hB]
    ring
  have hnormalized_powerful : PowerfulPos ((3 * A) * C) := by
    rw [hproduct]
    exact hAB
  obtain ⟨hleft, hright⟩ :=
    powerfulPos_factors_of_coprime_mul
      hnormalized_coprime hnormalized_powerful
  exact ⟨C, hB, hnormalized_coprime, hleft, hright⟩

end Erdos364
