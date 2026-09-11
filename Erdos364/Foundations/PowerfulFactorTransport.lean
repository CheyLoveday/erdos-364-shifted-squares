import Erdos364.Foundations.PowerfulPos

namespace Erdos364

private theorem powerfulPos_left_of_coprime_mul {A B : Nat}
    (hcop : Nat.Coprime A B)
    (hAB : PowerfulPos (A * B)) :
    PowerfulPos A := by
  refine ⟨pos_of_mul_pos_left hAB.1 (Nat.zero_le B), ?_⟩
  intro p hp hpA
  have hp2AB : p ^ 2 ∣ A * B :=
    hAB.2 p hp (dvd_mul_of_dvd_left hpA B)
  have hpB : Nat.Coprime p B :=
    Nat.Coprime.coprime_dvd_left hpA hcop
  exact (Nat.Coprime.pow_left 2 hpB).dvd_mul_right.mp hp2AB

/-- Both coprime factors of a positive powerful product are positive and powerful. -/
theorem powerfulPos_factors_of_coprime_mul {A B : Nat}
    (hcop : Nat.Coprime A B)
    (hAB : PowerfulPos (A * B)) :
    PowerfulPos A ∧ PowerfulPos B := by
  refine ⟨powerfulPos_left_of_coprime_mul hcop hAB, ?_⟩
  exact
    powerfulPos_left_of_coprime_mul hcop.symm
      (by simpa [mul_comm] using hAB)

end Erdos364
