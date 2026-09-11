import Erdos364.Foundations.TripleNormalForm

namespace Erdos364

/-- A powerful triple bundled with exact normal-form coordinates at the same input index. -/
structure PowerfulTripleCandidateAt (n : Nat) where
  source : PowerfulTripleAt n
  normalForm : TripleNormalFormAt n

/-- Every powerful triple admits an indexed candidate without selecting a global normalizer. -/
theorem PowerfulTripleAt.exists_candidate {n : Nat}
    (htriple : PowerfulTripleAt n) :
    Nonempty (PowerfulTripleCandidateAt n) := by
  obtain ⟨normalForm⟩ := htriple.exists_tripleNormalFormAt
  exact ⟨⟨htriple, normalForm⟩⟩

/-- A candidate reconstructs the exact three values from its preserved coordinates. -/
theorem PowerfulTripleCandidateAt.reconstruct {n : Nat}
    (candidate : PowerfulTripleCandidateAt n) :
    candidate.normalForm.a0 ^ 2 * candidate.normalForm.b0 ^ 3 = n ∧
      candidate.normalForm.a1 ^ 2 * candidate.normalForm.b1 ^ 3 = n + 1 ∧
        candidate.normalForm.a2 ^ 2 * candidate.normalForm.b2 ^ 3 = n + 2 := by
  exact candidate.normalForm.reconstruct

end Erdos364
