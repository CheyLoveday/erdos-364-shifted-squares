import Erdos364.Foundations.PowerfulTriple

namespace Erdos364

/-- The square-middle source predicate: the middle is the nontrivial square
`X ^ 2`, and both adjacent terms are positive powerful naturals. -/
def SquareMiddle (X : Nat) : Prop :=
  1 < X ∧ PowerfulPos (X ^ 2 - 1) ∧ PowerfulPos (X ^ 2 + 1)

/-- Every positive natural square is powerful. -/
theorem powerfulPos_square {X : Nat} (hX : 0 < X) : PowerfulPos (X ^ 2) := by
  refine ⟨pow_pos hX 2, ?_⟩
  intro p hp hp_dvd
  have hpX : p ∣ X := hp.dvd_of_dvd_pow hp_dvd
  obtain ⟨k, rfl⟩ := hpX
  refine ⟨k ^ 2, ?_⟩
  ring

/-- Subtracting and restoring one is exact for a nontrivial natural square. -/
theorem square_sub_one_add_one {X : Nat} (hX : 1 < X) :
    X ^ 2 - 1 + 1 = X ^ 2 := by
  have hX_pos : 0 < X := by omega
  have hsquare_pos : 0 < X ^ 2 := pow_pos hX_pos 2
  omega

/-- Moving two steps from `X ^ 2 - 1` reaches `X ^ 2 + 1` without a
natural-subtraction boundary case. -/
theorem square_sub_one_add_two {X : Nat} (hX : 1 < X) :
    X ^ 2 - 1 + 2 = X ^ 2 + 1 := by
  have hrestore := square_sub_one_add_one hX
  omega

/-- A square-middle source yields the existing consecutive-powerful-triple
source at the exact left index `X ^ 2 - 1`. -/
theorem SquareMiddle.toPowerfulTripleAt {X : Nat} (h : SquareMiddle X) :
    PowerfulTripleAt (X ^ 2 - 1) := by
  rcases h with ⟨hX, hleft, hright⟩
  refine ⟨hleft, ?_, ?_⟩
  · rw [square_sub_one_add_one hX]
    exact powerfulPos_square (by omega)
  · rw [square_sub_one_add_two hX]
    exact hright

/-- Conversely, a consecutive-powerful-triple at the exact square-derived
left index reconstructs the square-middle source. -/
theorem SquareMiddle.ofPowerfulTripleAt {X : Nat} (hX : 1 < X)
    (htriple : PowerfulTripleAt (X ^ 2 - 1)) : SquareMiddle X := by
  refine ⟨hX, htriple.1, ?_⟩
  rw [← square_sub_one_add_two hX]
  exact htriple.2.2

/-- Source-preserving bridge to the repository's established triple
foundation. The positivity hypothesis is retained explicitly on the right. -/
theorem squareMiddle_iff_powerfulTripleAt (X : Nat) :
    SquareMiddle X ↔ 1 < X ∧ PowerfulTripleAt (X ^ 2 - 1) := by
  constructor
  · intro h
    exact ⟨h.1, h.toPowerfulTripleAt⟩
  · rintro ⟨hX, htriple⟩
    exact SquareMiddle.ofPowerfulTripleAt hX htriple

end Erdos364
