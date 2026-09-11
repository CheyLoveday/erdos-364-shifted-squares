import Erdos364.Foundations.SquarefreeKernel

namespace Erdos364

/-- A positive powerful natural has a unique pair `(squareFactor, kernel)` in
the repository's `A²D³` normal form. -/
theorem existsUnique_squareCubeNormalForm_of_powerfulPos {n : Nat}
    (hpowerful : PowerfulPos n) :
    ∃! data : Nat × Nat,
      SquareCubeNormalForm n data.1 data.2 := by
  obtain ⟨a, D, hform⟩ := exists_squareCubeNormalForm_of_powerfulPos hpowerful
  refine ⟨(a, D), hform, ?_⟩
  rintro ⟨b, E⟩ hother
  have hunique :=
    squareCubeNormalForm_pair_unique hpowerful.1 hform hother
  rcases hunique with ⟨rfl, rfl⟩
  rfl

/-- Fully packaged existence-and-uniqueness interface for the canonical
`A²D³` representation. -/
theorem powerfulPos_iff_existsUnique_squareCubeNormalForm (n : Nat) :
    PowerfulPos n ↔
      ∃! data : Nat × Nat,
        SquareCubeNormalForm n data.1 data.2 := by
  constructor
  · exact existsUnique_squareCubeNormalForm_of_powerfulPos
  · rintro ⟨data, hform, _hunique⟩
    exact powerfulPos_of_squareCubeNormalForm hform

end Erdos364
