import Erdos364.Foundations.PowerfulTripleCandidate

namespace Erdos364

/-- The middle value of the triple starting at `n` is an exact natural cube. -/
def CubeMiddleAt (n : Nat) : Prop :=
  ∃ root : Nat, n + 1 = root ^ 3

/-- The exhaustive tagged root partition, carrying either a cube witness or its negation. -/
inductive MiddleBranchAt (n : Nat) : Type where
  | cube (root : Nat) (middle_eq : n + 1 = root ^ 3)
  | noncube (not_cube : ¬ CubeMiddleAt n)

/-- Split an existing candidate without rebuilding or replacing its normal-form coordinates. -/
noncomputable def PowerfulTripleCandidateAt.rootSplit {n : Nat}
    (candidate : PowerfulTripleCandidateAt n) :
    PowerfulTripleCandidateAt n × MiddleBranchAt n := by
  classical
  by_cases hcube : CubeMiddleAt n
  · exact (candidate, MiddleBranchAt.cube hcube.choose hcube.choose_spec)
  · exact (candidate, MiddleBranchAt.noncube hcube)

/-- The root split preserves its exact source and is exhaustive and disjoint. -/
theorem PowerfulTripleCandidateAt.rootSplit_contract {n : Nat}
    (candidate : PowerfulTripleCandidateAt n) :
    candidate.rootSplit.1 = candidate ∧
      (CubeMiddleAt n ∨ ¬ CubeMiddleAt n) ∧
        ¬ (CubeMiddleAt n ∧ ¬ CubeMiddleAt n) := by
  classical
  constructor
  · by_cases hcube : CubeMiddleAt n <;> simp [PowerfulTripleCandidateAt.rootSplit, hcube]
  · exact
      ⟨Classical.em (CubeMiddleAt n),
        fun hboth => hboth.2 hboth.1⟩

/-- The natural cube witness in the cube branch is unique. -/
theorem cubeMiddleAt_witness_unique {n x y : Nat}
    (hx : n + 1 = x ^ 3)
    (hy : n + 1 = y ^ 3) :
    x = y := by
  have hpowers : x ^ 3 = y ^ 3 := hx.symm.trans hy
  exact Nat.pow_left_injective (by omega) hpowers

end Erdos364
