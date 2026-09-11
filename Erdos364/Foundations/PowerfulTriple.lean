import Erdos364.Foundations.PowerfulPos

namespace Erdos364

/-- The exact Erdős 364 source domain: three consecutive positive powerful naturals,
indexed by the left term. -/
def PowerfulTripleAt (n : Nat) : Prop :=
  PowerfulPos n ∧ PowerfulPos (n + 1) ∧ PowerfulPos (n + 2)

end Erdos364
