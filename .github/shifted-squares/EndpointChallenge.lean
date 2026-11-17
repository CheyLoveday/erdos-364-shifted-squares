import Mathlib.Algebra.Group.Even

set_option autoImplicit false

namespace Erdos364

/-- The real coordinate of the (n)-th power of (u + sqrt{u^2+1}),
fixed by the initial values and three-term recurrence. -/
def sm2LucasReal (u : Nat) : Nat → Nat
  | 0 => 1
  | 1 => u
  | n + 2 => 2 * u * sm2LucasReal u (n + 1) + sm2LucasReal u n

-- These declarations are statement specifications for the isolated comparator.
theorem no_sm2LucasReal_shiftedSquare_of_positive_even_index
    {A N y : Nat}
    (hA : A % 4 = 2)
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hreal : sm2LucasReal A N = y ^ 2 + 1) :
    False := by sorry

theorem no_sm2LucasReal_shiftedSquare_of_positive_index_factor
    {A N y : Nat}
    (hA : A % 4 = 2)
    (hNpos : 0 < N)
    (hfactor : 17 ∣ N ∨ 41 ∣ N)
    (hreal : sm2LucasReal A N = y ^ 2 + 1) :
    False := by sorry

theorem ss41_shiftedSquare_impossible
    {A y : Nat}
    (hA : A % 8 = 2)
    (hreal : sm2LucasReal A 41 = y ^ 2 + 1) :
    False := by sorry

end Erdos364
