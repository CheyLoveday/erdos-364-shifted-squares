import Erdos364.DicksonLucas.ShiftedSquarePropagation

/-!
# Paper-strength statement bridge for Paper I (independent audit, member m5)

The maintained development in `Erdos364/SquareMiddle` and
`Erdos364/DicksonLucas/ShiftedSquarePropagation.lean` states its results for
*natural* square roots (`y : Nat`) and for natural differences
`sm2LucasReal A N - 1`.  Paper I states the same results for `y ∈ ℤ`, for the
integer square "`F_N(A) - 1` is a square", and writes the Pell corollary in a
quadratic ring.

This file closes that statement-level gap *inside Lean*: every theorem below
is the paper's printed statement at its stated quantifier strength, and each
is derived, with no extra hypothesis and no extra axiom, from the maintained
declarations.  It is a statement audit, not a new proof of the mathematics:
nothing here proves the fixed-index obstruction itself.

Everything in this file is proved from the kernel-checked maintained theorems;
the axiom footprints are printed at the end.
-/

namespace Erdos364

namespace StatementAudit

/-! ## The recurrence of (1.1) is the maintained recurrence -/

/-- (1.1), initial value `F_0(A) = 1`. -/
theorem paper_F_zero (A : Nat) : sm2LucasReal A 0 = 1 := rfl

/-- (1.1), initial value `F_1(A) = A`. -/
theorem paper_F_one (A : Nat) : sm2LucasReal A 1 = A := rfl

/-- (1.1), the recursion, with the paper's parameter `A`. -/
theorem paper_F_step (A n : Nat) :
    sm2LucasReal A (n + 2) = 2 * A * sm2LucasReal A (n + 1) + sm2LucasReal A n :=
  sm2LucasReal_succ_succ A n

/-! ## Natural squares versus integer squares

Paper I quantifies `y ∈ ℤ`; the maintained theorems quantify `y : Nat`.
An integer square is the square of the absolute value, so the two forms are
interderivable.  These two lemmas carry that transfer and nothing else. -/

/-- `n = y^2 + 1` with `y : ℤ` forces `n = z^2 + 1` with `z : Nat`. -/
theorem nat_of_int_square_add_one {n : Nat} {y : Int}
    (h : (n : Int) = y ^ 2 + 1) : ∃ z : Nat, n = z ^ 2 + 1 := by
  set k := y.natAbs with hk
  have hcases : y = (k : Int) ∨ y = -(k : Int) := by
    rw [hk]
    exact Int.natAbs_eq y
  refine ⟨k, ?_⟩
  rcases hcases with hy | hy
  · have hboth : (n : Int) = ((k : Nat) : Int) ^ 2 + 1 := by
      rw [h, hy]
    exact_mod_cast hboth
  · have hboth : (n : Int) = ((k : Nat) : Int) ^ 2 + 1 := by
      rw [h, hy]
      ring
    exact_mod_cast hboth

/-- `x = y^2 + 1` with `x, y : ℤ` writes `x` as a natural square plus one. -/
theorem int_square_add_one_to_nat {x y : Int} (h : x = y ^ 2 + 1) :
    ∃ z : Nat, x = ((z ^ 2 + 1 : Nat) : Int) := by
  set k := y.natAbs with hk
  have hcases : y = (k : Int) ∨ y = -(k : Int) := by
    rw [hk]
    exact Int.natAbs_eq y
  refine ⟨k, ?_⟩
  rcases hcases with hy | hy
  · rw [h, hy]
    push_cast
    ring
  · rw [h, hy]
    push_cast
    ring

/-- `2 ∣ N` as a natural divisibility statement gives `Even N`. -/
theorem even_of_two_dvd {N : Nat} (h : 2 ∣ N) : Even N := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, by ring⟩

/-! ## Theorem 1.1 (index-divisibility obstruction), paper strength

Paper: for `A ∈ ℤ≥0` with `A ≡ 2 (mod 4)` and `N > 0` with `17 ∣ N` or
`41 ∣ N`, there is no `y ∈ ℤ` with `F_N(A) = y^2 + 1`. -/

theorem theorem_1_1 (A N : Nat) (hA : A % 4 = 2) (hNpos : 0 < N)
    (hfactor : 17 ∣ N ∨ 41 ∣ N) :
    ∀ y : Int, (sm2LucasReal A N : Int) ≠ y ^ 2 + 1 := by
  intro y h
  obtain ⟨z, hz⟩ := nat_of_int_square_add_one h
  exact
    no_sm2LucasReal_shiftedSquare_of_positive_index_factor
      hA hNpos hfactor hz

/-! ## Theorem 1.2 (fixed indices), paper strength -/

theorem theorem_1_2_seventeen (A : Nat) (hA : A % 4 = 2) :
    ∀ y : Int, (sm2LucasReal A 17 : Int) ≠ y ^ 2 + 1 := by
  intro y h
  obtain ⟨z, hz⟩ := nat_of_int_square_add_one h
  exact no_sm2LucasReal_seventeen_square_of_mod_four_two hA hz

theorem theorem_1_2_fortyOne (A : Nat) (hA : A % 4 = 2) :
    ∀ y : Int, (sm2LucasReal A 41 : Int) ≠ y ^ 2 + 1 := by
  intro y h
  obtain ⟨z, hz⟩ := nat_of_int_square_add_one h
  exact no_sm2LucasReal_fortyOne_square_of_mod_four_two hA hz

/-! ## Theorem 1.3 (exact even-index valuation), paper strength

Paper: `v_2(F_N(A) - 1) = 2 v_2(N) + 1` for every positive even `N`.  In
`Nat`, `padicValNat 2 (sm2LucasReal A N - 1)` is the paper's `v_2` of the
positive integer `F_N(A) - 1`; the positivity is part of the statement below. -/

theorem theorem_1_3 (A N : Nat) (hA : A % 4 = 2) (hNpos : 0 < N)
    (hNeven : Even N) :
    padicValNat 2 (sm2LucasReal A N - 1) = 2 * padicValNat 2 N + 1 :=
  sm2LucasReal_sub_one_padicVal_two_of_positive_even hA hNpos hNeven

/-- The consequence the paper draws from Theorem 1.3 at paper strength. -/
theorem even_index_exclusion (A N : Nat) (hA : A % 4 = 2) (hNpos : 0 < N)
    (hNeven : Even N) :
    ∀ y : Int, (sm2LucasReal A N : Int) ≠ y ^ 2 + 1 := by
  intro y h
  obtain ⟨z, hz⟩ := nat_of_int_square_add_one h
  exact no_sm2LucasReal_shiftedSquare_of_positive_even_index hA hNpos hNeven hz

/-! ## Corollary 1.4 (negative-Pell formulation), paper strength

Paper: `K, u, v ∈ ℤ≥0`, `u^2 + 1 = K v^2`, `u ≡ 2 (mod 4)`; write
`(u + v√K)^N = X_N + Y_N√K` in `ℤ[√K]`.  If `N > 0` and one of `2 ∣ N`,
`17 ∣ N`, `41 ∣ N` holds then `X_N - 1` is not a square.

`ℤ√(K : Int)` is Mathlib's ring with basis `1, √K` and multiplication rule
`√K · √K = K`, whose coordinates `re`, `im` are precisely the paper's
`X_N`, `Y_N`.  So `(...).re` below *is* `X_N`; nothing is assumed about
squarefreeness of `K` or fundamentality of the unit. -/

theorem corollary_1_4 (K u v N : Nat) (hnegative : u ^ 2 + 1 = K * v ^ 2)
    (hu : u % 4 = 2) (hNpos : 0 < N)
    (hfactor : 2 ∣ N ∨ 17 ∣ N ∨ 41 ∣ N) :
    ∀ y : Int, (((⟨u, v⟩ : ℤ√(K : Int)) ^ N).re - 1) ≠ y ^ 2 := by
  intro y h
  have hre : ((⟨u, v⟩ : ℤ√(K : Int)) ^ N).re = y ^ 2 + 1 := by
    linarith
  obtain ⟨z, hz⟩ := int_square_add_one_to_nat hre
  rcases hfactor with h2 | h17 | h41
  · exact
      normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index
        hnegative hu hNpos (even_of_two_dvd h2) z hz
  · exact
      normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor
        hnegative hu hNpos (Or.inl h17) z hz
  · exact
      normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor
        hnegative hu hNpos (Or.inr h41) z hz

/-! ## The paper's own witnesses that the hypotheses cannot be dropped

These are the paper's stated counterexamples (§1.1, §5.2); they are stated
here at the paper's strength so that the boundary of Theorems 1.1–1.3 is
machine-checked too. -/

/-- §1.1: at `A = 2` and `N = 1` the shifted value *is* a square, so no
exclusion can hold without a condition on `N`. -/
theorem witness_index_one :
    (sm2LucasReal 2 1 : Int) = ((1 : Nat) : Int) ^ 2 + 1 := by decide

/-- §5.2: the parity guard in Lemma 5.1 is essential; `F_4(2) = 161` whereas
`F_2(F_2(2)) = 163`. -/
theorem witness_even_inner_composition :
    sm2LucasReal 2 4 ≠ sm2LucasReal (sm2LucasReal 2 2) 2 := by decide

/-! ## Theorem 4.2 (hard fixed-index phase), paper strength

Paper: for `p ∈ {17, 41}` and `A ≡ 2 (mod 8)`, `F_p(A) ≠ y^2 + 1` for
`y ∈ ℤ`.  The maintained statements are at `A % 8 = 2`; the statements below
add only the integer-square transfer.  Note that `A = 2` *is* an instance of
`A % 8 = 2`, so the formal statement of the degree-41 theorem covers the
endpoint that the published proof route dispatches separately. -/

theorem theorem_4_2_seventeen (A : Nat) (hA : A % 8 = 2) :
    ∀ y : Int, (sm2LucasReal A 17 : Int) ≠ y ^ 2 + 1 := by
  intro y h
  obtain ⟨z, hz⟩ := nat_of_int_square_add_one h
  exact no_sm2LucasReal_seventeen_square_of_mod_eight_two hA hz

theorem theorem_4_2_fortyOne (A : Nat) (hA : A % 8 = 2) :
    ∀ y : Int, (sm2LucasReal A 41 : Int) ≠ y ^ 2 + 1 := by
  intro y h
  obtain ⟨z, hz⟩ := nat_of_int_square_add_one h
  exact ss41_shiftedSquare_impossible hA hz

/-- The `A = 2` boundary is inside the degree-41 statement (it is
`2 % 8 = 2`); the paper proves it by a separate modulo-23 argument. -/
theorem endpoint_fortyOne_included :
    ∀ y : Int, (sm2LucasReal 2 41 : Int) ≠ y ^ 2 + 1 :=
  theorem_4_2_fortyOne 2 (by decide)

/-- The modulo-23 witness the paper uses for that boundary:
`F_41(2) - 1 ≡ 20 (mod 23)`. -/
theorem endpoint_fortyOne_residue : (sm2LucasReal 2 41 - 1) % 23 = 20 := by
  decide

/-- And `20` is a quadratic nonresidue modulo `23`, which is what makes the
residue in `endpoint_fortyOne_residue` an obstruction. -/
theorem endpoint_twenty_is_nonresidue :
    ∀ y : ZMod 23, (y : ZMod 23) ^ 2 ≠ 20 := by decide

/-- The same obstruction as a pure integer statement: no natural square is
congruent to `20` modulo `23`.  Combined with `endpoint_fortyOne_residue`
this is the paper's boundary argument. -/
theorem endpoint_fortyOne_mod23_obstruction (y : Nat) : (y ^ 2) % 23 ≠ 20 := by
  intro h
  have hcast : ((y : ZMod 23)) ^ 2 = 20 := by
    have h1 : ((y ^ 2 : Nat) : ZMod 23) = 20 :=
      (ZMod.natCast_eq_natCast_iff' (y ^ 2) 20 23).mpr (by simpa using h)
    simpa using h1
  exact endpoint_twenty_is_nonresidue (y : ZMod 23) hcast

/-! ## Axiom footprint of everything used above -/

#print axioms theorem_1_1
#print axioms theorem_1_2_seventeen
#print axioms theorem_1_2_fortyOne
#print axioms theorem_1_3
#print axioms even_index_exclusion
#print axioms corollary_1_4
#print axioms no_sm2LucasReal_shiftedSquare_of_positive_index_factor
#print axioms no_sm2LucasReal_seventeen_square_of_mod_four_two
#print axioms no_sm2LucasReal_fortyOne_square_of_mod_four_two
#print axioms sm2UpperNegativeUnit_pow_re
#print axioms theorem_4_2_seventeen
#print axioms theorem_4_2_fortyOne
#print axioms endpoint_fortyOne_residue
#print axioms endpoint_twenty_is_nonresidue

end StatementAudit

end Erdos364
