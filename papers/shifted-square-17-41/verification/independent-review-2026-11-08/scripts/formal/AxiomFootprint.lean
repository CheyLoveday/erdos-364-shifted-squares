import Erdos364.DicksonLucas.ShiftedSquarePropagation
import Erdos364.SquareMiddle.Sm2LowerSquareOuterFortyOne

/-!
# Axiom footprint of the declarations the paper/crosswalk attributes to Lean

By-product of the statement audit (member m5).  The crosswalk
`papers/shifted-square-17-41/theorem-formal-crosswalk.md` attaches a Lean
declaration to each formalised paper result; this file prints the axiom
footprint of every such declaration, so that a reader can see that the
conclusions transported in `PaperStatementBridge.lean` rest on kernel checking
with the standard three axioms only.
-/

#print axioms Erdos364.no_sm2LucasReal_seventeen_square_of_mod_eight_two
#print axioms Erdos364.ss41_shiftedSquare_impossible
#print axioms Erdos364.no_sm2LucasReal_seventeen_square_of_mod_four_two
#print axioms Erdos364.no_sm2LucasReal_fortyOne_square_of_mod_four_two
#print axioms Erdos364.sm2LucasReal_mod_four_two_of_odd
#print axioms Erdos364.sm2LucasReal_mod_eight_six_of_index_mod_four_one
#print axioms Erdos364.sm2LucasReal_mod_eight
#print axioms Erdos364.sm2LucasReal_mul_of_odd_right
#print axioms Erdos364.no_sm2LucasReal_shiftedSquare_of_odd_index_factor
#print axioms Erdos364.sm2LucasReal_sub_one_padicVal_two_of_positive_even
#print axioms Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_even_index
#print axioms Erdos364.no_sm2LucasReal_shiftedSquare_of_positive_index_factor
#print axioms Erdos364.sm2UpperNegativeUnit_pow_re
#print axioms Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_positive_even_index
#print axioms Erdos364.normNegativeOneUnit_real_ne_square_add_one_of_positive_index_factor
#print axioms Erdos364.noSm2OuterSeventeenBlocks
#print axioms Erdos364.no_outerLarge_selected_fortyOne
#print axioms Erdos364.no_rankDefect_selected_fortyOne
#print axioms Erdos364.pellRank_dvd_kernel
