import ControlEquations.CtrlStrengthConseq
import ControlEquations.CtrlOrder
import ControlEquations.CtrlArity

/-!
# Axiom audit: the derivation of (c) and the minimal presentation

This file contains no theorems.  It prints the axiom dependencies of the derivation of their
(c), of the minimal-presentation theorems, and of the results they are combined with.  Each
should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- the derivation of their (c)
#print axioms Crops.Ctrl.eqC_one_of_others
#print axioms Crops.Ctrl.eqC_one
#print axioms Crops.Ctrl.eqC_of_others

-- the consequences
#print axioms Crops.Ctrl.fiveSuffice_eqC
#print axioms Crops.Ctrl.sixSuffice
#print axioms Crops.Ctrl.fiveSufficeReversible
#print axioms Crops.Ctrl.entails_six
#print axioms Crops.Ctrl.entailsRev_five
#print axioms Crops.Ctrl.minimal_presentation_eq_six
#print axioms Crops.Ctrl.minimal_presentation_rev_eq_five
#print axioms Crops.Ctrl.eight_equations_minimal_presentation
#print axioms Crops.Ctrl.central_character_padding_trivial

-- the inputs they rely on
#print axioms Crops.Ctrl.eqB_of_eqA_eqE
#print axioms Crops.Ctrl.Entails.six_subset
#print axioms Crops.Ctrl.EntailsRev.five_subset
#print axioms Crops.Ctrl.sixCellsIndependent
#print axioms Crops.Ctrl.fiveCellsIndependentReversible
#print axioms Crops.Ctrl.unique_minimal_presentation_of_eqC_derivable

-- the arity axis
#print axioms Crops.Ctrl.exists_arity_indistinguishable
#print axioms Crops.Ctrl.no_bounded_arity_characterisation

-- complementarity in the order Figure 1 draws it
#print axioms Crops.Ctrl.eqE_iff_eqE'_of_eqF
#print axioms Crops.Ctrl.eqB_of_eqA_eqE'
#print axioms Crops.Ctrl.invol_tens_trivial_of_symmetric'
