import ControlEquations.CtrlUnique
import ControlEquations.CtrlCentralImage

/-!
# Axiom audit: entailment and uniqueness

This file contains no theorems.  It prints the axiom dependencies of the entailment and
uniqueness results, and of the two partial triviality results for central control.  Each should
depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

open Crops.Ctrl

#print axioms Crops.Ctrl.all_iff_forall_cell
#print axioms Crops.Ctrl.Entails.mem_of_witness
#print axioms Crops.Ctrl.EntailsRev.mem_of_witness
#print axioms Crops.Ctrl.Entails.six_subset
#print axioms Crops.Ctrl.EntailsRev.five_subset
#print axioms Crops.Ctrl.entails_seven
#print axioms Crops.Ctrl.entailsRev_six
#print axioms Crops.Ctrl.entailing_subsets_pinned
#print axioms Crops.Ctrl.entailing_subsets_pinned_reversible
#print axioms Crops.Ctrl.unique_minimal_presentation_of_eqC_independent
#print axioms Crops.Ctrl.unique_minimal_presentation_of_eqC_derivable
#print axioms Crops.Ctrl.minimal_presentation_unique
#print axioms Crops.Ctrl.minimal_presentation_unique_reversible
#print axioms Crops.Ctrl.xw_invol
#print axioms Crops.Ctrl.left_pad_trivial_of_central_control
#print axioms Crops.Ctrl.right_pad_one_trivial_of_left
#print axioms Crops.Ctrl.right_pad_trivial_of_left
#print axioms Crops.Ctrl.central_control_image_padding_trivial
