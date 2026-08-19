import ControlEquations.CtrlMinimal
import ControlEquations.CtrlTwist

/-!
# Axiom audit: the model separating (h), and the irredundancy statements

This file contains no theorems.  It prints the axiom dependencies of the crop separating their
(h) from the other seven equations, and of the irredundancy statements assembled from it.  Each
should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Crops

open Ctrl

-- the model of seven equations failing (h), and its ingredients
#print axioms Sm.smData_EqA
#print axioms Sm.smData_EqB
#print axioms Sm.smData_EqC
#print axioms Sm.smData_EqD
#print axioms Sm.smData_EqE
#print axioms Sm.smData_EqF
#print axioms Sm.smData_EqG
#print axioms Sm.smData_not_EqH
#print axioms Sm.Ctrl.eqH_not_derivable_from_seven

-- the blindness theorem for (c)
#print axioms Ctrl.eqC_of_trivial_symmetry

-- how short the list can be made, and how much of that is sharp
#print axioms Ctrl.sevenSuffice
#print axioms Ctrl.sixSufficeReversible
#print axioms Ctrl.sixCellsIndependent
#print axioms Ctrl.fiveCellsIndependentReversible
#print axioms Ctrl.eqF_derivable_reversible
#print axioms Ctrl.smCrop_reversible
#print axioms Ctrl.gradedData_reversible

-- the reduction of (c) to a central character
#print axioms Ctrl.twist_is_eqC_witness

end Crops
