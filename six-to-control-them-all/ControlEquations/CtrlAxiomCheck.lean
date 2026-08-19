import ControlEquations.CtrlModels
import ControlEquations.CtrlInv
import ControlEquations.CtrlSigned
import ControlEquations.CtrlComm

/-!
# Axiom audit: the models and the two restricted derivations

This file contains no theorems.  It prints the axiom dependencies of the derivations of their
(b) and of their (f) on invertible arguments, of the five separating models, and of the
blindness results for their (c) and (h).  Each should depend only on `propext`,
`Classical.choice` and `Quot.sound`: no `sorry`, no added axiom, no `native_decide`.
-/

namespace Crops

namespace Ctrl

-- the derivation: their (b) follows from their (a) and (e)
#print axioms eqB_of_eqA_eqE

-- their (f) follows from (a), (b), (d), (e) on invertible morphisms
#print axioms eqF_of_invertible
#print axioms eqB_and_eqF_of_groupoid

-- consistency: a crop with control data satisfying all eight
#print axioms allEight_model

-- the five independence models
#print axioms eqA_independent
#print axioms eqD_independent
#print axioms eqE_independent
#print axioms eqF_independent
#print axioms eqG_independent

-- the blindness theorems for the two open cells
#print axioms eqH_of_trivial_symmetry
#print axioms eqC_of_finite_graded
#print axioms eqC_of_graded
#print axioms SignedData.signed_alx_eq_one
#print axioms SignedData.eqC_of_signed
#print axioms SignedData.eqH_of_signed
#print axioms SignedData.sigNontriv_symmetry_nontrivial

-- the general obstruction
#print axioms invol_tens_trivial_of_symmetric

end Ctrl

end Crops
