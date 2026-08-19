import ControlEquations.CtrlModels
import ControlEquations.CtrlInv
import ControlEquations.CtrlSepH
import ControlEquations.CtrlTrivSym

/-!
# Which of the eight equations are irredundant

This file assembles the models and derivations into two statements.

`sevenSuffice` records that seven of the eight imply all eight, since their (b) follows from
their (a) and (e).  `sixCellsIndependent` records that six of those seven are irredundant: for
each of (a), (d), (e), (f), (g) and (h) there is a crop with control data satisfying the other
seven equations and failing that one.  `fiveCellsIndependentReversible` does the same inside the
reversible class, where (f) drops out because it is derivable there.

The remaining cell, their (c), is derived in `ControlEquations.CtrlStrength`, so the two files
together pin the minimal presentation exactly; `ControlEquations.CtrlUnique` does the pinning.

Each witness satisfies all seven of the other equations rather than merely enough to make a
point.  That is what makes the uniqueness argument of `ControlEquations.CtrlUnique` work: a
family of witnesses of that shape forces every entailing sub-list to contain every independent
cell.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

/-! ### Reversibility of the witnesses -/

/-- A crop is *reversible* when every morphism is invertible. -/
def Reversible (P : Crop) : Prop := ∀ (n : ℕ) (f : P.H n), IsInvertible (P := P) f

/-- A graded-constant crop whose scalar monoid is a group is reversible. -/
theorem gradedData_reversible {M : Type} [Monoid M] (Gd : GradedData M)
    (hinv : ∀ u : M, ∃ v : M, u * v = 1 ∧ v * u = 1) : Reversible Gd.crop := by
  intro n f
  obtain ⟨v, hv1, hv2⟩ := hinv (zElim n f)
  refine ⟨zMk n v, z_ext ?_, z_ext ?_⟩ <;>
    rcases eq_or_ne n 0 with rfl | hn <;>
    simp [zCmp, zIdm, hv1, hv2, *]

/-- The crop of `ControlEquations.CropSmall` is reversible: every hom-monoid is a group. -/
theorem smCrop_reversible : Reversible Sm.SmCrop := by
  intro n f
  refine ⟨Sm.sMk n ((Sm.sElim n f).1, (Sm.sElim n f).2⁻¹), Sm.s_ext ?_, Sm.s_ext ?_⟩ <;>
    rcases eq_or_ne n 0 with rfl | hn
  · show Sm.sElim 0 (Sm.sCmp f _) = Sm.sElim 0 (Sm.sIdm 0)
    rw [Sm.sElim_sCmp, Sm.sElim_sIdm, Sm.sElim_sMk, Sm.sElim_zero]
    simp [Sm.vmul, Sm.vone, Sm.sProj]
  · show Sm.sElim n (Sm.sCmp f _) = Sm.sElim n (Sm.sIdm n)
    rw [Sm.sElim_sCmp, Sm.sElim_sIdm, Sm.sElim_sMk, Sm.sProj_pos hn]
    have h1 : (Sm.sElim n f).1 = false := by
      have := Sm.pair_sElim hn f
      exact (congrArg Prod.fst this).symm
    simp [Sm.vmul, Sm.vone, h1]
  · show Sm.sElim 0 (Sm.sCmp _ f) = Sm.sElim 0 (Sm.sIdm 0)
    rw [Sm.sElim_sCmp, Sm.sElim_sIdm, Sm.sElim_sMk, Sm.sElim_zero]
    simp [Sm.vmul, Sm.vone, Sm.sProj]
  · show Sm.sElim n (Sm.sCmp _ f) = Sm.sElim n (Sm.sIdm n)
    rw [Sm.sElim_sCmp, Sm.sElim_sIdm, Sm.sElim_sMk, Sm.sProj_pos hn]
    have h1 : (Sm.sElim n f).1 = false := by
      have := Sm.pair_sElim hn f
      exact (congrArg Prod.fst this).symm
    simp [Sm.vmul, Sm.vone, h1]

/-! ### How many of the eight equations are needed -/

/-- **Seven of their eight equations imply all eight**, in every controllable prop: (b) may be
omitted, being a consequence of (a) and (e).

Scope: a statement about the equational presentation only. -/
theorem sevenSuffice {P : Crop} {D : Data P}
    (ha : D.EqA) (hc : D.EqC) (hd : D.EqD) (he : D.EqE) (hf : D.EqF) (hg : D.EqG)
    (hh : D.EqH) : D.All :=
  ⟨ha, eqB_of_eqA_eqE ha he, hc, hd, he, hf, hg, hh⟩

/-- **Six of their eight equations imply all eight in the reversible setting**: over a crop all
of whose morphisms are invertible, both (b) and (f) may be omitted.

Scope: a statement about the equational presentation only. -/
theorem sixSufficeReversible {P : Crop} {D : Data P} (hrev : Reversible P)
    (ha : D.EqA) (hc : D.EqC) (hd : D.EqD) (he : D.EqE) (hg : D.EqG) (hh : D.EqH) : D.All := by
  obtain ⟨hb, hf⟩ := eqB_and_eqF_of_groupoid (D := D) hrev ha hd he
  exact ⟨ha, hb, hc, hd, he, hf, hg, hh⟩

/-! ### Irredundancy of the remaining list -/

/-- **Six of the seven equations of `sevenSuffice` are irredundant**: for each of (a), (d), (e),
(f), (g) and (h) there is a controllable prop with control data satisfying the *other seven*
equations of Definition 6 and failing that one.  (The seventh, (c), is open; see
`ControlEquations.CtrlTrivSym` for where a witness cannot live.)

Each conjunct is an existential over crops, so the six witnesses are allowed to differ, as they
do. -/
theorem sixCellsIndependent :
    (∃ (P : Crop) (D : Data P),
        ¬ D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P),
        D.EqA ∧ D.EqB ∧ D.EqC ∧ ¬ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P),
        D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ ¬ D.EqE ∧ D.EqF ∧ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P),
        D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ ¬ D.EqF ∧ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P),
        D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ ¬ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P),
        D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ ¬ D.EqH) :=
  ⟨⟨_, _, eqA_independent⟩, ⟨_, _, eqD_independent⟩, ⟨_, _, eqE_independent⟩,
    ⟨_, _, eqF_independent⟩, ⟨_, _, eqG_independent⟩, Sm.Ctrl.eqH_not_derivable_from_seven⟩

/-- **Five of the six equations of `sixSufficeReversible` are irredundant already inside the
reversible class**: for each of (a), (d), (e), (g) and (h) there is a *reversible* crop with
control data satisfying the other seven equations and failing that one.

(f) cannot appear in this list: over a reversible crop it is a theorem, by
`eqF_of_invertible`.  (c) is open. -/
theorem fiveCellsIndependentReversible :
    (∃ (P : Crop) (D : Data P), Reversible P ∧
        ¬ D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P), Reversible P ∧
        D.EqA ∧ D.EqB ∧ D.EqC ∧ ¬ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P), Reversible P ∧
        D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ ¬ D.EqE ∧ D.EqF ∧ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P), Reversible P ∧
        D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ ¬ D.EqG ∧ D.EqH) ∧
    (∃ (P : Crop) (D : Data P), Reversible P ∧
        D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ ¬ D.EqH) := by
  refine ⟨⟨gA.crop, gA.ctrl V4.brk V4.brk, gradedData_reversible gA (by decide), eqA_independent⟩,
    ⟨gD.crop, gD.ctrl (fun u => u⁻¹) id, gradedData_reversible gD (by decide), eqD_independent⟩,
    ⟨gD.crop, gD.ctrl id id, gradedData_reversible gD (by decide), eqE_independent⟩,
    ⟨gG.crop, gG.ctrl id id, gradedData_reversible gG (by decide), eqG_independent⟩,
    ⟨Sm.SmCrop, Sm.smData, smCrop_reversible, Sm.smData_EqA, Sm.smData_EqB, Sm.smData_EqC,
      Sm.smData_EqD, Sm.smData_EqE, Sm.smData_EqF, Sm.smData_EqG, Sm.smData_not_EqH⟩⟩

/-- **(f) is the one cell whose independence is genuinely lost when passing to the reversible
setting**: over a reversible crop, (a), (d) and (e) imply (f).  So the general witness for (f)
is forced to use non-invertible morphisms, as `gF` does. -/
theorem eqF_derivable_reversible {P : Crop} {D : Data P} (hrev : Reversible P)
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) : D.EqF :=
  (eqB_and_eqF_of_groupoid (D := D) hrev ha hd he).2

end Ctrl

end Crops
