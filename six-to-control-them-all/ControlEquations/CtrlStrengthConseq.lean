import ControlEquations.CtrlStrength
import ControlEquations.CtrlUnique
import ControlEquations.CtrlTwist

/-!
# The minimal presentation

Combining the derivation of their (c) with the models: their eight equations are equivalent to
the six `{a, d, e, f, g, h}`, no proper sub-list of those six entails all eight, and that
six-element list is the only sub-list of the eight which is minimal in that sense.  Over
reversible crops the unique minimal presentation is the five `{a, d, e, g, h}`, since (f) is
derivable there.

A by-product: the central character to which the search for a (c)-witness had been reduced in
`ControlEquations.CtrlTwist` cannot exist, since (c) is now a theorem.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

variable {P : Crop}

/-! ### The upper bound: six equations suffice, and only five are needed for (c) -/

/-- **Their (c) needs only (a), (d), (e), (f), (h).**  (b) is supplied by `eqB_of_eqA_eqE`, and
their (g) plays no role. -/
theorem fiveSuffice_eqC {D : Data P} (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hf : D.EqF)
    (hh : D.EqH) : D.EqC :=
  eqC_of_others ha (eqB_of_eqA_eqE ha he) hd he hf hh

/-- **Six of their eight equations imply all eight, in every crop**: `{a, d, e, f, g, h}` entails
Definition 6.  Compare `sevenSuffice`, which had to assume (c). -/
theorem sixSuffice {D : Data P} (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hf : D.EqF)
    (hg : D.EqG) (hh : D.EqH) : D.All :=
  ⟨ha, eqB_of_eqA_eqE ha he, fiveSuffice_eqC ha hd he hf hh, hd, he, hf, hg, hh⟩

/-- Over a reversible crop, five suffice: `{a, d, e, g, h}`.  Both (b) and (f) are derivable there
(`eqB_and_eqF_of_groupoid`), and (c) is derivable outright. -/
theorem fiveSufficeReversible {D : Data P} (hrev : Reversible P)
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hg : D.EqG) (hh : D.EqH) : D.All := by
  obtain ⟨hb, hf⟩ := eqB_and_eqF_of_groupoid (D := D) hrev ha hd he
  exact ⟨ha, hb, eqC_of_others ha hb hd he hf hh, hd, he, hf, hg, hh⟩

/-! ### The minimal presentation -/

/-- `{a, d, e, f, g, h}` entails all eight. -/
theorem entails_six :
    Entails ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) := by
  intro P D hS
  rw [← all_iff_forall_cell]
  exact sixSuffice (hS .a (by simp)) (hS .d (by simp)) (hS .e (by simp)) (hS .f (by simp))
    (hS .g (by simp)) (hS .h (by simp))

/-- **The minimal presentation is unique and equals `{a, d, e, f, g, h}`.**  A sub-list of their
eight equations entails all eight, with no proper sub-list of it entailing, exactly when it is
`{a, d, e, f, g, h}`.

This is `unique_minimal_presentation_of_eqC_derivable` with its hypothesis discharged by
`eqC_of_others`; the other branch of that dichotomy is now closed off. -/
theorem minimal_presentation_eq_six :
    ∀ S : Set Cell,
      MinimalPresentation S ↔
        S = ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) :=
  unique_minimal_presentation_of_eqC_derivable
    (fun _ _ ha hb hd he hf _ hh => eqC_of_others ha hb hd he hf hh)

/-- `{a, d, e, g, h}` entails all eight inside the reversible class. -/
theorem entailsRev_five :
    EntailsRev ({Cell.a, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) := by
  intro P D hrev hS
  rw [← all_iff_forall_cell]
  exact fiveSufficeReversible hrev (hS .a (by simp)) (hS .d (by simp)) (hS .e (by simp))
    (hS .g (by simp)) (hS .h (by simp))

/-- **Inside the reversible class the minimal presentation is unique and equals
`{a, d, e, g, h}`.** -/
theorem minimal_presentation_rev_eq_five :
    ∀ S : Set Cell,
      MinimalPresentationRev S ↔ S = ({Cell.a, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) := by
  intro S
  constructor
  · rintro ⟨hS, hmin⟩
    by_contra hne
    exact hmin _ ⟨hS.five_subset, fun hsub => hne (Set.Subset.antisymm hsub hS.five_subset)⟩
      entailsRev_five
  · rintro rfl
    exact ⟨entailsRev_five, fun T hT hTe =>
      absurd (Set.Subset.antisymm hT.1 hTe.five_subset) (by
        intro hEq; exact hT.2 (hEq ▸ subset_rfl))⟩

/-- **The whole table, in one statement.**  Their eight equations are equivalent to the six
`{a, d, e, f, g, h}`; no proper sub-list of those six entails; and that six-element list is the
only sub-list of the eight which is minimal in this sense. -/
theorem eight_equations_minimal_presentation :
    Entails ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell)
      ∧ (∀ T : Set Cell, T ⊂ ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) →
          ¬ Entails T)
      ∧ (∀ S : Set Cell, MinimalPresentation S →
          S = ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell)) :=
  ⟨entails_six,
   ((minimal_presentation_eq_six _).2 rfl).2,
   fun S hS => (minimal_presentation_eq_six S).1 hS⟩

/-! ### What the derivability rules out

`ControlEquations.CtrlTwist` reduced a witness for (c) to a single piece of data: a central
character of exponent two, central for the symmetry after control, and nontrivial after padding.
Since (c) is now a theorem, that data cannot exist — the reduction turns into a nonexistence
statement, and the two partial blindness results of `ControlEquations.CtrlCentralImage` become
special cases of it. -/

/-- **No padding-nontrivial symmetry-central character exists.**  If a crop carries control data
satisfying their (a), (d), (e), (f), (h) and a central character whose control commutes with the
symmetry, then the character is trivial after padding by a wire, at every scalar whose padded
control is invertible.  Their (g) is not needed.

Formerly the hypotheses of `twist_is_eqC_witness`, a sufficient criterion for a (c)-witness; by
`eqC_of_others` there is no such witness, so the criterion is never met. -/
theorem central_character_padding_trivial {D : Data P} {X : CentralChar P}
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hf : D.EqF) (hh : D.EqH)
    (hsigma : ∀ f : P.H 0,
      P.cmp (sww (P := P) 0) (D.C1 1 (X.chi f)) = P.cmp (D.C1 1 (X.chi f)) (sww (P := P) 0))
    (f₀ : P.H 0) (hinv : IsInvertible (P := P) (P.tn (D.C1 0 f₀) (P.idm 1))) :
    P.tn (X.chi f₀) (P.idm 1) = P.idm 2 := by
  by_contra hpad
  have hb : D.EqB := eqB_of_eqA_eqE ha he
  have hc : D.EqC := eqC_of_others ha hb hd he hf hh
  have hcT : (D.twist X).EqC :=
    eqC_of_others (twist_EqA ha) (twist_EqB hb) (twist_EqD hd) (twist_EqE he) (twist_EqF hf)
      (twist_EqH ha hh hsigma)
  exact twist_not_EqC hc f₀ hinv hpad hcT

end Ctrl

end Crops
