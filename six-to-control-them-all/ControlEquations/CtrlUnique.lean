import ControlEquations.CtrlMinimal

/-!
# Which sub-lists of the eight equations suffice, and is the minimal one unique

`ControlEquations.CtrlMinimal` shows that a sub-list of the eight control equations already
implies all eight, and that most members of that sub-list cannot be dropped.  That leaves the
question one level up: two irredundant subsets of a set of axioms need not have the same size,
let alone be the same set, so which sub-lists work?

This file answers it by quantifying over subsets of the eight rather than inspecting them one at
a time.  Write `Cell` for the eight labels and `Entails S` for the statement that in every
controllable prop the equations labelled by `S` imply all eight.  Then `Entails.six_subset` says
every entailing `S` contains all of (a), (d), (e), (f), (g) and (h), and `entails_seven` says
the seven-element set `{a, c, d, e, f, g, h}` entails; so `entailing_subsets_pinned` bounds the
minimal presentations to at most two, differing only in the cell (c).

The two branches are `unique_minimal_presentation_of_eqC_independent` and
`unique_minimal_presentation_of_eqC_derivable`.  Either way the minimal presentation is unique,
which settles uniqueness without settling (c); `ControlEquations.CtrlStrength` then settles (c),
and `ControlEquations.CtrlStrengthConseq` discharges the second branch to give the answer
`{a, d, e, f, g, h}`.

The same is done inside the reversible class, where the answer is one cell shorter because (f)
is derivable there: `EntailsRev.five_subset`, `entailsRev_six`,
`minimal_presentation_unique_reversible`.

Entailment here is semantic and unrestricted, quantifying over all crops.  It is not entailment
in a proof system, and it is not the structural minimality of their Corollary 18.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

/-! ### The eight labels, and entailment between sub-lists -/

/-- A label for each of the eight equations of their Definition 6. -/
inductive Cell
  | a | b | c | d | e | f | g | h
  deriving DecidableEq, Repr

/-- The equation a label stands for. -/
def Cell.holds : Cell → {P : Crop} → Data P → Prop
  | .a, _, D => D.EqA
  | .b, _, D => D.EqB
  | .c, _, D => D.EqC
  | .d, _, D => D.EqD
  | .e, _, D => D.EqE
  | .f, _, D => D.EqF
  | .g, _, D => D.EqG
  | .h, _, D => D.EqH

/-- `D` satisfies all eight equations iff every label holds of it. -/
theorem all_iff_forall_cell {P : Crop} (D : Data P) : D.All ↔ ∀ t : Cell, t.holds D := by
  constructor
  · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ t
    cases t <;> assumption
  · intro h
    exact ⟨h .a, h .b, h .c, h .d, h .e, h .f, h .g, h .h⟩

/-- `S` **entails** when, in every controllable prop, the equations labelled by `S` imply all
eight equations of Definition 6. -/
def Entails (S : Set Cell) : Prop :=
  ∀ (P : Crop) (D : Data P), (∀ s ∈ S, s.holds D) → ∀ t : Cell, t.holds D

/-- The same notion restricted to reversible controllable props. -/
def EntailsRev (S : Set Cell) : Prop :=
  ∀ (P : Crop) (D : Data P), Reversible P → (∀ s ∈ S, s.holds D) → ∀ t : Cell, t.holds D

theorem EntailsRev.of_entails {S : Set Cell} (h : Entails S) : EntailsRev S :=
  fun P D _ hs => h P D hs

/-! ### The extraction lemma

A model failing **exactly one** label forces that label into every entailing subset.  This is
the only place the shape of the witnesses is used, and it is why they were built to satisfy all
seven of the other equations rather than just enough to make a point. -/

/-- If some control data satisfies every label other than `t` and fails `t`, then `t` belongs to
every entailing subset. -/
theorem Entails.mem_of_witness {S : Set Cell} (hS : Entails S) {t : Cell} {P : Crop}
    {D : Data P} (hother : ∀ u : Cell, u ≠ t → u.holds D) (hfail : ¬ t.holds D) : t ∈ S := by
  by_contra hmem
  exact hfail (hS P D (fun s hs => hother s fun hst => hmem (hst ▸ hs)) t)

/-- The reversible variant. -/
theorem EntailsRev.mem_of_witness {S : Set Cell} (hS : EntailsRev S) {t : Cell} {P : Crop}
    {D : Data P} (hrev : Reversible P) (hother : ∀ u : Cell, u ≠ t → u.holds D)
    (hfail : ¬ t.holds D) : t ∈ S := by
  by_contra hmem
  exact hfail (hS P D hrev (fun s hs => hother s fun hst => hmem (hst ▸ hs)) t)

/-! ### Every entailing sub-list contains the six settled cells -/

/-- **Every entailing subset of their eight equations contains (a), (d), (e), (f), (g) and
(h).**  Only the cells (b) — which is derivable — and (c) — which is open — can be missing.

Scope: general controllable props; a statement about the equational presentation only. -/
theorem Entails.six_subset {S : Set Cell} (hS : Entails S) :
    ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) ⊆ S := by
  have hA : Cell.a ∈ S := by
    obtain ⟨hna, hb, hc, hd, he, hf, hg, hh⟩ := eqA_independent
    exact hS.mem_of_witness (D := gA.ctrl V4.brk V4.brk)
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hna
  have hD : Cell.d ∈ S := by
    obtain ⟨ha, hb, hc, hnd, he, hf, hg, hh⟩ := eqD_independent
    exact hS.mem_of_witness (D := gD.ctrl (fun u => u⁻¹) id)
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hnd
  have hE : Cell.e ∈ S := by
    obtain ⟨ha, hb, hc, hd, hne, hf, hg, hh⟩ := eqE_independent
    exact hS.mem_of_witness (D := gD.ctrl id id)
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hne
  have hF : Cell.f ∈ S := by
    obtain ⟨ha, hb, hc, hd, he, hnf, hg, hh⟩ := eqF_independent
    exact hS.mem_of_witness (D := gF.ctrl id id)
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hnf
  have hG : Cell.g ∈ S := by
    obtain ⟨ha, hb, hc, hd, he, hf, hng, hh⟩ := eqG_independent
    exact hS.mem_of_witness (D := gG.ctrl id id)
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hng
  have hH : Cell.h ∈ S := by
    exact hS.mem_of_witness (D := Sm.smData)
      (fun u hu => by
        cases u <;>
          first
            | exact absurd rfl hu
            | exact Sm.smData_EqA | exact Sm.smData_EqB | exact Sm.smData_EqC
            | exact Sm.smData_EqD | exact Sm.smData_EqE | exact Sm.smData_EqF
            | exact Sm.smData_EqG)
      Sm.smData_not_EqH
  intro u hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- **Every subset entailing inside the reversible class contains (a), (d), (e), (g) and (h).**
(f) is absent because it is derivable there (`eqF_derivable_reversible`), and (b) because it is
derivable outright; (c) is settled separately.

Scope: reversible controllable props. -/
theorem EntailsRev.five_subset {S : Set Cell} (hS : EntailsRev S) :
    ({Cell.a, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) ⊆ S := by
  have hA : Cell.a ∈ S := by
    obtain ⟨hna, hb, hc, hd, he, hf, hg, hh⟩ := eqA_independent
    exact hS.mem_of_witness (D := gA.ctrl V4.brk V4.brk) (gradedData_reversible gA (by decide))
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hna
  have hD : Cell.d ∈ S := by
    obtain ⟨ha, hb, hc, hnd, he, hf, hg, hh⟩ := eqD_independent
    exact hS.mem_of_witness (D := gD.ctrl (fun u => u⁻¹) id)
      (gradedData_reversible gD (by decide))
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hnd
  have hE : Cell.e ∈ S := by
    obtain ⟨ha, hb, hc, hd, hne, hf, hg, hh⟩ := eqE_independent
    exact hS.mem_of_witness (D := gD.ctrl id id) (gradedData_reversible gD (by decide))
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hne
  have hG : Cell.g ∈ S := by
    obtain ⟨ha, hb, hc, hd, he, hf, hng, hh⟩ := eqG_independent
    exact hS.mem_of_witness (D := gG.ctrl id id) (gradedData_reversible gG (by decide))
      (fun u hu => by cases u <;> first | exact absurd rfl hu | assumption) hng
  have hH : Cell.h ∈ S := by
    exact hS.mem_of_witness (D := Sm.smData) smCrop_reversible
      (fun u hu => by
        cases u <;>
          first
            | exact absurd rfl hu
            | exact Sm.smData_EqA | exact Sm.smData_EqB | exact Sm.smData_EqC
            | exact Sm.smData_EqD | exact Sm.smData_EqE | exact Sm.smData_EqF
            | exact Sm.smData_EqG)
      Sm.smData_not_EqH
  intro u hu
  rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption

/-! ### The upper bounds: sub-lists that do entail -/

/-- The seven-element sub-list `{a, c, d, e, f, g, h}` entails all eight
(this is `sevenSuffice`, repackaged). -/
theorem entails_seven :
    Entails ({Cell.a, Cell.c, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) := by
  intro P D hS
  rw [← all_iff_forall_cell]
  exact sevenSuffice (hS .a (by simp)) (hS .c (by simp)) (hS .d (by simp)) (hS .e (by simp))
    (hS .f (by simp)) (hS .g (by simp)) (hS .h (by simp))

/-- The six-element sub-list `{a, c, d, e, g, h}` entails all eight inside the reversible class
(this is `sixSufficeReversible`, repackaged). -/
theorem entailsRev_six :
    EntailsRev ({Cell.a, Cell.c, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) := by
  intro P D hrev hS
  rw [← all_iff_forall_cell]
  exact sixSufficeReversible hrev (hS .a (by simp)) (hS .c (by simp)) (hS .d (by simp))
    (hS .e (by simp)) (hS .g (by simp)) (hS .h (by simp))

/-! ### The pinning theorems -/

/-- **The entailing sub-lists are pinned between two sets that differ in one cell.**  Every
entailing subset of their eight equations contains `{a, d, e, f, g, h}`, and adding (c) to that
set already entails.  So (b) is in no minimal entailing sub-list, and the only cell whose
membership is not decided is (c). -/
theorem entailing_subsets_pinned :
    (∀ S : Set Cell, Entails S → ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) ⊆ S)
      ∧ Entails ({Cell.a, Cell.c, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) :=
  ⟨fun _ hS => hS.six_subset, entails_seven⟩

/-- The reversible pinning: every reversibly-entailing subset contains `{a, d, e, g, h}`, and
`{a, c, d, e, g, h}` reversibly entails. -/
theorem entailing_subsets_pinned_reversible :
    (∀ S : Set Cell, EntailsRev S →
        ({Cell.a, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) ⊆ S)
      ∧ EntailsRev ({Cell.a, Cell.c, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) :=
  ⟨fun _ hS => hS.five_subset, entailsRev_six⟩

/-! ### Uniqueness of the minimal presentation

`S` is a *minimal presentation* when it entails and no proper subset of it does.  The two
theorems below show the minimal presentation is unique whichever way (c) falls, so
so uniqueness is settled even though (c) is not. -/

/-- `S` is a minimal presentation: it entails, and no proper subset of it does. -/
def MinimalPresentation (S : Set Cell) : Prop :=
  Entails S ∧ ∀ T : Set Cell, T ⊂ S → ¬ Entails T

/-- The reversible analogue. -/
def MinimalPresentationRev (S : Set Cell) : Prop :=
  EntailsRev S ∧ ∀ T : Set Cell, T ⊂ S → ¬ EntailsRev T

/-- **If (c) is independent, the minimal presentation is unique and equals
`{a, c, d, e, f, g, h}`.**  ("(c) is independent" is stated as: some control data satisfies all
labels but (c) and fails (c).) -/
theorem unique_minimal_presentation_of_eqC_independent
    (hcInd : ∃ (P : Crop) (D : Data P), (∀ u : Cell, u ≠ Cell.c → u.holds D) ∧ ¬ D.EqC) :
    ∀ S : Set Cell,
      MinimalPresentation S ↔
        S = ({Cell.a, Cell.c, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) := by
  obtain ⟨P₀, D₀, hother, hnc⟩ := hcInd
  -- every entailing set contains the seven
  have key : ∀ S : Set Cell, Entails S →
      ({Cell.a, Cell.c, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) ⊆ S := by
    intro S hS
    have hC : Cell.c ∈ S := hS.mem_of_witness (D := D₀) hother hnc
    have h6 := hS.six_subset
    intro u hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h6 (by simp)
    · exact hC
    · exact h6 (by simp)
    · exact h6 (by simp)
    · exact h6 (by simp)
    · exact h6 (by simp)
    · exact h6 (by simp)
  intro S
  constructor
  · rintro ⟨hS, hmin⟩
    by_contra hne
    exact hmin _ ⟨key S hS, fun hsub => hne (Set.Subset.antisymm hsub (key S hS))⟩ entails_seven
  · rintro rfl
    exact ⟨entails_seven, fun T hT hTe =>
      absurd (Set.Subset.antisymm hT.1 (key T hTe)) (by
        intro hEq; exact hT.2 (hEq ▸ subset_rfl))⟩

/-- **If instead (c) is derivable from the other seven, the minimal presentation is again
unique, and equals `{a, d, e, f, g, h}`.**  Together with the previous theorem: *whichever way
(c) falls, the minimal presentation is unique*; the two possible answers are the
six-element and the seven-element list, and they differ only in (c). -/
theorem unique_minimal_presentation_of_eqC_derivable
    (hcDer : ∀ (P : Crop) (D : Data P), D.EqA → D.EqB → D.EqD → D.EqE → D.EqF → D.EqG →
      D.EqH → D.EqC) :
    ∀ S : Set Cell,
      MinimalPresentation S ↔
        S = ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) := by
  have hsix : Entails ({Cell.a, Cell.d, Cell.e, Cell.f, Cell.g, Cell.h} : Set Cell) := by
    intro P D hS
    have ha : D.EqA := hS .a (by simp)
    have hd : D.EqD := hS .d (by simp)
    have he : D.EqE := hS .e (by simp)
    have hf : D.EqF := hS .f (by simp)
    have hg : D.EqG := hS .g (by simp)
    have hh : D.EqH := hS .h (by simp)
    have hb : D.EqB := eqB_of_eqA_eqE ha he
    rw [← all_iff_forall_cell]
    exact ⟨ha, hb, hcDer P D ha hb hd he hf hg hh, hd, he, hf, hg, hh⟩
  intro S
  constructor
  · rintro ⟨hS, hmin⟩
    by_contra hne
    exact hmin _ ⟨hS.six_subset, fun hsub => hne (Set.Subset.antisymm hsub hS.six_subset)⟩ hsix
  · rintro rfl
    exact ⟨hsix, fun T hT hTe =>
      absurd (Set.Subset.antisymm hT.1 hTe.six_subset) (by
        intro hEq; exact hT.2 (hEq ▸ subset_rfl))⟩

/-- **The minimal presentation is unique, unconditionally.**  Whether or not (c) is derivable,
there is exactly one minimal entailing sub-list of their eight equations: it is
`{a, c, d, e, f, g, h}` in the first case and `{a, d, e, f, g, h}` in the second.  In particular
the uniqueness question — two irredundant subsets of an axiom list need not even have the same
size — is settled here without settling (c). -/
theorem minimal_presentation_unique :
    ∃ S₀ : Set Cell, ∀ S : Set Cell, MinimalPresentation S ↔ S = S₀ := by
  by_cases hc : ∃ (P : Crop) (D : Data P), (∀ u : Cell, u ≠ Cell.c → u.holds D) ∧ ¬ D.EqC
  · exact ⟨_, unique_minimal_presentation_of_eqC_independent hc⟩
  · refine ⟨_, unique_minimal_presentation_of_eqC_derivable ?_⟩
    intro P D ha hb hd he hf hg hh
    by_contra hnc
    exact hc ⟨P, D, fun u hu => by cases u <;> first | exact absurd rfl hu | assumption, hnc⟩

/-- **Uniqueness inside the reversible class**, by the same argument: the minimal reversible
presentation is `{a, c, d, e, g, h}` if (c) is independent there and `{a, d, e, g, h}` if it is
derivable, and in either case it is unique. -/
theorem minimal_presentation_unique_reversible :
    ∃ S₀ : Set Cell, ∀ S : Set Cell, MinimalPresentationRev S ↔ S = S₀ := by
  by_cases hc : ∃ (P : Crop) (D : Data P), Reversible P ∧
      (∀ u : Cell, u ≠ Cell.c → u.holds D) ∧ ¬ D.EqC
  · obtain ⟨P₀, D₀, hrev₀, hother, hnc⟩ := hc
    have key : ∀ S : Set Cell, EntailsRev S →
        ({Cell.a, Cell.c, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) ⊆ S := by
      intro S hS
      have hC : Cell.c ∈ S := hS.mem_of_witness (D := D₀) hrev₀ hother hnc
      have h5 := hS.five_subset
      intro u hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h5 (by simp)
      · exact hC
      · exact h5 (by simp)
      · exact h5 (by simp)
      · exact h5 (by simp)
      · exact h5 (by simp)
    refine ⟨({Cell.a, Cell.c, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell), fun S => ⟨?_, ?_⟩⟩
    · rintro ⟨hS, hmin⟩
      by_contra hne
      exact hmin _ ⟨key S hS, fun hsub => hne (Set.Subset.antisymm hsub (key S hS))⟩ entailsRev_six
    · rintro rfl
      exact ⟨entailsRev_six, fun T hT hTe =>
        absurd (Set.Subset.antisymm hT.1 (key T hTe)) (by
          intro hEq; exact hT.2 (hEq ▸ subset_rfl))⟩
  · have hcDer : ∀ (P : Crop) (D : Data P), Reversible P → D.EqA → D.EqB → D.EqD → D.EqE →
        D.EqF → D.EqG → D.EqH → D.EqC := by
      intro P D hrev ha hb hd he hf hg hh
      by_contra hnc
      exact hc ⟨P, D, hrev, fun u hu => by cases u <;> first | exact absurd rfl hu | assumption,
        hnc⟩
    have hfive : EntailsRev ({Cell.a, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell) := by
      intro P D hrev hS
      have ha : D.EqA := hS .a (by simp)
      have hd : D.EqD := hS .d (by simp)
      have he : D.EqE := hS .e (by simp)
      have hg : D.EqG := hS .g (by simp)
      have hh : D.EqH := hS .h (by simp)
      obtain ⟨hb, hf⟩ := eqB_and_eqF_of_groupoid (D := D) hrev ha hd he
      rw [← all_iff_forall_cell]
      exact ⟨ha, hb, hcDer P D hrev ha hb hd he hf hg hh, hd, he, hf, hg, hh⟩
    refine ⟨({Cell.a, Cell.d, Cell.e, Cell.g, Cell.h} : Set Cell), fun S => ⟨?_, ?_⟩⟩
    · rintro ⟨hS, hmin⟩
      by_contra hne
      exact hmin _ ⟨hS.five_subset, fun hsub => hne (Set.Subset.antisymm hsub hS.five_subset)⟩
        hfive
    · rintro rfl
      exact ⟨hfive, fun T hT hTe =>
        absurd (Set.Subset.antisymm hT.1 hTe.five_subset) (by
          intro hEq; exact hT.2 (hEq ▸ subset_rfl))⟩

end Ctrl

end Crops
