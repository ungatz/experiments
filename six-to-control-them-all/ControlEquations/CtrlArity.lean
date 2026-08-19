import ControlEquations.CtrlModels

/-!
# No characterisation by bounded arity

Each of their (a), (c), (e), (f) and (h) is a scheme indexed by arity, so an instance at arity
`n` is a rule on `n+1` wires and the presentation is not bounded-arity.

Under the reading used throughout, in which `C0` and `C1` are bare arity-indexed maps, the
arities of a control datum are logically unrelated, and it follows formally that for every `N`
there is a crop carrying two control data agreeing at every arity at most `N`, one satisfying
all eight equations and one not.  Hence no condition invariant under agreement below `N` is
equivalent to Definition 6.

This is a formal check that a comparison with the unbounded-arity theorem of Clément, Delorme
and Perdrix is not available, not an analogue of it.  Their theorem is about circuits over fixed
generators, where the semantics constrains what the higher arities may do; the statement below
is a consequence of the bare-maps reading alone, and is the one place where that reading is
load-bearing.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

variable {P : Crop}

/-- Two control data **agree below `N`** when their `C0` and `C1` coincide at every arity `≤ N`.
Any condition that inspects control only at arities `≤ N` cannot separate such a pair. -/
def Data.AgreeBelow (N : ℕ) (D D' : Data P) : Prop :=
  ∀ n ≤ N, D.C0 n = D'.C0 n ∧ D.C1 n = D'.C1 n

namespace GradedData

variable {M : Type} [Monoid M] (G : GradedData M)

/-- Control data given by one pair of functions at arities `≤ N` and another pair above `N`. -/
def ctrlSplit (c0 c1 d0 d1 : M → M) (N : ℕ) : Data G.crop where
  C0 n a := zMk (1 + n) (if n ≤ N then c0 (zElim n a) else d0 (zElim n a))
  C1 n a := zMk (1 + n) (if n ≤ N then c1 (zElim n a) else d1 (zElim n a))

lemma ctrlSplit_agreeBelow (c0 c1 d0 d1 : M → M) (N : ℕ) :
    Data.AgreeBelow N (G.ctrl c0 c1) (G.ctrlSplit c0 c1 d0 d1 N) := by
  intro n hn
  constructor <;> funext a <;>
    simp only [ctrl, ctrlSplit, if_pos hn]

end GradedData

/-! ### The separating pair -/

/-- The nontrivial element of the two-element carrier. -/
def c2gen : C2 := Multiplicative.ofAdd (1 : ZMod 2)

lemma c2gen_ne_one : c2gen ≠ 1 := by decide

/-- **For every `N` there is a crop carrying two control data that agree at all arities `≤ N`,
one satisfying all eight of their equations and one satisfying none of the arity-`(N+1)`
instances of (b).**

The carrier is the two-element graded crop `gAll` of `ControlEquations.CtrlModels`; the second
datum is the first, redefined above arity `N` to be constantly the nontrivial element. -/
theorem exists_arity_indistinguishable (N : ℕ) :
    ∃ (P : Crop) (D D' : Data P), Data.AgreeBelow N D D' ∧ D.All ∧ ¬ D'.All := by
  refine ⟨gAll.crop, gAll.ctrl id id,
    gAll.ctrlSplit id id (fun _ => c2gen) (fun _ => c2gen) N,
    gAll.ctrlSplit_agreeBelow id id (fun _ => c2gen) (fun _ => c2gen) N, allEight_model, ?_⟩
  rintro ⟨-, hb, -⟩
  have h := congrArg (zElim (M := C2) (1 + (N + 1))) (hb (N + 1))
  have hlt : ¬ (N + 1 ≤ N) := by omega
  simp only [GradedData.ctrlSplit, GradedData.crop_idm, zElim_zIdm, if_neg hlt,
    zElim_zMk_pos (show 1 + (N + 1) ≠ 0 by omega)] at h
  exact c2gen_ne_one h

/-- **No condition of bounded arity characterises their eight equations.**  If a property `Φ` of
control data cannot tell apart two data that agree at every arity `≤ N`, then `Φ` is not
equivalent to Definition 6.

Read in the service register: their Definition 6 is a finite list of *schemes*, and this says
the schemes cannot be replaced by their instances up to any fixed arity.  Compare Clément,
Delorme and Perdrix (LICS 2024) for the corresponding — and much deeper — statement about
quantum circuits; see the file header for why the two are not of comparable strength. -/
theorem no_bounded_arity_characterisation (N : ℕ) (Phi : ∀ P : Crop, Data P → Prop)
    (hinv : ∀ (P : Crop) (D D' : Data P), Data.AgreeBelow N D D' → (Phi P D ↔ Phi P D')) :
    ¬ (∀ (P : Crop) (D : Data P), Phi P D ↔ D.All) := by
  intro hchar
  obtain ⟨P, D, D', hagree, hall, hnot⟩ := exists_arity_indistinguishable N
  exact hnot ((hchar P D').1 (((hinv P D D' hagree).1 ((hchar P D).2 hall))))

end Ctrl

end Crops
