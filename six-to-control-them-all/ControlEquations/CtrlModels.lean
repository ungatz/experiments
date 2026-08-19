import ControlEquations.CtrlGraded

/-!
# Five models separating five of the control equations

The first question in the conclusion of Heunen, Kaarsgaard and Lemonnier asks for models
satisfying all but one of the control equations of their Figure 1.  This file supplies five, one
each for (a), (d), (e), (f) and (g).  Every one of them is a graded-constant crop, so the
hom-monoid is a fixed monoid `M` in every positive arity, the empty wire is a strict unit, and
every permutation acts as the identity.

| equation failing | carrier | control data |
|---|---|---|
| (a) | Klein four-group `V4` | `c0 = c1 =` a non-multiplicative map fixing `1` |
| (d) | cyclic group `C3` | `c1 = id`, `c0 =` inversion |
| (e) | cyclic group `C3` | `c0 = c1 = id` |
| (f) | the six-element monoid `M6 = ⟨p,q⟩`, all words of length at least two absorbing except `pq` and `qp` | `c0 = c1 = id` |
| (g) | cyclic group `C2`, with `x` the nontrivial element | `c0 = c1 = id` |

`allEight_model`, with carrier `C2` and `x = 1`, satisfies all eight equations, so the
seven-equation fragments above are not vacuously satisfied.

The two remaining cells are not separated by any crop in this family, and for a reason:
their (h) holds in every crop with a trivial symmetry (`eqH_holds`), and their (c) holds in
every finite graded-constant crop (`eqC_of_finite_graded`).  `ControlEquations.CtrlComm` gives
the general reason, and `ControlEquations.CropSmall` leaves the family to separate (h).
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

open GradedData

/-! ### Small finite carriers -/

/-- The Klein four-group, as a carrier. -/
inductive V4 | e | a | b | c
  deriving DecidableEq, Fintype, Repr

namespace V4

/-- Multiplication of the Klein four-group. -/
def mul : V4 → V4 → V4
  | e, y => y
  | x, e => x
  | a, a => e | a, b => c | a, c => b
  | b, a => c | b, b => e | b, c => a
  | c, a => b | c, b => a | c, c => e

instance : Monoid V4 where
  mul := mul
  one := e
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

@[simp] lemma one_def : (1 : V4) = e := rfl

/-- A non-multiplicative self-map fixing the unit and squaring to the unit. -/
def brk : V4 → V4
  | e => e | a => a | b => b | c => e

end V4

/-- The 6-element monoid `⟨p, q⟩` in which every word of length `≥ 3`, and both `pp` and `qq`,
is the absorbing element. -/
inductive M6 | one | p | q | pq | qp | zero
  deriving DecidableEq, Fintype, Repr

namespace M6

/-- Multiplication of `M6`. -/
def mul : M6 → M6 → M6
  | one, y => y
  | x, one => x
  | p, q => pq
  | q, p => qp
  | _, _ => zero

instance : Monoid M6 where
  mul := mul
  one := one
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

@[simp] lemma one_def : (1 : M6) = one := rfl

/-- The collapse map: the unit stays, everything else goes to the absorbing element. -/
def col : M6 → M6
  | one => one
  | _ => zero

/-- `col` as a monoid endomorphism. -/
def colHom : M6 →* M6 where
  toFun := col
  map_one' := rfl
  map_mul' := by decide

end M6

/-! ### The trivial grading -/

/-- The graded-constant data whose monoidal product is trivial in positive arities
(`al = 1`), with a prescribed involution. -/
def trivGrading {M : Type} [Monoid M] (x : M) (hx : x * x = 1) : GradedData M where
  al := 1
  al_idem _ := rfl
  al_comm _ _ := rfl
  x := x
  x_invol := hx

@[simp] lemma trivGrading_al {M : Type} [Monoid M] (x : M) (hx : x * x = 1) (u : M) :
    (trivGrading x hx).al u = 1 := rfl

@[simp] lemma trivGrading_x {M : Type} [Monoid M] (x : M) (hx : x * x = 1) :
    (trivGrading x hx).x = x := rfl

/-! ### A model of all eight equations

The seven-equation fragments below are not vacuous: here is a controllable prop with control
data satisfying all eight of their equations.  (Their own models are of course the interesting
ones; this one only certifies that the fragments being separated are consistent.) -/

/-- Carrier `C2 = ℤ/2` written multiplicatively, `x = 1`, `C0 = C1 = id`. -/
abbrev C2 := Multiplicative (ZMod 2)

/-- Carrier `C3 = ℤ/3` written multiplicatively. -/
abbrev C3 := Multiplicative (ZMod 3)

/-- The graded-constant crop on `C2` with trivial involution. -/
def gAll : GradedData C2 := trivGrading (1 : C2) (by decide)

theorem allEight_model : ((gAll.ctrl id id).All) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqA_iff]; decide
  · rw [eqB_iff]; decide
  · rw [eqC_iff]; decide
  · rw [eqD_iff]; exact ⟨by decide, by decide⟩
  · rw [eqE_iff]; decide
  · rw [eqF_iff]; decide
  · rw [eqG_iff]; decide
  · exact eqH_holds _ _ _

/-! ### (a) is independent -/

/-- The graded-constant crop on the Klein four-group with trivial involution. -/
def gA : GradedData V4 := trivGrading (1 : V4) (by decide)

/-- **Their equation (a) is independent of the other seven**, witnessed by the Klein
four-group with `C0 = C1 = brk`.  (Under the reading in which `C0`, `C1` are merely
arity-indexed maps on morphisms, which is how Figure 1 lists (a).) -/
theorem eqA_independent :
    ¬ (gA.ctrl V4.brk V4.brk).EqA ∧ (gA.ctrl V4.brk V4.brk).EqB ∧
      (gA.ctrl V4.brk V4.brk).EqC ∧ (gA.ctrl V4.brk V4.brk).EqD ∧
      (gA.ctrl V4.brk V4.brk).EqE ∧ (gA.ctrl V4.brk V4.brk).EqF ∧
      (gA.ctrl V4.brk V4.brk).EqG ∧ (gA.ctrl V4.brk V4.brk).EqH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqA_iff]; decide
  · rw [eqB_iff]; decide
  · rw [eqC_iff]; decide
  · rw [eqD_iff]; exact ⟨by decide, by decide⟩
  · rw [eqE_iff]; decide
  · rw [eqF_iff]; decide
  · rw [eqG_iff]; decide
  · exact eqH_holds _ _ _

/-! ### (d) is independent -/

/-- The graded-constant crop on `C3` with trivial involution. -/
def gD : GradedData C3 := trivGrading (1 : C3) (by decide)

/-- **Their equation (d) is independent of the other seven**, witnessed by `C3` with
`C1 = id` and `C0 = ` inversion.  Note both maps are genuine endofunctors here, so the witness
is insensitive to whether functoriality is read as data or as the equations (a), (b). -/
theorem eqD_independent :
    (gD.ctrl (fun u => u⁻¹) id).EqA ∧ (gD.ctrl (fun u => u⁻¹) id).EqB ∧
      (gD.ctrl (fun u => u⁻¹) id).EqC ∧ ¬ (gD.ctrl (fun u => u⁻¹) id).EqD ∧
      (gD.ctrl (fun u => u⁻¹) id).EqE ∧ (gD.ctrl (fun u => u⁻¹) id).EqF ∧
      (gD.ctrl (fun u => u⁻¹) id).EqG ∧ (gD.ctrl (fun u => u⁻¹) id).EqH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqA_iff]; decide
  · rw [eqB_iff]; decide
  · rw [eqC_iff]; decide
  · rw [eqD_iff]
    rintro ⟨-, h⟩
    have := h (Multiplicative.ofAdd (1 : ZMod 3))
    revert this
    decide
  · rw [eqE_iff]; decide
  · rw [eqF_iff]; decide
  · rw [eqG_iff]; decide
  · exact eqH_holds _ _ _

/-! ### (e) is independent -/

/-- **Their equation (e) is independent of the other seven**, witnessed by `C3` with
`C0 = C1 = id`. -/
theorem eqE_independent :
    (gD.ctrl id id).EqA ∧ (gD.ctrl id id).EqB ∧ (gD.ctrl id id).EqC ∧
      (gD.ctrl id id).EqD ∧ ¬ (gD.ctrl id id).EqE ∧ (gD.ctrl id id).EqF ∧
      (gD.ctrl id id).EqG ∧ (gD.ctrl id id).EqH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqA_iff]; decide
  · rw [eqB_iff]; decide
  · rw [eqC_iff]; decide
  · rw [eqD_iff]; exact ⟨by decide, by decide⟩
  · rw [eqE_iff]; decide
  · rw [eqF_iff]; decide
  · rw [eqG_iff]; decide
  · exact eqH_holds _ _ _

/-! ### (f) is independent -/

/-- The graded-constant crop on `M6`, whose monoidal product collapses everything but the
unit. -/
def gF : GradedData M6 where
  al := M6.colHom
  al_idem := by decide
  al_comm := by decide
  x := 1
  x_invol := by decide

/-- **Their equation (f) is independent of the other seven**, witnessed by the 6-element
monoid `M6` with `C0 = C1 = id`.  By `eqF_of_invertible` such a witness must have
non-invertible morphisms, and `M6` is the smallest shape realising that. -/
theorem eqF_independent :
    (gF.ctrl id id).EqA ∧ (gF.ctrl id id).EqB ∧ (gF.ctrl id id).EqC ∧
      (gF.ctrl id id).EqD ∧ (gF.ctrl id id).EqE ∧ ¬ (gF.ctrl id id).EqF ∧
      (gF.ctrl id id).EqG ∧ (gF.ctrl id id).EqH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqA_iff]; decide
  · rw [eqB_iff]; decide
  · rw [eqC_iff]; decide
  · rw [eqD_iff]; exact ⟨by decide, by decide⟩
  · rw [eqE_iff]; decide
  · rw [eqF_iff]; decide
  · rw [eqG_iff]; decide
  · exact eqH_holds _ _ _

/-! ### (g) is independent -/

/-- The graded-constant crop on `C2` whose involution is the nontrivial element. -/
def gG : GradedData C2 := trivGrading (Multiplicative.ofAdd (1 : ZMod 2)) (by decide)

/-- **Their equation (g) is independent of the other seven**, witnessed by `C2` with the
nontrivial involution and `C0 = C1 = id`. -/
theorem eqG_independent :
    (gG.ctrl id id).EqA ∧ (gG.ctrl id id).EqB ∧ (gG.ctrl id id).EqC ∧
      (gG.ctrl id id).EqD ∧ (gG.ctrl id id).EqE ∧ (gG.ctrl id id).EqF ∧
      ¬ (gG.ctrl id id).EqG ∧ (gG.ctrl id id).EqH := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqA_iff]; decide
  · rw [eqB_iff]; decide
  · rw [eqC_iff]; decide
  · rw [eqD_iff]; exact ⟨by decide, by decide⟩
  · rw [eqE_iff]; decide
  · rw [eqF_iff]; decide
  · rw [eqG_iff]; decide
  · exact eqH_holds _ _ _

/-! ### The blindness theorem for (c)

No *finite* graded-constant model can witness the independence of (c): over that class, (c) is
a consequence of (a), (d) and (e).  So the cell (c) is genuinely open, and any witness must
leave the class in which every other witness here lives — either by having an infinite
hom-monoid or by having a nontrivial symmetry inclusion. -/

/-- **Over finite graded-constant crops, their equation (c) follows from (a), (d) and (e).**

The mechanism: (d) and (e) force `al u = (al (c1 u))²`, so squaring is surjective on the finite
commutative submonoid `range al`, hence injective there, hence the conjugating element
`al x` — an involution — is the unit.  Then (e) reads `c1 u * c1 u = al u` and (c) follows by
applying it to `c1 u`. -/
theorem eqC_of_finite_graded {M : Type} [Monoid M] [Finite M] (G : GradedData M)
    (c0 c1 : M → M) (ha : (G.ctrl c0 c1).EqA) (hd : (G.ctrl c0 c1).EqD)
    (he : (G.ctrl c0 c1).EqE) : (G.ctrl c0 c1).EqC := by
  rw [eqA_iff] at ha
  rw [eqD_iff] at hd
  rw [eqE_iff] at he
  obtain ⟨-, hd⟩ := hd
  set a : M := G.al G.x with hadef
  have haa : a * a = 1 := by
    rw [hadef, ← map_mul, G.x_invol, map_one]
  -- (d) + (e): `a * c1 u * a * c1 u = al u`
  have key : ∀ u : M, a * c1 u * (a * c1 u) = G.al u := by
    intro u
    have h1 : c0 u = a * c1 u * a := by
      have := hd u
      calc c0 u = 1 * c0 u * 1 := by rw [one_mul, mul_one]
        _ = a * a * c0 u * (a * a) := by rw [haa]
        _ = a * (a * c0 u * a) * a := by simp [mul_assoc]
        _ = a * c1 u * a := by rw [this]
    have := he u
    rw [h1] at this
    calc a * c1 u * (a * c1 u) = a * c1 u * a * c1 u := by simp [mul_assoc]
      _ = G.al u := this
  -- applying `al` : every element of the image is a square in the image
  have sq : ∀ u : M, G.al (c1 u) * G.al (c1 u) = G.al u := by
    intro u
    have hala : G.al a = a := by rw [hadef, G.al_idem]
    have h := congrArg G.al (key u)
    simp only [map_mul, G.al_idem, hala] at h
    calc G.al (c1 u) * G.al (c1 u)
        = a * a * (G.al (c1 u) * G.al (c1 u)) := by rw [haa, one_mul]
      _ = a * G.al (c1 u) * (a * G.al (c1 u)) := by
            have hcomm : a * G.al (c1 u) = G.al (c1 u) * a := by
              rw [hadef]; exact G.al_comm G.x (c1 u)
            calc a * a * (G.al (c1 u) * G.al (c1 u))
                = a * ((a * G.al (c1 u)) * G.al (c1 u)) := by
                  simp [mul_assoc]
              _ = a * ((G.al (c1 u) * a) * G.al (c1 u)) := by rw [hcomm]
              _ = a * G.al (c1 u) * (a * G.al (c1 u)) := by simp [mul_assoc]
      _ = G.al u := h
  -- squaring is surjective, hence injective, on the (finite) image submonoid
  have ha1 : a = 1 := by
    let A : Submonoid M := MonoidHom.mrange G.al
    have hmem : ∀ u : M, G.al u ∈ A := fun u => ⟨u, rfl⟩
    have : Finite A := Subtype.finite
    let f : A → A := fun t => t * t
    have hsurj : Function.Surjective f := by
      rintro ⟨t, u, rfl⟩
      exact ⟨⟨G.al (c1 u), hmem _⟩, Subtype.ext (sq u)⟩
    have hinj : Function.Injective f := (Finite.injective_iff_surjective).2 hsurj
    have haA : a ∈ A := hmem G.x
    have h1A : (1 : M) ∈ A := A.one_mem
    have : (⟨a, haA⟩ : A) = ⟨1, h1A⟩ := by
      apply hinj
      apply Subtype.ext
      simpa [f] using haa
    exact congrArg Subtype.val this
  -- with `a = 1`, (e) says `c1 u * c1 u = al u`, and (c) is (e) applied to `c1 u`
  have hsq : ∀ u : M, c1 u * c1 u = G.al u := by
    intro u
    have hk := key u
    rw [ha1] at hk
    simpa using hk
  rw [eqC_iff]
  intro u
  calc c1 (G.al u) = c1 (c1 u * c1 u) := by rw [hsq]
    _ = c1 (c1 u) * c1 (c1 u) := ha _ _
    _ = G.al (c1 u) := hsq _

end Ctrl

end Crops
