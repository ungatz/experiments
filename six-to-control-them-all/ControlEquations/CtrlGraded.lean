import ControlEquations.CtrlDefs

/-!
# Graded-constant crops

A family of crops in which the whole prop is compressed into a single monoid.  The construction
is elementary and the point of it is only that it is flexible enough to separate several of the
control equations from each other.

Fix a monoid `M`, an idempotent monoid endomorphism `al : M →* M` whose image is commutative,
and an involution `x : M`.  The crop `gradedCrop` has

* `H 0 = PUnit` and `H n = M` for `n ≥ 1`;
* composition the multiplication of `M`, and `id_n = 1`;
* monoidal product `a + b = al a * al b` when both arities are positive, and the evident thing
  when one of them is `0`, so that the empty wire is a strict unit;
* every permutation acting as the identity;
* distinguished involution `x`.

Idempotence of `al` gives associativity of the product, and commutativity of its image gives
bifunctoriality and naturality of the symmetry.

Control data is given by two arity-independent functions `c0 c1 : M → M`, and the eight
equations then read as equations in `M`, with `u` and `v` ranging over `M`:

| equation | reads |
|---|---|
| (a) | `c1 (v * u) = c1 v * c1 u` |
| (b) | `c1 1 = 1` |
| (c) | `c1 (al u) = al (c1 u)` |
| (d) | `x * c0 1 * x = c1 1` and `al x * c0 u * al x = c1 u` |
| (e) | `c0 u * c1 u = al u` |
| (f) | `c0 u * c1 v = c1 v * c0 u` |
| (g) | `c1 x * c1 x * c1 x = 1` |
| (h) | always true |

These are the lemmas `eqA_iff` to `eqH_holds` below.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

/-! ### The hom-types -/

/-- The hom-types of a graded-constant prop: nothing in arity `0`, the monoid `M` above. -/
def ZH (M : Type) : ℕ → Type
  | 0 => PUnit
  | _ + 1 => M

variable {M : Type} [Monoid M]

/-- The scalar of a morphism (`1` in arity `0`). -/
def zElim : (n : ℕ) → ZH M n → M
  | 0, _ => 1
  | _ + 1, a => a

/-- The morphism with a given scalar. -/
def zMk : (n : ℕ) → M → ZH M n
  | 0, _ => PUnit.unit
  | _ + 1, s => s

@[simp] lemma zMk_zElim : ∀ (n : ℕ) (a : ZH M n), zMk n (zElim n a) = a
  | 0, _ => rfl
  | _ + 1, _ => rfl

lemma z_ext {n : ℕ} {a b : ZH M n} (h : zElim n a = zElim n b) : a = b := by
  rw [← zMk_zElim n a, h, zMk_zElim]

@[simp] lemma zElim_zMk_pos {n : ℕ} (h : n ≠ 0) (s : M) : zElim n (zMk n s) = s := by
  cases n with
  | zero => exact absurd rfl h
  | succ k => rfl

@[simp] lemma zElim_zero (a : ZH M 0) : zElim 0 a = 1 := rfl

lemma zElim_cst {m n : ℕ} (h : m = n) (a : ZH M m) : zElim n (h ▸ a) = zElim m a := by
  cases h; rfl

/-! ### The structure maps -/

/-- The scalar of a monoidal product, as a function of the two arities. -/
def tsel (al : M →* M) (m n : ℕ) (u v : M) : M :=
  if m = 0 then v else if n = 0 then u else al u * al v

variable (al : M →* M)

@[simp] lemma tsel_zero_left (n : ℕ) (u v : M) : tsel al 0 n u v = v := by simp [tsel]

lemma tsel_zero_right {m : ℕ} (hm : m ≠ 0) (u v : M) : tsel al m 0 u v = u := by
  simp [tsel, hm]

lemma tsel_pos {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (u v : M) :
    tsel al m n u v = al u * al v := by simp [tsel, hm, hn]

/-- Composition: multiply the scalars. -/
def zCmp {n : ℕ} (a b : ZH M n) : ZH M n := zMk n (zElim n a * zElim n b)

/-- Identity. -/
def zIdm (n : ℕ) : ZH M n := zMk n 1

/-- The monoidal product. -/
def zTn {m n : ℕ} (a : ZH M m) (b : ZH M n) : ZH M (m + n) :=
  zMk (m + n) (tsel al m n (zElim m a) (zElim n b))

/-- The (trivial) inclusion of the permutation prop. -/
def zIo {n : ℕ} (_ : PH n) : ZH M n := zIdm n

@[simp] lemma zElim_zCmp {n : ℕ} (a b : ZH M n) :
    zElim n (zCmp a b) = zElim n a * zElim n b := by
  cases n with
  | zero => simp [zCmp]
  | succ k => rfl

@[simp] lemma zElim_zIdm (n : ℕ) : zElim n (zIdm (M := M) n) = 1 := by
  cases n with
  | zero => rfl
  | succ k => rfl

@[simp] lemma zElim_zTn {m n : ℕ} (a : ZH M m) (b : ZH M n) :
    zElim (m + n) (zTn al a b) = tsel al m n (zElim m a) (zElim n b) := by
  by_cases h : m + n = 0
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst hm; subst hn
    simp
  · rw [zTn, zElim_zMk_pos h]

/-! ### The parameters of the construction -/

/-- The data of a graded-constant crop: an idempotent endomorphism with commutative image,
and an involution. -/
structure GradedData (M : Type) [Monoid M] where
  /-- the idempotent endomorphism defining the monoidal product -/
  al : M →* M
  /-- idempotence -/
  al_idem : ∀ g : M, al (al g) = al g
  /-- the image of `al` is commutative -/
  al_comm : ∀ g h : M, al g * al h = al h * al g
  /-- the distinguished involution -/
  x : M
  /-- it is an involution -/
  x_invol : x * x = 1

namespace GradedData

variable (G : GradedData M)

lemma tsel_symm {m n : ℕ} (a : ZH M m) (b : ZH M n) :
    tsel G.al m n (zElim m a) (zElim n b) = tsel G.al n m (zElim n b) (zElim m a) := by
  by_cases hm : m = 0 <;> by_cases hn : n = 0
  · subst hm; subst hn; simp
  · subst hm; rw [tsel_zero_left, tsel_zero_right _ hn]
  · subst hn; rw [tsel_zero_left, tsel_zero_right _ hm]
  · rw [tsel_pos _ hm hn, tsel_pos _ hn hm, G.al_comm]

lemma al_al_mul (u v : M) : G.al (G.al u * G.al v) = G.al u * G.al v := by
  rw [map_mul, G.al_idem, G.al_idem]

lemma al_swap (a b c d : M) :
    G.al a * G.al b * (G.al c * G.al d) = G.al a * G.al c * (G.al b * G.al d) := by
  rw [mul_assoc, ← mul_assoc (G.al b), G.al_comm b c, mul_assoc, ← mul_assoc]

/-- The graded-constant endo-prop. -/
def endoProp : EndoProp where
  H := ZH M
  cmp := zCmp
  idm := zIdm
  tn := zTn G.al
  io := zIo
  cmp_assoc a b c := z_ext (by simp [mul_assoc])
  idm_cmp a := z_ext (by simp)
  cmp_idm a := z_ext (by simp)
  tn_cmp {m n} a b c d := by
    refine z_ext ?_
    simp only [zElim_zTn, zElim_zCmp]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all [tsel]
    exact G.al_swap _ _ _ _
  tn_idm m n := by
    refine z_ext ?_
    simp only [zElim_zTn, zElim_zIdm]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all [tsel]
  tn_assoc {m n p} a b c := by
    refine z_ext ?_
    rw [zElim_cst]
    simp only [zElim_zTn]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> by_cases hp : p = 0 <;>
      simp_all [tsel, G.al_al_mul, mul_assoc]
  tn_idm_right {m} a := by
    refine z_ext ?_
    simp only [zElim_zTn, zElim_zIdm]
    by_cases hm : m = 0
    · subst hm; simp [tsel]
    · simp [tsel, hm]
  tn_idm_left {m} a := by
    refine z_ext ?_
    rw [zElim_cst]
    simp only [zElim_zTn, zElim_zIdm, tsel_zero_left]
  io_cmp p q := z_ext (by simp [zIo])
  io_one n := rfl
  io_tn {m n} p q := by
    refine z_ext ?_
    simp only [zIo, zElim_zTn, zElim_zIdm]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all [tsel]
  io_swap_nat {m n} a b := by
    refine z_ext ?_
    simp only [zElim_zCmp, zIo, zElim_zIdm, one_mul, mul_one, zElim_cst, zElim_zTn]
    exact G.tsel_symm a b

/-- The graded-constant crop. -/
def crop : Crop where
  toEndoProp := G.endoProp
  invol := G.x
  invol_invol := by
    show zCmp (G.x : ZH M 1) G.x = zIdm 1
    exact z_ext (by simpa [zCmp, zIdm] using G.x_invol)

@[simp] lemma crop_cmp {n : ℕ} (a b : ZH M n) : (G.crop).cmp a b = zCmp a b := rfl

@[simp] lemma crop_idm (n : ℕ) : (G.crop).idm n = zIdm n := rfl

@[simp] lemma crop_tn {m n : ℕ} (a : ZH M m) (b : ZH M n) :
    (G.crop).tn a b = zTn G.al a b := rfl

@[simp] lemma crop_io {n : ℕ} (p : PH n) : (G.crop).io p = zIdm n := rfl

@[simp] lemma crop_invol : (G.crop).invol = G.x := rfl

/-! ### Control data -/

/-- Control data given by two arity-independent functions on the monoid. -/
def ctrl (c0 c1 : M → M) : Data G.crop where
  C0 n a := zMk (1 + n) (c0 (zElim n a))
  C1 n a := zMk (1 + n) (c1 (zElim n a))

variable (c0 c1 : M → M)

@[simp] lemma zElim_C1 (n : ℕ) (a : ZH M n) :
    zElim (1 + n) ((G.ctrl c0 c1).C1 n a) = c1 (zElim n a) :=
  zElim_zMk_pos (by omega) _

@[simp] lemma zElim_C0 (n : ℕ) (a : ZH M n) :
    zElim (1 + n) ((G.ctrl c0 c1).C0 n a) = c0 (zElim n a) :=
  zElim_zMk_pos (by omega) _

/-! ### The eight equations, read off in the monoid -/

lemma zElim_cropCst {m n : ℕ} (h : m = n) (a : ZH M m) :
    zElim n ((G.crop).cst h a) = zElim m a := by
  cases h; rfl

lemma eqA_iff : (G.ctrl c0 c1).EqA ↔ ∀ u v : M, c1 (v * u) = c1 v * c1 u := by
  constructor
  · intro h u v
    have h' := congrArg (zElim (M := M) (1 + 1)) (h 1 (zMk 1 u : ZH M 1) (zMk 1 v))
    simpa using h'
  · intro h n f g
    refine z_ext ?_
    simp only [zElim_C1, crop_cmp, zElim_zCmp]
    cases n with
    | zero => simpa using h 1 1
    | succ k => simpa using h _ _

lemma eqB_iff : (G.ctrl c0 c1).EqB ↔ c1 1 = 1 := by
  constructor
  · intro h
    have h' := congrArg (zElim (M := M) (1 + 1)) (h 1)
    simpa using h'
  · intro h n
    refine z_ext ?_
    simp only [zElim_C1, crop_idm, zElim_zIdm]
    exact h

lemma eqC_iff : (G.ctrl c0 c1).EqC ↔ ∀ u : M, c1 (G.al u) = G.al (c1 u) := by
  constructor
  · intro h u
    have h' := congrArg (zElim (M := M) (1 + (1 + 1))) (h 1 1 (zMk 1 u : ZH M 1))
    rw [G.zElim_cropCst] at h'
    simp only [zElim_C1, crop_tn, zElim_zTn, crop_idm, zElim_zIdm] at h'
    rw [tsel_pos _ (by omega) (by omega), tsel_pos _ (by omega) (by omega)] at h'
    simpa using h'
  · intro h n m f
    refine z_ext ?_
    rw [G.zElim_cropCst]
    simp only [zElim_C1, crop_tn, zElim_zTn, crop_idm, zElim_zIdm]
    by_cases hn : n = 0 <;> by_cases hm : m = 0
    · subst hn; subst hm; simp [tsel]
    · subst hn
      rw [tsel_zero_left, tsel_pos _ (by omega) hm, map_one, mul_one, zElim_zero]
      have := h 1
      rw [map_one] at this
      exact this
    · subst hm
      rw [tsel_zero_right _ hn, tsel_zero_right _ (by omega)]
    · rw [tsel_pos _ hn hm, tsel_pos _ (by omega) hm, map_one, mul_one, mul_one]
      exact h _

lemma eqD_iff : (G.ctrl c0 c1).EqD ↔
    ((G.x * c0 1 * G.x = c1 1) ∧ ∀ u : M, G.al G.x * c0 u * G.al G.x = c1 u) := by
  have hx : ∀ n : ℕ, zElim (M := M) (1 + n) (xw (P := G.crop) n) =
      if n = 0 then G.x else G.al G.x := by
    intro n
    unfold xw
    rw [crop_invol, crop_idm, crop_tn, zElim_zTn]
    by_cases hn : n = 0
    · subst hn
      rw [tsel_zero_right _ (by omega), if_pos rfl]
      rfl
    · rw [tsel_pos _ (by omega) hn, zElim_zIdm, map_one, mul_one, if_neg hn]
      rfl
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h' := congrArg (zElim (M := M) (1 + 0)) (h 0 PUnit.unit)
      simp only [crop_cmp, zElim_zCmp, zElim_C0, zElim_C1, zElim_zero, hx] at h'
      simpa [mul_assoc] using h'
    · intro u
      have h' := congrArg (zElim (M := M) (1 + 1)) (h 1 (zMk 1 u : ZH M 1))
      simp only [crop_cmp, zElim_zCmp, zElim_C0, zElim_C1, hx] at h'
      simpa [mul_assoc] using h'
  · rintro ⟨h0, h1⟩ n f
    refine z_ext ?_
    simp only [crop_cmp, zElim_zCmp, zElim_C0, zElim_C1, hx]
    cases n with
    | zero => simpa [mul_assoc] using h0
    | succ k => simpa [mul_assoc] using h1 (zElim (k + 1) f)

lemma eqE_iff : (G.ctrl c0 c1).EqE ↔ ∀ u : M, c0 u * c1 u = G.al u := by
  have hr : ∀ (n : ℕ) (f : ZH M n),
      zElim (M := M) (1 + n) ((G.crop).tn ((G.crop).idm 1) f) =
        if n = 0 then 1 else G.al (zElim n f) := by
    intro n f
    rw [crop_idm, crop_tn, zElim_zTn]
    by_cases hn : n = 0
    · subst hn
      rw [tsel_zero_right _ (by omega), zElim_zIdm, if_pos rfl]
    · rw [tsel_pos _ (by omega) hn, zElim_zIdm, map_one, one_mul, if_neg hn]
  constructor
  · intro h u
    have h' := congrArg (zElim (M := M) (1 + 1)) (h 1 (zMk 1 u : ZH M 1))
    simp only [crop_cmp, zElim_zCmp, zElim_C0, zElim_C1, hr] at h'
    simpa using h'
  · intro h n f
    refine z_ext ?_
    simp only [crop_cmp, zElim_zCmp, zElim_C0, zElim_C1, hr]
    cases n with
    | zero =>
      have := h 1
      rw [map_one] at this
      simpa using this
    | succ k => simpa using h (zElim (k + 1) f)

lemma eqF_iff : (G.ctrl c0 c1).EqF ↔ ∀ u v : M, c0 u * c1 v = c1 v * c0 u := by
  constructor
  · intro h u v
    have h' := congrArg (zElim (M := M) (1 + 1)) (h 1 (zMk 1 u : ZH M 1) (zMk 1 v))
    simpa using h'
  · intro h n f₁ f₂
    refine z_ext ?_
    simp only [crop_cmp, zElim_zCmp, zElim_C0, zElim_C1]
    exact h _ _

lemma eqG_iff : (G.ctrl c0 c1).EqG ↔ c1 G.x * (c1 G.x * c1 G.x) = 1 := by
  have hsw : zElim (M := M) 2 (sw (P := G.crop)) = 1 := by
    unfold sw
    rw [crop_io, zElim_zIdm]
  have hcx : zElim (M := M) 2 ((G.ctrl c0 c1).C1 1 ((G.crop).invol)) = c1 G.x := by
    show zElim (M := M) (1 + 1) _ = _
    rw [zElim_C1]
    rfl
  unfold Data.EqG
  constructor
  · intro h
    have h' := congrArg (zElim (M := M) 2) h
    simp only [crop_cmp, zElim_zCmp, hsw, hcx, one_mul, mul_one] at h'
    exact h'
  · intro h
    refine z_ext (M := M) (n := 2) ?_
    simp only [crop_cmp, zElim_zCmp, hsw, hcx, one_mul, mul_one]
    exact h

/-- In every graded-constant crop, their equation (h) holds for every control datum: the
symmetry inclusion is trivial. -/
lemma eqH_holds : (G.ctrl c0 c1).EqH :=
  eqH_of_trivial_symmetry _ (fun _ _ => rfl)

end GradedData

end Ctrl

end Crops
