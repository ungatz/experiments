import ControlEquations.CtrlInv

/-!
# Deforming control by a central character

Before their (c) was derived in general, the search for a crop separating it was reduced to a
single piece of data: a central character `chi` of exponent two, into the centre, whose control
commutes with the symmetry, and which stays nontrivial after padding by a wire.  This file
carries out that reduction.

`ControlEquations.CtrlStrengthConseq` then shows the data cannot exist, since (c) is a theorem.
The reduction is kept because it is what made the derivation findable, and because the
non-existence statement is stated in its vocabulary.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

attribute [local instance] homMonoid

variable {P : Crop}

/-- A **central character** on a crop: a monoid map from the scalars `H 0` into the centre of
the arity-one hom-monoid, of exponent two. -/
structure CentralChar (P : Crop) where
  /-- the underlying map -/
  chi : P.H 0 → P.H 1
  /-- it preserves the identity -/
  map_one : chi (P.idm 0) = P.idm 1
  /-- it preserves composition -/
  map_mul : ∀ f g : P.H 0, chi (P.cmp f g) = P.cmp (chi f) (chi g)
  /-- its values are central -/
  central : ∀ (f : P.H 0) (u : P.H 1), P.cmp (chi f) u = P.cmp u (chi f)
  /-- its values are involutions -/
  invol : ∀ f : P.H 0, P.cmp (chi f) (chi f) = P.idm 1

/-- The deformation of control data by a central character: arity `0` only. -/
def Data.twist (D : Data P) (X : CentralChar P) : Data P where
  C0 n :=
    match n with
    | 0 => fun f => P.cmp (D.C0 0 f) (X.chi f)
    | k + 1 => D.C0 (k + 1)
  C1 n :=
    match n with
    | 0 => fun f => P.cmp (D.C1 0 f) (X.chi f)
    | k + 1 => D.C1 (k + 1)

@[simp] lemma twist_C0_zero (D : Data P) (X : CentralChar P) (f : P.H 0) :
    (D.twist X).C0 0 f = P.cmp (D.C0 0 f) (X.chi f) := rfl

@[simp] lemma twist_C1_zero (D : Data P) (X : CentralChar P) (f : P.H 0) :
    (D.twist X).C1 0 f = P.cmp (D.C1 0 f) (X.chi f) := rfl

@[simp] lemma twist_C0_succ (D : Data P) (X : CentralChar P) (k : ℕ) (f : P.H (k + 1)) :
    (D.twist X).C0 (k + 1) f = D.C0 (k + 1) f := rfl

@[simp] lemma twist_C1_succ (D : Data P) (X : CentralChar P) (k : ℕ) (f : P.H (k + 1)) :
    (D.twist X).C1 (k + 1) f = D.C1 (k + 1) f := rfl

lemma twist_C1_pos (D : Data P) (X : CentralChar P) {n : ℕ} (hn : n ≠ 0) (f : P.H n) :
    (D.twist X).C1 n f = D.C1 n f := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

lemma twist_C0_pos (D : Data P) (X : CentralChar P) {n : ℕ} (hn : n ≠ 0) (f : P.H n) :
    (D.twist X).C0 n f = D.C0 n f := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

/-! ### The six equations the deformation cannot see -/

variable {D : Data P} {X : CentralChar P}

theorem twist_EqA (ha : D.EqA) : (D.twist X).EqA := by
  intro n f g
  rcases eq_or_ne n 0 with rfl | hn
  · show P.cmp (D.C1 0 (P.cmp g f)) (X.chi (P.cmp g f))
        = P.cmp (P.cmp (D.C1 0 g) (X.chi g)) (P.cmp (D.C1 0 f) (X.chi f))
    rw [ha 0 f g, X.map_mul]
    show (D.C1 0 g * D.C1 0 f) * (X.chi g * X.chi f)
        = (D.C1 0 g * X.chi g) * (D.C1 0 f * X.chi f)
    have hc : X.chi g * D.C1 0 f = D.C1 0 f * X.chi g := X.central g _
    calc (D.C1 0 g * D.C1 0 f) * (X.chi g * X.chi f)
        = D.C1 0 g * ((D.C1 0 f * X.chi g) * X.chi f) := by simp [mul_assoc]
      _ = D.C1 0 g * ((X.chi g * D.C1 0 f) * X.chi f) := by rw [hc]
      _ = (D.C1 0 g * X.chi g) * (D.C1 0 f * X.chi f) := by simp [mul_assoc]
  · rw [twist_C1_pos D X hn, twist_C1_pos D X hn, twist_C1_pos D X hn]
    exact ha n f g

theorem twist_EqB (hb : D.EqB) : (D.twist X).EqB := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · show P.cmp (D.C1 0 (P.idm 0)) (X.chi (P.idm 0)) = P.idm 1
    rw [hb 0, X.map_one, P.cmp_idm]
  · rw [twist_C1_pos D X hn]
    exact hb n

theorem twist_EqD (hd : D.EqD) : (D.twist X).EqD := by
  intro n f
  rcases eq_or_ne n 0 with rfl | hn
  · have hx : xw (P := P) 0 = P.invol := P.tn_idm_right P.invol
    show P.cmp (xw (P := P) 0) (P.cmp (P.cmp (D.C0 0 f) (X.chi f)) (xw (P := P) 0))
        = P.cmp (D.C1 0 f) (X.chi f)
    have hcen : P.cmp (X.chi f) (xw (P := P) 0) = P.cmp (xw (P := P) 0) (X.chi f) := by
      rw [hx]; exact X.central f P.invol
    have h := hd 0 f
    show xw (P := P) 0 * ((D.C0 0 f * X.chi f) * xw (P := P) 0) = D.C1 0 f * X.chi f
    have hcen' : X.chi f * xw (P := P) 0 = xw (P := P) 0 * X.chi f := hcen
    calc xw (P := P) 0 * ((D.C0 0 f * X.chi f) * xw (P := P) 0)
        = xw (P := P) 0 * (D.C0 0 f * (X.chi f * xw (P := P) 0)) := by simp [mul_assoc]
      _ = xw (P := P) 0 * (D.C0 0 f * (xw (P := P) 0 * X.chi f)) := by rw [hcen']
      _ = (xw (P := P) 0 * (D.C0 0 f * xw (P := P) 0)) * X.chi f := by simp [mul_assoc]
      _ = D.C1 0 f * X.chi f := by rw [show xw (P := P) 0 * (D.C0 0 f * xw (P := P) 0)
            = D.C1 0 f from h]
  · rw [twist_C0_pos D X hn, twist_C1_pos D X hn]
    exact hd n f

theorem twist_EqE (he : D.EqE) : (D.twist X).EqE := by
  intro n f
  rcases eq_or_ne n 0 with rfl | hn
  · show (D.C0 0 f * X.chi f) * (D.C1 0 f * X.chi f) = P.tn (P.idm 1) f
    have hc : X.chi f * D.C1 0 f = D.C1 0 f * X.chi f := X.central f _
    calc (D.C0 0 f * X.chi f) * (D.C1 0 f * X.chi f)
        = D.C0 0 f * ((X.chi f * D.C1 0 f) * X.chi f) := by simp [mul_assoc]
      _ = D.C0 0 f * ((D.C1 0 f * X.chi f) * X.chi f) := by rw [hc]
      _ = (D.C0 0 f * D.C1 0 f) * (X.chi f * X.chi f) := by simp [mul_assoc]
      _ = P.tn (P.idm 1) f := by
          rw [show X.chi f * X.chi f = 1 from X.invol f, mul_one]
          exact he 0 f
  · rw [twist_C0_pos D X hn, twist_C1_pos D X hn]
    exact he n f

theorem twist_EqF (hf : D.EqF) : (D.twist X).EqF := by
  intro n f₁ f₂
  rcases eq_or_ne n 0 with rfl | hn
  · show (D.C0 0 f₁ * X.chi f₁) * (D.C1 0 f₂ * X.chi f₂)
        = (D.C1 0 f₂ * X.chi f₂) * (D.C0 0 f₁ * X.chi f₁)
    have h1 : X.chi f₁ * D.C1 0 f₂ = D.C1 0 f₂ * X.chi f₁ := X.central f₁ _
    have h2 : X.chi f₂ * D.C0 0 f₁ = D.C0 0 f₁ * X.chi f₂ := X.central f₂ _
    have h3 : X.chi f₁ * X.chi f₂ = X.chi f₂ * X.chi f₁ := X.central f₁ _
    have h4 : D.C0 0 f₁ * D.C1 0 f₂ = D.C1 0 f₂ * D.C0 0 f₁ := hf 0 f₁ f₂
    calc (D.C0 0 f₁ * X.chi f₁) * (D.C1 0 f₂ * X.chi f₂)
        = D.C0 0 f₁ * ((X.chi f₁ * D.C1 0 f₂) * X.chi f₂) := by simp [mul_assoc]
      _ = D.C0 0 f₁ * ((D.C1 0 f₂ * X.chi f₁) * X.chi f₂) := by rw [h1]
      _ = (D.C0 0 f₁ * D.C1 0 f₂) * (X.chi f₁ * X.chi f₂) := by simp [mul_assoc]
      _ = (D.C1 0 f₂ * D.C0 0 f₁) * (X.chi f₂ * X.chi f₁) := by rw [h4, h3]
      _ = D.C1 0 f₂ * ((D.C0 0 f₁ * X.chi f₂) * X.chi f₁) := by simp [mul_assoc]
      _ = D.C1 0 f₂ * ((X.chi f₂ * D.C0 0 f₁) * X.chi f₁) := by rw [h2]
      _ = (D.C1 0 f₂ * X.chi f₂) * (D.C0 0 f₁ * X.chi f₁) := by simp [mul_assoc]
  · rw [twist_C0_pos D X hn, twist_C1_pos D X hn]
    exact hf n f₁ f₂

theorem twist_EqG (hg : D.EqG) : (D.twist X).EqG := hg

/-! ### The two equations it does see -/

/-- The deformation preserves (h) exactly when the control of the character is central for the
symmetry. -/
theorem twist_EqH (ha : D.EqA) (hh : D.EqH)
    (hsigma : ∀ f : P.H 0,
      P.cmp (sww (P := P) 0) (D.C1 1 (X.chi f)) = P.cmp (D.C1 1 (X.chi f)) (sww (P := P) 0)) :
    (D.twist X).EqH := by
  intro n f
  rcases eq_or_ne n 0 with rfl | hn
  · show P.cmp (sww (P := P) 0) (D.C1 1 (P.cmp (D.C1 0 f) (X.chi f)))
        = P.cmp (D.C1 1 (P.cmp (D.C1 0 f) (X.chi f))) (sww (P := P) 0)
    rw [ha 1 (X.chi f) (D.C1 0 f)]
    have h1 := hh 0 f
    have h2 := hsigma f
    show sww (P := P) 0 * (D.C1 1 (D.C1 0 f) * D.C1 1 (X.chi f))
        = (D.C1 1 (D.C1 0 f) * D.C1 1 (X.chi f)) * sww (P := P) 0
    calc sww (P := P) 0 * (D.C1 1 (D.C1 0 f) * D.C1 1 (X.chi f))
        = (sww (P := P) 0 * D.C1 1 (D.C1 0 f)) * D.C1 1 (X.chi f) := by rw [mul_assoc]
      _ = (D.C1 1 (D.C1 0 f) * sww (P := P) 0) * D.C1 1 (X.chi f) := by
            rw [show sww (P := P) 0 * D.C1 1 (D.C1 0 f)
              = D.C1 1 (D.C1 0 f) * sww (P := P) 0 from h1]
      _ = D.C1 1 (D.C1 0 f) * (sww (P := P) 0 * D.C1 1 (X.chi f)) := by rw [mul_assoc]
      _ = D.C1 1 (D.C1 0 f) * (D.C1 1 (X.chi f) * sww (P := P) 0) := by
            rw [show sww (P := P) 0 * D.C1 1 (X.chi f)
              = D.C1 1 (X.chi f) * sww (P := P) 0 from h2]
      _ = (D.C1 1 (D.C1 0 f) * D.C1 1 (X.chi f)) * sww (P := P) 0 := by rw [mul_assoc]
  · rw [twist_C1_pos D X hn, twist_C1_pos D X (by omega)]
    exact hh n f

/-- The deformation breaks (c) as soon as the character survives padding by one wire — provided
the padded control is cancellable, which it is in any reversible crop. -/
theorem twist_not_EqC (hc : D.EqC) (f₀ : P.H 0)
    (hinv : IsInvertible (P := P) (P.tn (D.C1 0 f₀) (P.idm 1)))
    (hpad : P.tn (X.chi f₀) (P.idm 1) ≠ P.idm 2) : ¬ (D.twist X).EqC := by
  intro hc'
  have h0 := hc 0 1 f₀
  have h1 := hc' 0 1 f₀
  rw [twist_C1_pos D X (by omega), twist_C1_zero] at h1
  rw [h0] at h1
  -- both sides are casts of morphisms on two wires; strip the cast
  have h2 : P.tn (D.C1 0 f₀) (P.idm 1)
      = P.tn (P.cmp (D.C1 0 f₀) (X.chi f₀)) (P.idm 1) := P.cst_inj _ h1
  rw [P.tn_cmp_idm_right] at h2
  obtain ⟨g, hg1, hg2⟩ := hinv
  apply hpad
  calc P.tn (X.chi f₀) (P.idm 1)
      = P.cmp (P.cmp g (P.tn (D.C1 0 f₀) (P.idm 1))) (P.tn (X.chi f₀) (P.idm 1)) := by
        rw [hg2, P.idm_cmp]
    _ = P.cmp g (P.cmp (P.tn (D.C1 0 f₀) (P.idm 1)) (P.tn (X.chi f₀) (P.idm 1))) :=
        P.cmp_assoc _ _ _
    _ = P.cmp g (P.tn (D.C1 0 f₀) (P.idm 1)) := by rw [← h2]
    _ = P.idm 2 := hg2

/-! ### The reduction -/

/-- Cell (c) reduces to the existence of a padding-nontrivial, symmetry-central
character.**  If a controllable prop carries control data satisfying all eight equations
together with a central character of exponent two whose control commutes with the symmetry and
whose padding by one wire is nontrivial (and whose padded control is cancellable, as it is in
any reversible crop), then the deformed data satisfies their (a), (b), (d), (e), (f), (g), (h)
and fails their (c) — a witness for the last open cell.

This is a sufficient criterion, not a characterisation; the cell itself is left open in
the derivation of (c). -/
theorem twist_is_eqC_witness (ha : D.EqA) (hb : D.EqB) (hc : D.EqC) (hd : D.EqD) (he : D.EqE)
    (hf : D.EqF) (hg : D.EqG) (hh : D.EqH)
    (hsigma : ∀ f : P.H 0,
      P.cmp (sww (P := P) 0) (D.C1 1 (X.chi f)) = P.cmp (D.C1 1 (X.chi f)) (sww (P := P) 0))
    (f₀ : P.H 0) (hinv : IsInvertible (P := P) (P.tn (D.C1 0 f₀) (P.idm 1)))
    (hpad : P.tn (X.chi f₀) (P.idm 1) ≠ P.idm 2) :
    (D.twist X).EqA ∧ (D.twist X).EqB ∧ ¬ (D.twist X).EqC ∧ (D.twist X).EqD ∧
      (D.twist X).EqE ∧ (D.twist X).EqF ∧ (D.twist X).EqG ∧ (D.twist X).EqH :=
  ⟨twist_EqA ha, twist_EqB hb, twist_not_EqC hc f₀ hinv hpad, twist_EqD hd, twist_EqE he,
    twist_EqF hf, twist_EqG hg, twist_EqH ha hh hsigma⟩

end Ctrl

end Crops
