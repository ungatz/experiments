import ControlEquations.CtrlDefs

/-!
# Commutativity holds automatically on invertible arguments

Their equation (f), commutativity of the two colours of control, follows from their (a), (b),
(d) and (e) whenever the two morphisms involved are invertible.  Over a crop all of whose
morphisms are invertible, which is the reversible setting their Remark 20 singles out, (f) is
therefore a theorem rather than an axiom.

One consequence is a constraint on models: any crop separating (f) from the other seven
equations has to use non-invertible morphisms, which is what the six-element monoid of
`ControlEquations.CtrlModels` does.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

/-- The hom-monoid of a crop at arity `n`: composition as multiplication, identity as unit. -/
def homMonoid (P : Crop) (n : ℕ) : Monoid (P.H n) where
  mul := P.cmp
  one := P.idm n
  mul_assoc := P.cmp_assoc
  one_mul := P.idm_cmp
  mul_one := P.cmp_idm

attribute [local instance] homMonoid

variable {P : Crop}

theorem hom_mul_def {n : ℕ} (a b : P.H n) : a * b = P.cmp a b := rfl

theorem hom_one_def (n : ℕ) : (1 : P.H n) = P.idm n := rfl

/-- Two-sided invertibility of a morphism of a crop. -/
def IsInvertible {n : ℕ} (f : P.H n) : Prop :=
  ∃ g : P.H n, P.cmp f g = P.idm n ∧ P.cmp g f = P.idm n

/-- Cancellation in a monoid: an element with a left inverse cancels on the left, an element
with a right inverse cancels on the right. -/
theorem mul_cancel_both {M : Type*} [Monoid M] {u u' w w' p q : M}
    (hu : u' * u = 1) (hw : w * w' = 1) (h : u * p * w = u * q * w) : p = q := by
  have h1 : u' * (u * p * w) * w' = u' * (u * q * w) * w' := by rw [h]
  calc p = u' * u * p * (w * w') := by rw [hu, hw, one_mul, mul_one]
    _ = u' * (u * p * w) * w' := by simp [mul_assoc]
    _ = u' * (u * q * w) * w' := h1
    _ = u' * u * q * (w * w') := by simp [mul_assoc]
    _ = q := by rw [hu, hw, one_mul, mul_one]

/-- **Their equation (f) is a consequence of their (a), (b), (d), (e) on invertible morphisms.**

In any controllable prop with control data satisfying (a) composition, (b) identity, (d) colour
change and (e) complementarity, the two colours of control commute at any pair of *invertible*
morphisms.  Hence a model witnessing the logical independence of (f) is forced to use
non-invertible morphisms. -/
theorem eqF_of_invertible {D : Data P} (ha : D.EqA) (hb : D.EqB) (hd : D.EqD) (he : D.EqE)
    {n : ℕ} (f₁ f₂ : P.H n) (h₁ : IsInvertible f₁) (h₂ : IsInvertible f₂) :
    P.cmp (D.C0 n f₁) (D.C1 n f₂) = P.cmp (D.C1 n f₂) (D.C0 n f₁) := by
  obtain ⟨g₁, hg₁r, hg₁l⟩ := h₁
  obtain ⟨g₂, hg₂r, hg₂l⟩ := h₂
  set X : P.H (1 + n) := xw n with hX
  set K : P.H n → P.H (1 + n) := D.C1 n with hK
  set C : P.H n → P.H (1 + n) := D.C0 n with hCd
  set I : P.H n → P.H (1 + n) := fun f => P.tn (P.idm 1) f with hI
  -- `X` is an involution
  have hXX : X * X = 1 := by
    show P.cmp (xw n) (xw n) = P.idm (1 + n)
    unfold xw
    rw [← P.tn_cmp, P.invol_invol, P.cmp_idm, P.tn_idm]
  -- (d) rewritten: `C f = X * K f * X`
  have hCX : ∀ f : P.H n, C f = X * K f * X := by
    intro f
    have h : X * (C f * X) = K f := hd n f
    have h' : X * C f * X = K f := by rw [mul_assoc]; exact h
    calc C f = 1 * C f * 1 := by rw [one_mul, mul_one]
      _ = X * X * C f * (X * X) := by rw [hXX]
      _ = X * (X * C f * X) * X := by simp [mul_assoc]
      _ = X * K f * X := by rw [h']
  -- (a) : `K` is multiplicative
  have hKmul : ∀ a b : P.H n, K (a * b) = K a * K b := fun a b => ha n b a
  -- hence so is `C`
  have hCmul : ∀ a b : P.H n, C (a * b) = C a * C b := by
    intro a b
    rw [hCX, hCX, hCX, hKmul]
    calc X * (K a * K b) * X = X * K a * (X * X) * (K b * X) := by
          rw [hXX]; simp [mul_assoc]
      _ = X * K a * X * (X * K b * X) := by simp [mul_assoc]
  -- (b) : `K 1 = 1`
  have hK1 : K (1 : P.H n) = 1 := hb n
  -- `I` is multiplicative
  have hImul : ∀ a b : P.H n, I a * I b = I (a * b) := by
    intro a b
    show P.cmp (P.tn (P.idm 1) a) (P.tn (P.idm 1) b) = P.tn (P.idm 1) (P.cmp a b)
    rw [← P.tn_cmp, P.cmp_idm]
  -- (e)
  have hE : ∀ f : P.H n, C f * K f = I f := fun f => he n f
  -- invertibility of `K f₁`, `K f₂`, and hence of `C f₁`, `C f₂`
  have hKinv : ∀ (a a' : P.H n), P.cmp a a' = P.idm n → K a * K a' = 1 := by
    intro a a' h
    rw [← hKmul]
    show K (P.cmp a a') = 1
    rw [h]
    exact hK1
  have hCleft : C f₂ * (X * K g₂ * X) = 1 := by
    rw [hCX]
    calc X * K f₂ * X * (X * K g₂ * X) = X * (K f₂ * (X * X) * K g₂) * X := by
          simp [mul_assoc]
      _ = X * (K f₂ * K g₂) * X := by rw [hXX, mul_one]
      _ = X * 1 * X := by rw [hKinv f₂ g₂ hg₂r]
      _ = 1 := by rw [mul_one, hXX]
  have hCright : (X * K g₂ * X) * C f₂ = 1 := by
    rw [hCX]
    calc X * K g₂ * X * (X * K f₂ * X) = X * (K g₂ * (X * X) * K f₂) * X := by
          simp [mul_assoc]
      _ = X * (K g₂ * K f₂) * X := by rw [hXX, mul_one]
      _ = X * 1 * X := by rw [hKinv g₂ f₂ hg₂l]
      _ = 1 := by rw [mul_one, hXX]
  -- the key computation, at the composite `f₂ * f₁`
  have hkey : C f₂ * (C f₁ * K f₂) * K f₁ = C f₂ * (K f₂ * C f₁) * K f₁ := by
    have h1 : C (f₂ * f₁) * K (f₂ * f₁) = I (f₂ * f₁) := hE _
    rw [hCmul, hKmul, ← hImul, ← hE f₂, ← hE f₁] at h1
    calc C f₂ * (C f₁ * K f₂) * K f₁ = C f₂ * C f₁ * (K f₂ * K f₁) := by simp [mul_assoc]
      _ = C f₂ * K f₂ * (C f₁ * K f₁) := h1
      _ = C f₂ * (K f₂ * C f₁) * K f₁ := by simp [mul_assoc]
  have := mul_cancel_both (u := C f₂) (u' := X * K g₂ * X) (w := K f₁)
    (w' := K g₁) hCright (hKinv f₁ g₁ hg₁r) hkey
  exact this

/-- **Over a crop all of whose morphisms are invertible — the reversible setting that motivates
their construction — two of their eight equations are redundant:** (b) and (f) both follow from
(a), (d) and (e).

Scope: this is a statement about the *equational presentation* of their Definition 6 restricted
to the class of crops whose morphisms are all invertible.  It is not a statement about their
structural minimality result. -/
theorem eqB_and_eqF_of_groupoid {D : Data P}
    (hinv : ∀ (n : ℕ) (f : P.H n), IsInvertible f)
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) : D.EqB ∧ D.EqF :=
  ⟨eqB_of_eqA_eqE ha he,
    fun n f₁ f₂ =>
      eqF_of_invertible ha (eqB_of_eqA_eqE ha he) hd he f₁ f₂ (hinv n f₁) (hinv n f₂)⟩

end Ctrl

end Crops
