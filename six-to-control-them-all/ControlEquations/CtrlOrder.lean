import ControlEquations.CtrlComm

/-!
# The order of the two controls in complementarity

Definition 6 writes complementarity as `C0 f ∘ C1 f = id₁ + f`.  Figure 1 draws the negative
control first and the positive control second, which under the convention fixed by (a), where the
gate drawn first is applied first, depicts `C1 f ∘ C0 f = id₁ + f`.  The two forms agree as soon
as (f) is available, since (f) makes the two control values commute, so the theory is the same
whichever is taken.

This file records that, and checks that the two results which use complementarity *without* (f)
go through under either form: the derivation of (b) from (a) and (e), and the obstruction saying
that an involution commuting with the symmetry is stably trivial.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

attribute [local instance] homMonoid

variable {P : Crop}

/-- Complementarity with the two controls in the order Figure 1 draws them. -/
def Data.EqE' (D : Data P) : Prop :=
  ∀ (n : ℕ) (f : P.H n), P.cmp (D.C1 n f) (D.C0 n f) = P.tn (P.idm 1) f

/-- Under (f) the two forms of complementarity are interchangeable, so the eight equations
present the same theory whichever is used. -/
theorem eqE_iff_eqE'_of_eqF {D : Data P} (hf : D.EqF) : D.EqE ↔ D.EqE' := by
  constructor <;> intro he n f
  · rw [← hf n f f]; exact he n f
  · rw [hf n f f]; exact he n f

/-- (b) follows from (a) together with complementarity in the order Figure 1 draws it, exactly as
it follows from (a) and the form written in Definition 6. -/
theorem eqB_of_eqA_eqE' {D : Data P} (ha : D.EqA) (he : D.EqE') : D.EqB := by
  intro n
  set u : P.H (1 + n) := D.C1 n (P.idm n) with hu
  have hidem : P.cmp u u = u := by
    have := ha n (P.idm n) (P.idm n)
    rw [P.cmp_idm] at this
    exact this.symm
  have hinv : P.cmp u (D.C0 n (P.idm n)) = P.idm (1 + n) := by
    have := he n (P.idm n)
    rw [P.tn_idm] at this
    exact this
  calc u = P.cmp u (P.idm (1 + n)) := (P.cmp_idm u).symm
    _ = P.cmp u (P.cmp u (D.C0 n (P.idm n))) := by rw [hinv]
    _ = P.cmp (P.cmp u u) (D.C0 n (P.idm n)) := (P.cmp_assoc _ _ _).symm
    _ = P.cmp u (D.C0 n (P.idm n)) := by rw [hidem]
    _ = P.idm (1 + n) := hinv

/-- The obstruction holds under either form of complementarity: if the distinguished involution
commutes with the symmetry, control makes it stably trivial. -/
theorem invol_tens_trivial_of_symmetric' {D : Data P} (hd : D.EqD) (he : D.EqE') (hg : D.EqG)
    (hsym : P.tn P.invol (P.idm 1) = P.tn (P.idm 1) P.invol) :
    P.tn P.invol (P.idm 1) = P.idm 2 := by
  set A : P.H (1 + 1) := P.tn P.invol (P.idm 1) with hA
  set S : P.H 2 := sw (P := P) with hS
  set Y : P.H (1 + 1) := D.C1 1 P.invol with hY
  have hAA : A * A = 1 := by
    show P.cmp A A = P.idm 2
    rw [hA, ← P.tn_cmp, P.invol_invol, P.cmp_idm, P.tn_idm]
  have hSS : S * S = 1 := by
    show P.cmp S S = P.idm 2
    rw [hS, sw, ← P.io_cmp, swapPH_one_one_sq, P.io_one]
  have hAS : A * S = S * A := by
    have hnat := P.io_swap_nat (m := 1) (n := 1) P.invol (P.idm 1)
    have hcast : (Nat.add_comm 1 1) ▸ (P.tn (P.idm 1) P.invol) = P.tn (P.idm 1) P.invol := rfl
    rw [hcast, ← hsym] at hnat
    exact hnat.symm
  have hC0 : D.C0 1 P.invol = A * Y * A := by
    have h := hd 1 P.invol
    have h' : A * (D.C0 1 P.invol * A) = Y := h
    calc D.C0 1 P.invol = 1 * D.C0 1 P.invol * 1 := by rw [one_mul, mul_one]
      _ = A * A * D.C0 1 P.invol * (A * A) := by rw [hAA]
      _ = A * (A * (D.C0 1 P.invol * A)) * A := by simp [mul_assoc]
      _ = A * Y * A := by rw [h']
  -- complementarity in Figure 1's order, at the involution
  have hex' : Y * A * (Y * A) = A := by
    have h : Y * D.C0 1 P.invol = P.tn (P.idm 1) P.invol := he 1 P.invol
    rw [hC0, ← hsym] at h
    calc Y * A * (Y * A) = Y * (A * Y * A) := by simp [mul_assoc]
      _ = A := h
  -- conjugating by the involution turns it into the order Definition 6 writes
  have key : A * (Y * A * (Y * A)) * A = A * Y * (A * Y) := by
    calc A * (Y * A * (Y * A)) * A = (A * Y * (A * Y)) * (A * A) := by simp [mul_assoc]
      _ = A * Y * (A * Y) := by rw [hAA, mul_one]
  have hex : A * Y * (A * Y) = A := by
    rw [← key, hex', hAA, one_mul]
  have hg' : Y * (S * (Y * (S * Y))) = S := hg
  exact alx_trivial_core hAA hSS hAS hex hg'


/-! ### Commutativity on invertible arguments, under the other order

The derivation of their (f) on invertible arguments also uses complementarity without (f),
so it too has to be checked against the order Figure 1 draws.  It survives, and the cheapest
way to see that is to swap the two colours: the data with `C0` and `C1` exchanged satisfies
(a), (b) and (d) whenever the original does, and its (e) is the original's (e) in the other
order.  Applying the derivation to the swapped data and exchanging the arguments back gives
the statement for the original. -/

/-- The control data with its two colours exchanged. -/
def Data.swapColours (D : Data P) : Data P where
  C0 := D.C1
  C1 := D.C0

theorem eqF_of_invertible' {D : Data P} (ha : D.EqA) (hb : D.EqB) (hd : D.EqD) (he : D.EqE')
    {n : ℕ} (f₁ f₂ : P.H n) (h₁ : IsInvertible f₁) (h₂ : IsInvertible f₂) :
    P.cmp (D.C0 n f₁) (D.C1 n f₂) = P.cmp (D.C1 n f₂) (D.C0 n f₁) := by
  have hXX : ∀ m : ℕ, P.cmp (xw m) (xw m) = P.idm (1 + m) := by
    intro m; unfold xw
    rw [← P.tn_cmp, P.invol_invol, P.cmp_idm, P.tn_idm]
  -- (d) read the other way: `C1` is the `x`-conjugate of `C0`, and conversely.
  have hd' : ∀ (m : ℕ) (f : P.H m),
      P.cmp (xw m) (P.cmp (D.C1 m f) (xw m)) = D.C0 m f := by
    intro m f
    have h := hd m f
    calc P.cmp (xw m) (P.cmp (D.C1 m f) (xw m))
        = P.cmp (xw m) (P.cmp (P.cmp (xw m) (P.cmp (D.C0 m f) (xw m))) (xw m)) := by rw [h]
      _ = P.cmp (P.cmp (xw m) (xw m)) (P.cmp (D.C0 m f) (P.cmp (xw m) (xw m))) := by
            simp [P.cmp_assoc]
      _ = D.C0 m f := by rw [hXX m]; rw [P.idm_cmp, P.cmp_idm]
  -- the swapped data satisfies (a), (b), (d) and (e)
  have ha' : (D.swapColours).EqA := by
    intro m f g
    show D.C0 m (P.cmp g f) = P.cmp (D.C0 m g) (D.C0 m f)
    letI := homMonoid P (1 + m)
    have hX : (xw m : P.H (1 + m)) * xw m = 1 := hXX m
    have hc : ∀ h : P.H m, D.C0 m h = xw m * D.C1 m h * xw m := by
      intro h; rw [← hd' m h]; simp [hom_mul_def, P.cmp_assoc]
    have hk : D.C1 m (P.cmp g f) = D.C1 m g * D.C1 m f := ha m f g
    show D.C0 m (P.cmp g f) = D.C0 m g * D.C0 m f
    rw [hc, hc, hc, hk]
    calc xw m * (D.C1 m g * D.C1 m f) * xw m
        = xw m * D.C1 m g * (xw m * xw m) * (D.C1 m f * xw m) := by rw [hX]; simp [mul_assoc]
      _ = xw m * D.C1 m g * xw m * (xw m * D.C1 m f * xw m) := by simp [mul_assoc]
  have hb' : (D.swapColours).EqB := by
    intro m
    letI := homMonoid P (1 + m)
    show D.C0 m (P.idm m) = P.idm (1 + m)
    rw [← hd' m (P.idm m), hb m]
    show (xw m : P.H (1 + m)) * (1 * xw m) = 1
    rw [one_mul]; exact hXX m
  have hd'' : (D.swapColours).EqD := by
    intro m f; exact hd' m f
  have he' : (D.swapColours).EqE := by
    intro m f; exact he m f
  have key := eqF_of_invertible ha' hb' hd'' he' f₂ f₁ h₂ h₁
  exact key.symm


end Ctrl

end Crops
