import ControlEquations.CropCore

/-!
# The control equations, and one derivation

This file fixes the data and the eight equations of Definition 6 of Heunen, Kaarsgaard and
Lemonnier, *One rig to control them all* (LICS 2026, arXiv:2510.05032v3).

A controllable prop is a prop all of whose morphisms are endomorphisms together with a
distinguished involution `x : 1 → 1`, which is the `Crop` of `ControlEquations.CropCore`.
Control data on it is a pair of arity-indexed maps `C0 C1 : ∀ n, H n → H (1+n)`, the object part
of the two endofunctors being `n ↦ 1 + n`.  The eight equations are the predicates `EqA` to
`EqH` below.

Taking the control data to be bare maps is the only reading under which their (a) and (b) are
equations that could be independent; Definition 6 introduces `C0` and `C1` as endofunctors and
then lists functoriality as (a) and (b).  Nothing that follows depends on the choice except the
cell (a) itself: every other model built here satisfies (a) and (b).

The derivation proved here is `eqB_of_eqA_eqE`: their (b) follows from their (a) and (e) alone,
in every controllable prop.  The argument is one line of monoid theory, since (a) makes `C1 id`
idempotent and (e) gives it a one-sided inverse.

All of this concerns the logical independence of an equational presentation.  That is a
different question from the structural minimality of their construction, which is the universal
property of their Corollary 18 and the paragraph after their Theorem 23, and neither question
implies the other.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

variable (P : Crop)

/-- Control data on a crop: the morphism part of the two endofunctors `C0`, `C1`, whose
object part is `n ↦ 1 + n`.  No equation is imposed here; the eight equations of
Heunen–Kaarsgaard–Lemonnier's Definition 6 are the predicates `EqA`–`EqH` below. -/
structure Data where
  /-- the `0`-controlled functor, on morphisms -/
  C0 : (n : ℕ) → P.H n → P.H (1 + n)
  /-- the `1`-controlled functor, on morphisms -/
  C1 : (n : ℕ) → P.H n → P.H (1 + n)

variable {P}

/-- The distinguished involution on the control wire, tensored with `n` wires: `x + id_n`. -/
def xw (n : ℕ) : P.H (1 + n) := P.tn P.invol (P.idm n)

/-- The symmetry `σ_{1,1}`. -/
def sw : P.H 2 := P.io (swapPH 1 1)

/-- `σ_{1,1} + id_n`, as a morphism on `1 + (1 + n)` wires. -/
def sww (n : ℕ) : P.H (1 + (1 + n)) := P.cst (by omega) (P.tn (sw (P := P)) (P.idm n))

/-- **(a) composition**: `C1 (g ∘ f) = C1 g ∘ C1 f`. -/
def Data.EqA (D : Data P) : Prop :=
  ∀ (n : ℕ) (f g : P.H n), D.C1 n (P.cmp g f) = P.cmp (D.C1 n g) (D.C1 n f)

/-- **(b) identity**: `C1 (id_n) = id_{1+n}`. -/
def Data.EqB (D : Data P) : Prop :=
  ∀ (n : ℕ), D.C1 n (P.idm n) = P.idm (1 + n)

/-- **(c) strength**: `C1 (f + id_m) = C1 f + id_m`. -/
def Data.EqC (D : Data P) : Prop :=
  ∀ (n m : ℕ) (f : P.H n),
    D.C1 (n + m) (P.tn f (P.idm m)) = P.cst (by omega) (P.tn (D.C1 n f) (P.idm m))

/-- **(d) colour change**: `(x + id_n) ∘ C0 f ∘ (x + id_n) = C1 f`. -/
def Data.EqD (D : Data P) : Prop :=
  ∀ (n : ℕ) (f : P.H n), P.cmp (xw n) (P.cmp (D.C0 n f) (xw n)) = D.C1 n f

/-- **(e) complementarity**: `C0 f ∘ C1 f = id_1 + f`. -/
def Data.EqE (D : Data P) : Prop :=
  ∀ (n : ℕ) (f : P.H n), P.cmp (D.C0 n f) (D.C1 n f) = P.tn (P.idm 1) f

/-- **(f) commutativity**: `C0 f₁ ∘ C1 f₂ = C1 f₂ ∘ C0 f₁`. -/
def Data.EqF (D : Data P) : Prop :=
  ∀ (n : ℕ) (f₁ f₂ : P.H n),
    P.cmp (D.C0 n f₁) (D.C1 n f₂) = P.cmp (D.C1 n f₂) (D.C0 n f₁)

/-- **(g) "swap"**: `C1 x ∘ s ∘ C1 x ∘ s ∘ C1 x = s`, with `s = σ_{1,1}`. -/
def Data.EqG (D : Data P) : Prop :=
  P.cmp (D.C1 1 P.invol)
      (P.cmp sw (P.cmp (D.C1 1 P.invol) (P.cmp sw (D.C1 1 P.invol)))) = sw

/-- **(h) "swap" coherence**: `(σ_{1,1} + id_n) ∘ C1 (C1 f) = C1 (C1 f) ∘ (σ_{1,1} + id_n)`. -/
def Data.EqH (D : Data P) : Prop :=
  ∀ (n : ℕ) (f : P.H n),
    P.cmp (sww n) (D.C1 (1 + n) (D.C1 n f)) = P.cmp (D.C1 (1 + n) (D.C1 n f)) (sww n)

/-- All eight equations. -/
def Data.All (D : Data P) : Prop :=
  D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ D.EqH

/-!
### The one derivation

Their equation **(b)** is not independent: it follows from **(a)** and **(e)** alone, in every
controllable prop.  (Consequently no model can witness the independence of (b), and the cell
(b) is derivable rather than independent.)
-/

/-- **Their equation (b) is derivable from their (a) and (e).**  In any controllable prop with
control data, if `C1` preserves composition and `C0 f ∘ C1 f = id_1 + f`, then
`C1 (id_n) = id_{1+n}`.

Scope: this is a statement about the *equational presentation* of Definition 6 — it says the
listed axiom (b) is redundant.  It says nothing about the structural minimality of the
construction, which is a different (and known) statement. -/
theorem eqB_of_eqA_eqE {D : Data P} (ha : D.EqA) (he : D.EqE) : D.EqB := by
  intro n
  set u : P.H (1 + n) := D.C1 n (P.idm n) with hu
  -- (a) at `f = g = id` makes `u` idempotent
  have hidem : P.cmp u u = u := by
    have := ha n (P.idm n) (P.idm n)
    rw [P.cmp_idm] at this
    exact this.symm
  -- (e) at `f = id` gives `u` a left inverse
  have hinv : P.cmp (D.C0 n (P.idm n)) u = P.idm (1 + n) := by
    have := he n (P.idm n)
    rw [P.tn_idm] at this
    exact this
  calc u = P.cmp (P.idm (1 + n)) u := (P.idm_cmp u).symm
    _ = P.cmp (P.cmp (D.C0 n (P.idm n)) u) u := by rw [hinv]
    _ = P.cmp (D.C0 n (P.idm n)) (P.cmp u u) := P.cmp_assoc _ _ _
    _ = P.cmp (D.C0 n (P.idm n)) u := by rw [hidem]
    _ = P.idm (1 + n) := hinv

/-!
### A blindness theorem for (h)

Every model built here is a prop whose symmetry inclusion is trivial (all
permutations act as identities).  In *any* such crop, equation (h) holds for free, whatever the
control data.  So the degenerate corner in which the other witnesses live cannot witness (h);
this is the precise reason cell (h) is left open rather than merely unattempted.
-/

/-- If the symmetry inclusion of the crop is trivial, then their equation (h) holds for every
control datum.  More generally it suffices that `σ_{1,1} + id_n` is the identity. -/
theorem eqH_of_trivial_symmetry (D : Data P)
    (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n) : D.EqH := by
  intro n f
  have hs : (sww (P := P) n) = P.idm (1 + (1 + n)) := by
    unfold sww sw
    rw [hio, P.tn_idm, P.cst_idm]
  rw [hs, P.idm_cmp, P.cmp_idm]

end Ctrl

end Crops
