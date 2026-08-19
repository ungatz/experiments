import ControlEquations.CtrlSigned
import ControlEquations.CtrlInv

/-!
# Control forces a symmetric involution to become trivial

Every witness in `ControlEquations.CtrlModels` lives in a crop whose monoidal product is
collapsed, in the sense that `x + id₁ = id₁ + x`.  This file explains, for arbitrary crops, why
that corner cannot separate their (c) or their (h):

> in any controllable prop in which `x + id₁ = id₁ + x`, control data satisfying their (d), (e)
> and (g) forces `x + id₁ = id₂`.

So on such a crop the distinguished involution is stably trivial, and with it collapse the
phenomena that (c) and (h) are about.  This is an invariant of the crop rather than a bound
reached by a search: it identifies what a witness has to violate, namely `x + id₁ ≠ id₁ + x`,
as holds in the intended models, where `X ⊗ I ≠ I ⊗ X`.

Read against their Remark 8, it strengthens the observation there: one need not choose
`x = id₁` to reach the degenerate situation, since control makes the involution stably trivial
as soon as it fails to move under the symmetry.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

attribute [local instance] homMonoid

/-- The transposition of two wires is an involution of the permutation prop. -/
theorem swapPH_one_one_sq : (swapPH 1 1) * (swapPH 1 1) = (1 : PH 2) := by
  apply PH.ext'
  ext i
  simp only [PH.coe_mul, Equiv.Perm.mul_apply, swapPH_apply, PH.coe_one, Equiv.Perm.coe_one,
    id_eq]
  split_ifs <;> omega

variable {P : Crop}

/-- The obstruction.  If the distinguished involution of a controllable prop
commutes with the symmetry in the sense that `x + id₁ = id₁ + x`, then any control data
satisfying their (d), (e) and (g) forces `x + id₁ = id₂`.

Every graded-constant crop — signed or not — satisfies the hypothesis `x + id₁ = id₁ + x`, which
is why no crop in those classes can carry control data with a nontrivial involution, and hence
why those classes are blind to the independence of (c) and of (h). -/
theorem invol_tens_trivial_of_symmetric {D : Data P} (hd : D.EqD) (he : D.EqE) (hg : D.EqG)
    (hsym : P.tn P.invol (P.idm 1) = P.tn (P.idm 1) P.invol) :
    P.tn P.invol (P.idm 1) = P.idm 2 := by
  set A : P.H (1 + 1) := P.tn P.invol (P.idm 1) with hA
  set S : P.H 2 := sw (P := P) with hS
  set Y : P.H (1 + 1) := D.C1 1 P.invol with hY
  -- `A` is an involution
  have hAA : A * A = 1 := by
    show P.cmp A A = P.idm 2
    rw [hA, ← P.tn_cmp, P.invol_invol, P.cmp_idm, P.tn_idm]
  -- so is the symmetry
  have hSS : S * S = 1 := by
    show P.cmp S S = P.idm 2
    rw [hS, sw, ← P.io_cmp, swapPH_one_one_sq, P.io_one]
  -- naturality of the symmetry, plus the hypothesis, makes them commute
  have hAS : A * S = S * A := by
    have hnat := P.io_swap_nat (m := 1) (n := 1) P.invol (P.idm 1)
    have hcast : (Nat.add_comm 1 1) ▸ (P.tn (P.idm 1) P.invol) = P.tn (P.idm 1) P.invol := rfl
    rw [hcast, ← hsym] at hnat
    exact hnat.symm
  -- (d) at the involution, rewritten
  have hC0 : D.C0 1 P.invol = A * Y * A := by
    have h := hd 1 P.invol
    have h' : A * (D.C0 1 P.invol * A) = Y := h
    calc D.C0 1 P.invol = 1 * D.C0 1 P.invol * 1 := by rw [one_mul, mul_one]
      _ = A * A * D.C0 1 P.invol * (A * A) := by rw [hAA]
      _ = A * (A * (D.C0 1 P.invol * A)) * A := by simp [mul_assoc]
      _ = A * Y * A := by rw [h']
  -- (e) at the involution, using the hypothesis to identify `id₁ + x` with `A`
  have hex : A * Y * (A * Y) = A := by
    have h : D.C0 1 P.invol * Y = P.tn (P.idm 1) P.invol := he 1 P.invol
    rw [hC0, ← hsym] at h
    calc A * Y * (A * Y) = A * Y * A * Y := by simp [mul_assoc]
      _ = A := h
  -- (g)
  have hg' : Y * (S * (Y * (S * Y))) = S := hg
  have : A = 1 := alx_trivial_core hAA hSS hAS hex hg'
  exact this

end Ctrl

end Crops
