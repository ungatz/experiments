import ControlEquations.CtrlTwist

/-!
# Two partial triviality results for central control

Partial versions of the statement that a central character is trivial after padding, obtained
under a centrality and involutivity hypothesis on the image of the control operators.  Both are
subsumed by `central_character_padding_trivial` in `ControlEquations.CtrlStrengthConseq`, which
needs no such hypothesis, and are kept for the record.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

variable {P : Crop}

/-- The padded involution `x + id_n` is an involution. -/
theorem xw_invol (n : ℕ) : P.cmp (xw (P := P) n) (xw (P := P) n) = P.idm (1 + n) := by
  rw [xw, ← P.tn_cmp, P.invol_invol, P.cmp_idm, P.tn_idm]

/-! ### The obstruction -/

/-- **A control image that is central and involutive is invisible to padding.**

If `C1 h` is central in `H (1+n)` and `h ∘ h = id`, then their (a), (d) and (e) force
`id₁ + h = id`.  No hypothesis on the crop, the arity or invertibility. -/
theorem left_pad_trivial_of_central_control {D : Data P}
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) {n : ℕ} {h : P.H n}
    (hh : P.cmp h h = P.idm n)
    (hcen : ∀ u : P.H (1 + n), P.cmp (D.C1 n h) u = P.cmp u (D.C1 n h)) :
    P.tn (P.idm 1) h = P.idm (1 + n) := by
  set w : P.H (1 + n) := D.C1 n h with hw
  set X : P.H (1 + n) := xw (P := P) n with hX
  have hXX : P.cmp X X = P.idm (1 + n) := xw_invol n
  -- (d) determines `C0 h`, and centrality collapses the conjugation
  have hc0 : D.C0 n h = w := by
    have h1 : P.cmp X (P.cmp (D.C0 n h) X) = w := hd n h
    have h2 : P.cmp (D.C0 n h) X = P.cmp X w := by
      calc P.cmp (D.C0 n h) X
          = P.cmp (P.idm (1 + n)) (P.cmp (D.C0 n h) X) := (P.idm_cmp _).symm
        _ = P.cmp (P.cmp X X) (P.cmp (D.C0 n h) X) := by rw [hXX]
        _ = P.cmp X (P.cmp X (P.cmp (D.C0 n h) X)) := P.cmp_assoc _ _ _
        _ = P.cmp X w := by rw [h1]
    calc D.C0 n h = P.cmp (D.C0 n h) (P.idm (1 + n)) := (P.cmp_idm _).symm
      _ = P.cmp (D.C0 n h) (P.cmp X X) := by rw [hXX]
      _ = P.cmp (P.cmp (D.C0 n h) X) X := (P.cmp_assoc _ _ _).symm
      _ = P.cmp (P.cmp X w) X := by rw [h2]
      _ = P.cmp (P.cmp w X) X := by rw [hcen X]
      _ = P.cmp w (P.cmp X X) := P.cmp_assoc _ _ _
      _ = w := by rw [hXX, P.cmp_idm]
  -- (e) then reads `w ∘ w = id₁ + h`, while (a) and `h ∘ h = id` read `w ∘ w = C1 (id) = id`
  have hsq : P.cmp w w = P.tn (P.idm 1) h := by
    have := he n h
    rwa [hc0] at this
  have hb : D.C1 n (P.idm n) = P.idm (1 + n) := eqB_of_eqA_eqE ha he n
  have hsq' : P.cmp w w = P.idm (1 + n) := by
    have := ha n h h
    rw [hh, hb] at this
    exact this.symm
  rw [← hsq, hsq']

/-- Left padding by one wire is trivial iff right padding by one wire is: the block symmetry
conjugates one into the other. -/
theorem right_pad_one_trivial_of_left {n : ℕ} {h : P.H n}
    (hl : P.tn (P.idm 1) h = P.idm (1 + n)) : P.tn h (P.idm 1) = P.idm (n + 1) := by
  have hnat := P.io_swap_nat (P.idm 1) h
  rw [hl, P.cmp_idm] at hnat
  set Y : P.H (1 + n) := (Nat.add_comm n 1) ▸ (P.tn h (P.idm 1)) with hY
  have hYid : Y = P.idm (1 + n) := by
    calc Y = P.cmp Y (P.idm (1 + n)) := (P.cmp_idm _).symm
      _ = P.cmp Y (P.cmp (P.io (swapPH 1 n)) (P.io (swapPH 1 n)⁻¹)) := by rw [P.io_inv_cmp]
      _ = P.cmp (P.cmp Y (P.io (swapPH 1 n))) (P.io (swapPH 1 n)⁻¹) := (P.cmp_assoc _ _ _).symm
      _ = P.cmp (P.io (swapPH 1 n)) (P.io (swapPH 1 n)⁻¹) := by rw [← hnat]
      _ = P.idm (1 + n) := P.io_inv_cmp _
  have := hYid
  rw [hY] at this
  have hcast : P.cst (Nat.add_comm n 1) (P.tn h (P.idm 1)) = P.cst (Nat.add_comm n 1)
      (P.idm (n + 1)) := by
    rw [P.cst_idm]; exact this
  exact P.cst_inj _ hcast

/-- Right padding by any positive number of wires is trivial too. -/
theorem right_pad_trivial_of_left {n : ℕ} {h : P.H n}
    (hl : P.tn (P.idm 1) h = P.idm (1 + n)) :
    ∀ m : ℕ, P.tn h (P.idm (m + 1)) = P.idm (n + (m + 1))
  | 0 => right_pad_one_trivial_of_left hl
  | m + 1 => by
      have hstep : P.tn h (P.idm (m + 1)) = P.idm (n + (m + 1)) :=
        right_pad_trivial_of_left hl m
      have hsplit : P.idm (m + 1 + 1) = P.tn (P.idm (m + 1)) (P.idm 1) := (P.tn_idm _ _).symm
      have hassoc := P.tn_assoc h (P.idm (m + 1)) (P.idm 1)
      have : P.tn h (P.tn (P.idm (m + 1)) (P.idm 1))
          = P.cst (Nat.add_assoc n (m + 1) 1) (P.tn (P.tn h (P.idm (m + 1))) (P.idm 1)) :=
        hassoc.symm
      rw [hsplit, this, hstep, P.tn_idm, P.cst_idm]

/-! ### The consequence for the twist criterion -/

/-- **A central involutive control image is padding-trivial, hence useless as a twisting
character.**  If `C1 h` is central in `H (1+n)` and `h` is an involution, then every positive
padding of `C1 h` is an identity; a central-character twist by `χ = C1 h` therefore satisfies
their (c) and cannot witness its independence.

Uses their (a), (c), (d), (e) in the underlying model. -/
theorem central_control_image_padding_trivial {D : Data P}
    (ha : D.EqA) (hc : D.EqC) (hd : D.EqD) (he : D.EqE) {n : ℕ} {h : P.H n}
    (hh : P.cmp h h = P.idm n)
    (hcen : ∀ u : P.H (1 + n), P.cmp (D.C1 n h) u = P.cmp u (D.C1 n h)) (m : ℕ) :
    P.tn (D.C1 n h) (P.idm (m + 1)) = P.idm (1 + n + (m + 1)) := by
  have hl : P.tn (P.idm 1) h = P.idm (1 + n) :=
    left_pad_trivial_of_central_control ha hd he hh hcen
  have hr : P.tn h (P.idm (m + 1)) = P.idm (n + (m + 1)) := right_pad_trivial_of_left hl m
  have hb : D.C1 (n + (m + 1)) (P.idm (n + (m + 1))) = P.idm (1 + (n + (m + 1))) :=
    eqB_of_eqA_eqE ha he _
  have hcm := hc n (m + 1) h
  rw [hr, hb] at hcm
  have : P.cst (by omega : 1 + n + (m + 1) = 1 + (n + (m + 1)))
      (P.tn (D.C1 n h) (P.idm (m + 1)))
      = P.cst (by omega : 1 + n + (m + 1) = 1 + (n + (m + 1))) (P.idm (1 + n + (m + 1))) := by
    rw [P.cst_idm]; exact hcm.symm
  exact P.cst_inj _ this

end Ctrl

end Crops
