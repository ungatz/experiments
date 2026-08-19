import ControlEquations.CtrlComm

/-!
# A trivial symmetry forces their (c)

`ControlEquations.CtrlDefs` proves that in a crop whose permutation inclusion is trivial, their
(h) holds for free.  The companion statement for their (c) is proved here:

> in any crop whose permutation inclusion is trivial, control data satisfying their (a), (d),
> (e) and (g) satisfies their (c).

So the degenerate corner, which is every graded-constant crop and more generally every crop in
which permutations act as identities, separates neither (c) nor (h).

The mechanism.  With a trivial symmetry the two paddings coincide, `f + id₁ = id₁ + f`; the
obstruction `invol_tens_trivial_of_symmetric` then makes `x + id₁ = id₂`, so `C0 = C1` in every
positive arity, and (e) reads `C1 f ∘ C1 f = id₁ + f`.  Applying `C1` to that identity turns
left padding into left padding one level up, and induction on the number of padding wires
delivers (c).

`ControlEquations.CtrlStrength` later derives (c) in every crop, with no hypothesis on the
symmetry, so the theorem below is subsumed.  It is kept because it is what located the general
derivation.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

variable {P : Crop} {D : Data P}

/-! ### Consequences of a trivial permutation inclusion -/

/-- With a trivial permutation inclusion the two paddings by one wire agree. -/
lemma pad_comm_of_trivial_symmetry (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    {n : ℕ} (f : P.H n) :
    P.tn f (P.idm 1) = P.cst (Nat.add_comm 1 n) (P.tn (P.idm 1) f) := by
  have h := P.io_swap_nat (m := n) (n := 1) f (P.idm 1)
  rw [hio] at h
  rw [P.idm_cmp, P.cmp_idm] at h
  exact h

/-- With a trivial permutation inclusion the symmetry `σ₁,₁` is the identity. -/
lemma sw_trivial (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n) :
    sw (P := P) = P.idm 2 := hio 2 (swapPH 1 1)

/-- Under the hypotheses of the obstruction, the involution padded by one wire is trivial. -/
lemma invol_pad_trivial (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    (hd : D.EqD) (he : D.EqE) (hg : D.EqG) :
    P.tn P.invol (P.idm 1) = P.idm 2 := by
  refine invol_tens_trivial_of_symmetric (D := D) hd he hg ?_
  have h := pad_comm_of_trivial_symmetry hio (P.invol)
  rw [h]
  rfl

/-- The involution padded by `1 + k` wires is the identity. -/
lemma xw_succ_trivial (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    (hd : D.EqD) (he : D.EqE) (hg : D.EqG) (k : ℕ) :
    xw (P := P) (1 + k) = P.idm (1 + (1 + k)) := by
  have hA : P.tn P.invol (P.idm 1) = P.idm 2 := invol_pad_trivial hio hd he hg
  unfold xw
  rw [← P.tn_idm 1 k, ← P.tn_assoc' P.invol (P.idm 1) (P.idm k), hA, P.tn_idm, P.cst_idm]

/-- Where the padded involution is trivial, the two colours of control agree. -/
lemma C0_eq_C1_of_xw_trivial (hd : D.EqD) {n : ℕ} (hx : xw (P := P) n = P.idm (1 + n))
    (f : P.H n) : D.C0 n f = D.C1 n f := by
  have h := hd n f
  rwa [hx, P.idm_cmp, P.cmp_idm] at h

/-- Where the padded involution is trivial, (e) says that control squares to left padding. -/
lemma C1_sq_of_xw_trivial (hd : D.EqD) (he : D.EqE) {n : ℕ}
    (hx : xw (P := P) n = P.idm (1 + n)) (f : P.H n) :
    P.cmp (D.C1 n f) (D.C1 n f) = P.tn (P.idm 1) f := by
  have h := he n f
  rwa [C0_eq_C1_of_xw_trivial hd hx f] at h

/-- Controlling the distinguished involution gives the identity. -/
lemma C1_invol_trivial (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    (hd : D.EqD) (he : D.EqE) (hg : D.EqG) : D.C1 1 P.invol = P.idm 2 := by
  have hx1 : xw (P := P) 1 = P.idm (1 + 1) := xw_succ_trivial hio hd he hg 0
  -- (e), with `C0 = C1`, squares the controlled involution to `id₁ + x`
  have hsq : P.cmp (D.C1 1 P.invol) (D.C1 1 P.invol) = P.tn (P.idm 1) P.invol :=
    C1_sq_of_xw_trivial hd he hx1 P.invol
  have hpad : P.tn (P.idm 1) P.invol = P.idm 2 := by
    have h := pad_comm_of_trivial_symmetry hio (P.invol)
    have hA : P.tn P.invol (P.idm 1) = P.idm 2 := invol_pad_trivial hio hd he hg
    rw [hA] at h
    have : P.cst (Nat.add_comm 1 1) (P.tn (P.idm 1) P.invol) = P.tn (P.idm 1) P.invol := rfl
    rw [this] at h
    exact h.symm
  rw [hpad] at hsq
  -- (g), with a trivial symmetry, cubes it to the identity
  have hg' : P.cmp (D.C1 1 P.invol)
      (P.cmp (sw (P := P)) (P.cmp (D.C1 1 P.invol)
        (P.cmp (sw (P := P)) (D.C1 1 P.invol)))) = sw (P := P) := hg
  simp only [sw_trivial hio, P.idm_cmp] at hg'
  calc D.C1 1 P.invol
      = P.cmp (P.idm 2) (D.C1 1 P.invol) := (P.idm_cmp _).symm
    _ = P.cmp (P.cmp (D.C1 1 P.invol) (D.C1 1 P.invol)) (D.C1 1 P.invol) := by rw [hsq]
    _ = P.cmp (D.C1 1 P.invol) (P.cmp (D.C1 1 P.invol) (D.C1 1 P.invol)) := P.cmp_assoc _ _ _
    _ = P.idm 2 := hg'

/-- Controlling the padded involution gives the identity, in every arity. -/
lemma C1_xw_trivial (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hg : D.EqG) (n : ℕ) :
    D.C1 (1 + n) (xw (P := P) n) = P.idm (1 + (1 + n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hx0 : xw (P := P) 0 = P.invol := P.tn_idm_right P.invol
    rw [hx0]
    exact C1_invol_trivial hio hd he hg
  · obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega⟩
    rw [xw_succ_trivial hio hd he hg k]
    exact eqB_of_eqA_eqE ha he (1 + (1 + k))

/-! ### The key step: control commutes with left padding -/

/-- **Control commutes with left padding**, in a crop with trivial symmetry. -/
lemma C1_pad_left (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hg : D.EqG) {n : ℕ} (f : P.H n) :
    D.C1 (1 + n) (P.tn (P.idm 1) f) = P.tn (P.idm 1) (D.C1 n f) := by
  have hx : xw (P := P) (1 + n) = P.idm (1 + (1 + n)) := xw_succ_trivial hio hd he hg n
  -- (e) at `f`, and (d) rewritten as `C0 f = xw ∘ C1 f ∘ xw`
  have hC0 : D.C0 n f = P.cmp (xw (P := P) n) (P.cmp (D.C1 n f) (xw (P := P) n)) := by
    have hxx : P.cmp (xw (P := P) n) (xw (P := P) n) = P.idm (1 + n) := by
      unfold xw
      rw [← P.tn_cmp, P.invol_invol, P.cmp_idm, P.tn_idm]
    have h := hd n f
    calc D.C0 n f
        = P.cmp (P.idm (1 + n)) (P.cmp (D.C0 n f) (P.idm (1 + n))) := by
          rw [P.idm_cmp, P.cmp_idm]
      _ = P.cmp (P.cmp (xw (P := P) n) (xw (P := P) n))
            (P.cmp (D.C0 n f) (P.cmp (xw (P := P) n) (xw (P := P) n))) := by rw [hxx]
      _ = P.cmp (xw (P := P) n)
            (P.cmp (P.cmp (xw (P := P) n) (P.cmp (D.C0 n f) (xw (P := P) n)))
              (xw (P := P) n)) := by
          simp only [P.cmp_assoc]
      _ = P.cmp (xw (P := P) n) (P.cmp (D.C1 n f) (xw (P := P) n)) := by rw [h]
  have hE : P.cmp (D.C0 n f) (D.C1 n f) = P.tn (P.idm 1) f := he n f
  -- apply `C1` to (e) and use that controlling `xw` is the identity
  have hstep : D.C1 (1 + n) (P.tn (P.idm 1) f)
      = P.cmp (D.C1 (1 + n) (D.C0 n f)) (D.C1 (1 + n) (D.C1 n f)) := by
    rw [← hE, ha]
  have hC1C0 : D.C1 (1 + n) (D.C0 n f) = D.C1 (1 + n) (D.C1 n f) := by
    rw [hC0, ha, ha, C1_xw_trivial hio ha hd he hg n, P.idm_cmp, P.cmp_idm]
  rw [hstep, hC1C0]
  exact C1_sq_of_xw_trivial hd he hx (D.C1 n f)

/-! ### The blindness theorem -/

/-- Transporting `C1` along an equality of wire counts. -/
lemma C1_cst {M N : ℕ} (h : M = N) (g : P.H M) :
    D.C1 N (P.cst h g) = P.cst (by omega) (D.C1 M g) := by
  cases h; rfl

/-- A cast along an equality whose two sides are definitionally equal is the identity. -/
lemma cst_self {M : ℕ} (h : M = M) (g : P.H M) : P.cst h g = g := by
  rw [Subsingleton.elim h rfl, P.cst_rfl]

/-- **Control commutes with right padding by one wire**, in a crop with trivial symmetry. -/
lemma C1_pad_right_one (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hg : D.EqG) {n : ℕ} (f : P.H n) :
    D.C1 (n + 1) (P.tn f (P.idm 1)) = P.cst (by omega) (P.tn (D.C1 n f) (P.idm 1)) := by
  rw [pad_comm_of_trivial_symmetry hio f, C1_cst,
    C1_pad_left hio ha hd he hg f,
    pad_comm_of_trivial_symmetry hio (D.C1 n f), P.cst_cst]

/-- **In a crop with a trivial permutation inclusion, their (c) follows from their (a), (d), (e)
and (g).**  Consequently no such crop witnesses the logical independence of (c); with
`eqH_of_trivial_symmetry`, no such crop witnesses the independence of (h) either.

Reading: `C0`, `C1` are bare arity-indexed maps, as in `ControlEquations.CtrlDefs`.  Under the
alternative reading in which they are given as functors, (a) is part of the data and the
statement is unchanged. -/
theorem eqC_of_trivial_symmetry (hio : ∀ (n : ℕ) (p : PH n), P.io p = P.idm n)
    (ha : D.EqA) (hd : D.EqD) (he : D.EqE) (hg : D.EqG) : D.EqC := by
  intro n m
  induction m with
  | zero =>
    intro f
    rw [P.tn_idm_right, P.tn_idm_right]
    exact (cst_self _ _).symm
  | succ m ih =>
    intro f
    have hsplit : P.tn f (P.idm (m + 1))
        = P.cst (by omega) (P.tn (P.tn f (P.idm m)) (P.idm 1)) := by
      rw [← P.tn_idm m 1, ← P.tn_assoc' f (P.idm m) (P.idm 1)]
    rw [hsplit, C1_cst, C1_pad_right_one hio ha hd he hg, ih, P.tn_cst_left, P.cst_cst,
      P.cst_cst, ← P.tn_idm m 1, ← P.tn_assoc' (D.C1 n f) (P.idm m) (P.idm 1), P.cst_cst]

end Ctrl

end Crops
