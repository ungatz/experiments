import ControlEquations.CtrlComm

/-!
# Their equation (c) is derivable

> In every controllable prop, control data satisfying their (a), (d), (e), (f) and (h) satisfies
> their (c).

Together with `eqB_of_eqA_eqE`, which derives their (b) from (a) and (e), this says that two of
the eight listed equations are redundant, and the remaining six are irredundant.

## The argument

Write `u = x + id_n`, `K = C₁ f`, and let `s = σ_{n,1}` be the symmetry that moves the last wire
to the front.  Both sides of (c) are conjugates of one and the same morphism

  `Ω = C₁ (id₁ + f)`,

the left side by `C₁ s` and the right side by `id₁ + s`:

* `f + id₁ = s⁻¹ (id₁ + f) s` by naturality, so `C₁ (f + id₁) = C₁(s)⁻¹ Ω C₁ s` by (a);
* `C₁ f + id₁ = σ⁻¹ (id₁ + C₁ f) σ` for `σ = σ_{1+n,1} = (σ_{1,1} + id_n)(id₁ + s)`.  By (e) and
  (d), `id₁ + C₁ f = u C₁K u C₁K`; conjugating by `σ_{1,1} + id_n` moves `u` to the second wire
  and fixes `C₁ K`, which is exactly their (h), and (e) applied to `u` itself, together with
  (f), collapses the result to `Ω`.  So the right side is `(id₁+s)⁻¹ Ω (id₁+s)`.

The two conjugators differ by `C₀ s`: their (e) at the morphism `s` says
`id₁ + s = C₀(s) · C₁(s)`, and their (f) says `C₀ s` commutes with `C₁ (id₁ + f) = Ω`.  Hence the
two conjugates agree.

At `n = 0` the symmetry `σ_{0,1}` is the identity and the argument degenerates to the
observation that both sides equal `Ω`.  The content of the general case is that the discrepancy
between the two conjugators is a `C₀`-value, which (f) makes invisible.

Their (g) is not used anywhere in the derivation.

## Provenance

The equations, Definition 6 and the question of which of them are independent are Heunen,
Kaarsgaard and Lemonnier's.  The method of deciding which of a printed list of rules are
independent, which sub-lists suffice, and whether the minimal sub-list is unique is the method
of Clément, Delorme and Perdrix, *Minimal equational theories for quantum circuits* (LICS 2024),
for the different object of quantum circuits.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

attribute [local instance] homMonoid

variable {P : Crop}

/-! ### Cast bookkeeping -/

lemma cst_self {m : ℕ} (h : m = m) (g : P.H m) : P.cst h g = g := rfl

@[simp] lemma io_cst {m m' : ℕ} (h : m = m') (p : PH m) :
    P.io (h ▸ p) = P.cst h (P.io p) := by subst h; rfl

lemma Data.C1_cst (D : Data P) {m m' : ℕ} (h : m = m') (g : P.H m) :
    D.C1 m' (P.cst h g) = P.cst (by omega) (D.C1 m g) := by subst h; rfl

/-! ### Elementary facts about the padded involution and the padded symmetry -/

/-- The involution padded on the right is an involution. -/
lemma xw_sq (n : ℕ) : (xw (P := P) n) * (xw (P := P) n) = 1 := by
  show P.cmp (xw n) (xw n) = P.idm (1 + n)
  unfold xw
  rw [← P.tn_cmp, P.invol_invol, P.cmp_idm, P.tn_idm]

/-- The symmetry `σ_{1,1} + id_n` is an involution. -/
lemma sww_sq (n : ℕ) : (sww (P := P) n) * (sww (P := P) n) = 1 := by
  show P.cmp (sww n) (sww n) = P.idm (1 + (1 + n))
  unfold sww
  rw [← P.cst_cmp, ← P.tn_cmp, P.cmp_idm]
  have h : P.cmp (sw (P := P)) (sw (P := P)) = P.idm 2 := by
    unfold sw
    rw [← P.io_cmp, swapPH_one_one_sq, P.io_one]
  rw [h, P.tn_idm, P.cst_idm]

lemma xw_succ_eq (n : ℕ) :
    P.cst (Nat.add_assoc 1 1 n) (P.tn (P.tn P.invol (P.idm 1)) (P.idm n))
      = xw (P := P) (1 + n) := by
  rw [P.tn_assoc' P.invol (P.idm 1) (P.idm n), P.tn_idm]; rfl

lemma xw_succ_eq' (n : ℕ) :
    P.cst (Nat.add_assoc 1 1 n) (P.tn (P.tn (P.idm 1) P.invol) (P.idm n))
      = P.tn (P.idm 1) (xw (P := P) n) := by
  rw [P.tn_assoc' (P.idm 1) P.invol (P.idm n)]; rfl

lemma sw_mul_invol :
    P.cmp (sw (P := P)) (P.tn P.invol (P.idm 1))
      = P.cmp (P.tn (P.idm 1) P.invol) (sw (P := P)) := by
  have hnat := P.io_swap_nat (m := 1) (n := 1) P.invol (P.idm 1)
  have hcast : (Nat.add_comm 1 1) ▸ (P.tn (P.idm 1) P.invol) = P.tn (P.idm 1) P.invol := rfl
  rw [hcast] at hnat
  exact hnat

/-- Conjugating the padded involution by the symmetry moves it onto the second wire. -/
lemma sww_mul_xw (n : ℕ) :
    (sww (P := P) n) * (xw (P := P) (1 + n))
      = (P.tn (P.idm 1) (xw (P := P) n)) * (sww (P := P) n) := by
  have key : P.cmp (P.tn (sw (P := P)) (P.idm n)) (P.tn (P.tn P.invol (P.idm 1)) (P.idm n))
      = P.cmp (P.tn (P.tn (P.idm 1) P.invol) (P.idm n)) (P.tn (sw (P := P)) (P.idm n)) := by
    rw [← P.tn_cmp_idm_right, ← P.tn_cmp_idm_right, sw_mul_invol]
  have h1 : xw (P := P) (1 + n)
      = P.cst (Nat.add_assoc 1 1 n) (P.tn (P.tn P.invol (P.idm 1)) (P.idm n)) :=
    (xw_succ_eq n).symm
  have h2 : P.tn (P.idm 1) (xw (P := P) n)
      = P.cst (Nat.add_assoc 1 1 n) (P.tn (P.tn (P.idm 1) P.invol) (P.idm n)) :=
    (xw_succ_eq' n).symm
  have h3 : sww (P := P) n = P.cst (Nat.add_assoc 1 1 n) (P.tn (sw (P := P)) (P.idm n)) := rfl
  show P.cmp _ _ = P.cmp _ _
  rw [h1, h2, h3, ← P.cst_cmp, ← P.cst_cmp, key]

/-- The block symmetry that moves the last of `1 + n + 1` wires to the front factors as the
transposition of the first two wires after the block symmetry on the last `n + 1`. -/
lemma swapPH_succ_one (n : ℕ) :
    swapPH (1 + n) 1 =
      ((show 2 + n = (1 + n) + 1 by omega) ▸ (PH.tens (swapPH 1 1) (1 : PH n)))
        * ((show 1 + (n + 1) = (1 + n) + 1 by omega) ▸ PH.tens (1 : PH 1) (swapPH n 1)) := by
  apply PH.ext'
  ext i
  simp only [PH.coe_mul, PH.coe_cast, Equiv.Perm.mul_apply, PH.tens_apply, swapPH_apply,
    PH.coe_one, Equiv.Perm.coe_one, id_eq]
  split_ifs <;> omega

/-! ### The derivation -/

variable {D : Data P}

/-- (d), rewritten: `C₀ g = (x + id) ∘ C₁ g ∘ (x + id)`. -/
lemma C0_eq (hd : D.EqD) {m : ℕ} (g : P.H m) :
    D.C0 m g = (xw (P := P) m) * D.C1 m g * (xw (P := P) m) := by
  have hXX : (xw (P := P) m) * (xw (P := P) m) = 1 := xw_sq m
  have h : (xw (P := P) m) * (D.C0 m g * (xw (P := P) m)) = D.C1 m g := hd m g
  have h' : (xw (P := P) m) * D.C0 m g * (xw (P := P) m) = D.C1 m g := by
    rw [mul_assoc]; exact h
  calc D.C0 m g = 1 * D.C0 m g * 1 := by rw [one_mul, mul_one]
    _ = (xw (P := P) m) * (xw (P := P) m) * D.C0 m g *
          ((xw (P := P) m) * (xw (P := P) m)) := by rw [hXX]
    _ = (xw (P := P) m) * ((xw (P := P) m) * D.C0 m g * (xw (P := P) m)) *
          (xw (P := P) m) := by simp [mul_assoc]
    _ = (xw (P := P) m) * D.C1 m g * (xw (P := P) m) := by rw [h']

/-- **Their (c) at one padding wire, derived from their (a), (b), (d), (e), (f) and (h).** -/
theorem eqC_one_of_others (ha : D.EqA) (hb : D.EqB) (hd : D.EqD) (he : D.EqE)
    (hf : D.EqF) (hh : D.EqH) (n : ℕ) (f : P.H n) :
    D.C1 (1 + n) (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1)))
      = P.cst (show (1 + n) + 1 = 1 + (1 + n) by omega) (P.tn (D.C1 n f) (P.idm 1)) := by
  -- multiplicativity of `C1`
  have hmul : ∀ (m : ℕ) (a b : P.H m), D.C1 m (a * b) = D.C1 m a * D.C1 m b :=
    fun m a b => ha m b a
  have hone : ∀ m : ℕ, D.C1 m (1 : P.H m) = 1 := hb
  -- the players
  set u : P.H (1 + n) := xw (P := P) n with hu
  set K : P.H (1 + n) := D.C1 n f with hK
  set IF : P.H (1 + n) := P.tn (P.idm 1) f with hIF
  set sp : P.H (1 + n) := P.cst (Nat.add_comm n 1) (P.io (swapPH n 1)) with hsp
  set spi : P.H (1 + n) := P.cst (Nat.add_comm n 1) (P.io (swapPH n 1)⁻¹) with hspi
  set U : P.H (1 + (1 + n)) := xw (P := P) (1 + n) with hU
  set S : P.H (1 + (1 + n)) := sww (P := P) n with hS
  set W : P.H (1 + (1 + n)) := D.C1 (1 + n) u with hW
  set G : P.H (1 + (1 + n)) := D.C1 (1 + n) K with hG
  set T : P.H (1 + (1 + n)) := D.C1 (1 + n) sp with hT
  set T' : P.H (1 + (1 + n)) := D.C1 (1 + n) spi with hT'
  set Om : P.H (1 + (1 + n)) := D.C1 (1 + n) IF with hOm
  set R : P.H (1 + (1 + n)) := P.tn (P.idm 1) sp with hR
  set Ri : P.H (1 + (1 + n)) := P.tn (P.idm 1) spi with hRi
  -- basic invertibility
  have hspspi : sp * spi = 1 := by
    rw [hsp, hspi]
    show P.cmp _ _ = P.idm (1 + n)
    rw [← P.cst_cmp, P.io_inv_cmp, P.cst_idm]
  have hspisp : spi * sp = 1 := by
    rw [hsp, hspi]
    show P.cmp _ _ = P.idm (1 + n)
    rw [← P.cst_cmp, P.io_cmp_inv, P.cst_idm]
  have hTT' : T * T' = 1 := by rw [hT, hT', ← hmul, hspspi, hone]
  have hT'T : T' * T = 1 := by rw [hT, hT', ← hmul, hspisp, hone]
  have hRRi : R * Ri = 1 := by
    rw [hR, hRi]
    show P.cmp _ _ = P.idm (1 + (1 + n))
    rw [← P.tn_cmp, P.cmp_idm]
    show P.tn (P.idm 1) (sp * spi) = _
    rw [hspspi]
    show P.tn (P.idm 1) (P.idm (1 + n)) = _
    rw [P.tn_idm]
  have hRiR : Ri * R = 1 := by
    rw [hR, hRi]
    show P.cmp _ _ = P.idm (1 + (1 + n))
    rw [← P.tn_cmp, P.cmp_idm]
    show P.tn (P.idm 1) (spi * sp) = _
    rw [hspisp]
    show P.tn (P.idm 1) (P.idm (1 + n)) = _
    rw [P.tn_idm]
  have hUU : U * U = 1 := xw_sq (1 + n)
  have hSS : S * S = 1 := sww_sq n
  -- (e) with (d): the three instances of complementarity used below
  have hE : ∀ g : P.H (1 + n),
      (U * D.C1 (1 + n) g * U) * D.C1 (1 + n) g = P.tn (P.idm 1) g := by
    intro g
    have := he (1 + n) g
    rw [C0_eq hd g] at this
    exact this
  -- (f) : `C₀` values commute with `C₁` values
  have hF : ∀ g₁ g₂ : P.H (1 + n),
      (U * D.C1 (1 + n) g₁ * U) * D.C1 (1 + n) g₂
        = D.C1 (1 + n) g₂ * (U * D.C1 (1 + n) g₁ * U) := by
    intro g₁ g₂
    have := hf (1 + n) g₁ g₂
    rw [C0_eq hd g₁] at this
    exact this
  -- `Ω` in terms of `W` and `G`
  have huKuK : (u * K * u) * K = IF := by
    have := he n f
    rw [C0_eq hd f] at this
    exact this
  have hOmWG : Om = W * G * W * G := by
    rw [hOm, ← huKuK, hmul, hmul, hmul, hW, hG]
  -- `W` squares to one
  have hWW : W * W = 1 := by
    rw [hW, ← hmul, hu, xw_sq n, hone]
  -- the padded symmetry conjugates `U` to `U'`
  have hSU : S * U = (P.tn (P.idm 1) u) * S := sww_mul_xw n
  -- their (h)
  have hHH : S * G = G * S := hh n f
  -- Step: `S * (id₁ + K) * S = Ω`
  have hIKU : P.tn (P.idm 1) K = (U * G * U) * G := (hE K).symm
  have hU'W : P.tn (P.idm 1) u = (U * W * U) * W := (hE u).symm
  have hV1G : (U * W * U) * G = G * (U * W * U) := hF u K
  have hV1W : (U * W * U) * W = W * (U * W * U) := hF u u
  have hV1V1 : (U * W * U) * (U * W * U) = 1 := by
    calc (U * W * U) * (U * W * U) = U * W * (U * U) * W * U := by simp [mul_assoc]
      _ = U * (W * W) * U := by rw [hUU]; simp [mul_assoc]
      _ = U * U := by rw [hWW, mul_one]
      _ = 1 := hUU
  set V : P.H (1 + (1 + n)) := U * W * U with hV
  have hGV : ∀ z : P.H (1 + (1 + n)), G * (V * z) = V * (G * z) := by
    intro z; rw [← mul_assoc, ← hV1G, mul_assoc]
  have hWV : ∀ z : P.H (1 + (1 + n)), W * (V * z) = V * (W * z) := by
    intro z; rw [← mul_assoc, ← hV1W, mul_assoc]
  have hcj : ∀ z w : P.H (1 + (1 + n)), S * (z * w) * S = (S * z * S) * (S * w * S) := by
    intro z w
    calc S * (z * w) * S = S * z * (S * S) * w * S := by rw [hSS]; simp [mul_assoc]
      _ = (S * z * S) * (S * w * S) := by simp [mul_assoc]
  have hcU : S * U * S = P.tn (P.idm 1) u := by rw [hSU, mul_assoc, hSS, mul_one]
  have hcG : S * G * S = G := by rw [hHH, mul_assoc, hSS, mul_one]
  have hstep : S * (P.tn (P.idm 1) K) * S = Om := by
    have hcUGU : S * (U * G * U) * S = (P.tn (P.idm 1) u) * G * (P.tn (P.idm 1) u) := by
      rw [hcj (U * G) U, hcj U G, hcU, hcG]
    rw [hIKU, hcj (U * G * U) G, hcUGU, hcG, hU'W, hOmWG]
    simp only [mul_assoc]
    rw [hGV, hWV, ← mul_assoc, hV1V1, one_mul]
  -- Step: the left side
  have hnatf := P.io_swap_nat (m := n) (n := 1) f (P.idm 1)
  have hcastf : P.cst (Nat.add_comm n 1) ((Nat.add_comm 1 n) ▸ (P.tn (P.idm 1) f))
      = P.tn (P.idm 1) f := by
    show P.cst (Nat.add_comm n 1) (P.cst (Nat.add_comm 1 n) (P.tn (P.idm 1) f)) = _
    rw [P.cst_cst]; rfl
  have hleft : sp * (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1))) = IF * sp := by
    have h := congrArg (P.cst (Nat.add_comm n 1)) hnatf
    rw [P.cst_cmp, P.cst_cmp, hcastf] at h
    exact h
  have hA : D.C1 (1 + n) (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1))) = T' * Om * T := by
    have h0 : P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1)) = spi * IF * sp := by
      calc P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1))
          = 1 * P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1)) := (one_mul _).symm
        _ = (spi * sp) * P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1)) := by rw [hspisp]
        _ = spi * (sp * P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1))) := by rw [mul_assoc]
        _ = spi * (IF * sp) := by rw [hleft]
        _ = spi * IF * sp := by rw [mul_assoc]
    rw [h0, hmul, hmul, hT', hOm, hT]
  -- Step: the right side
  have hβ : (1 + n) + 1 = 1 + (1 + n) := by omega
  set B : P.H (1 + (1 + n)) := P.cst hβ (P.tn K (P.idm 1)) with hB
  have hnatK := P.io_swap_nat (m := 1 + n) (n := 1) K (P.idm 1)
  set S' : P.H (1 + (1 + n)) := P.cst hβ (P.io (swapPH (1 + n) 1)) with hS'
  have hcastK : P.cst hβ ((Nat.add_comm 1 (1 + n)) ▸ (P.tn (P.idm 1) K))
      = P.tn (P.idm 1) K := by
    show P.cst hβ (P.cst (Nat.add_comm 1 (1 + n)) (P.tn (P.idm 1) K)) = _
    rw [P.cst_cst]; rfl
  have hright : S' * B = (P.tn (P.idm 1) K) * S' := by
    have h := congrArg (P.cst hβ) hnatK
    rw [P.cst_cmp, P.cst_cmp, hcastK] at h
    exact h
  -- Step: the factorisation of the block symmetry
  have hSfact : S' = S * R := by
    have hio : P.io (swapPH (1 + n) 1) =
        P.cmp (P.cst (show 2 + n = (1 + n) + 1 by omega) (P.tn (sw (P := P)) (P.idm n)))
          (P.cst (show 1 + (n + 1) = (1 + n) + 1 by omega)
            (P.tn (P.idm 1) (P.io (swapPH n 1)))) := by
      rw [swapPH_succ_one n, P.io_cmp]
      simp only [io_cst, P.io_tn, P.io_one]
      rfl
    have e1 : P.cst hβ (P.cst (show 2 + n = (1 + n) + 1 by omega)
        (P.tn (sw (P := P)) (P.idm n))) = S := by
      rw [P.cst_cst]; rfl
    have e2 : P.cst hβ (P.cst (show 1 + (n + 1) = (1 + n) + 1 by omega)
        (P.tn (P.idm 1) (P.io (swapPH n 1)))) = R := by
      rw [P.cst_cst, hR, hsp, P.tn_cst_right]
    rw [hS', hio, P.cst_cmp, e1, e2]
    rfl
  -- Step: `R = C₀(s) · C₁(s)` and `C₀(s)` commutes with `Ω`
  have hRfact : R = (U * T * U) * T := by rw [hR, hT, hE sp]
  have hV2Om : (U * T * U) * Om = Om * (U * T * U) := by rw [hOm, hT]; exact hF sp IF
  -- conclude
  have hRB : R * B = Om * R := by
    have h1 : S * (S' * B) = S * ((P.tn (P.idm 1) K) * S') := by rw [hright]
    rw [hSfact] at h1
    have h2 : R * B = S * ((P.tn (P.idm 1) K) * (S * R)) := by
      calc R * B = 1 * (R * B) := (one_mul _).symm
        _ = (S * S) * (R * B) := by rw [hSS]
        _ = S * (S * R * B) := by simp [mul_assoc]
        _ = S * ((P.tn (P.idm 1) K) * (S * R)) := h1
    rw [h2]
    calc S * ((P.tn (P.idm 1) K) * (S * R)) = (S * (P.tn (P.idm 1) K) * S) * R := by
          simp [mul_assoc]
      _ = Om * R := by rw [hstep]
  have hRA : R * (T' * Om * T) = Om * R := by
    calc R * (T' * Om * T) = ((U * T * U) * T) * (T' * Om * T) := by rw [hRfact]
      _ = (U * T * U) * (T * T') * (Om * T) := by simp [mul_assoc]
      _ = (U * T * U) * Om * T := by rw [hTT']; simp [mul_assoc]
      _ = Om * ((U * T * U) * T) := by rw [hV2Om]; simp [mul_assoc]
      _ = Om * R := by rw [hRfact]
  have : R * (D.C1 (1 + n) (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1)))) = R * B := by
    rw [hA, hRA, hRB]
  calc D.C1 (1 + n) (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1)))
      = 1 * D.C1 (1 + n) (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1))) := (one_mul _).symm
    _ = (Ri * R) * D.C1 (1 + n) (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1))) := by rw [hRiR]
    _ = Ri * (R * D.C1 (1 + n) (P.cst (Nat.add_comm n 1) (P.tn f (P.idm 1)))) := by
          rw [mul_assoc]
    _ = Ri * (R * B) := by rw [this]
    _ = (Ri * R) * B := by rw [mul_assoc]
    _ = B := by rw [hRiR, one_mul]

/-! ### From the cast-normalised form to their (c) -/

/-- Their **(c) at one padding wire**: `C1 (f + id_1) = C1 f + id_1`. -/
theorem eqC_one {D : Data P} (ha : D.EqA) (hb : D.EqB) (hd : D.EqD) (he : D.EqE)
    (hf : D.EqF) (hh : D.EqH) (n : ℕ) (f : P.H n) :
    D.C1 (n + 1) (P.tn f (P.idm 1))
      = P.cst (show (1 + n) + 1 = 1 + (n + 1) by omega) (P.tn (D.C1 n f) (P.idm 1)) := by
  have hkey := eqC_one_of_others ha hb hd he hf hh n f
  refine P.cst_inj (show 1 + (n + 1) = 1 + (1 + n) by omega) ?_
  rw [← Data.C1_cst, P.cst_cst]
  exact hkey

/-- **Their (c) is derivable.**  In every crop, control data satisfying their
(a), (b), (d), (e), (f) and (h) satisfies their (c).  Since (b) itself follows from (a) and (e)
(`eqB_of_eqA_eqE`), five of the eight listed equations already entail (c); their (g) is not
used. -/
theorem eqC_of_others {D : Data P} (ha : D.EqA) (hb : D.EqB) (hd : D.EqD) (he : D.EqE)
    (hf : D.EqF) (hh : D.EqH) : D.EqC := by
  intro n m
  induction m with
  | zero =>
      intro f
      rw [P.tn_idm_right, P.tn_idm_right]
      rfl
  | succ m ih =>
      intro f
      have hpad : P.tn f (P.idm (m + 1))
          = P.cst (Nat.add_assoc n m 1) (P.tn (P.tn f (P.idm m)) (P.idm 1)) := by
        rw [P.tn_assoc' f (P.idm m) (P.idm 1), P.tn_idm]
      rw [hpad, Data.C1_cst, eqC_one ha hb hd he hf hh (n + m) (P.tn f (P.idm m)), ih,
        P.tn_cst_left, P.cst_cst, P.cst_cst, ← P.tn_idm m 1,
        ← P.tn_assoc' (D.C1 n f) (P.idm m) (P.idm 1), P.cst_cst]


end Ctrl

end Crops
