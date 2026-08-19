import ControlEquations.CtrlGraded
import ControlEquations.CropSign

/-!
# Signed graded-constant crops

The graded-constant crops of `ControlEquations.CtrlGraded` have a trivial symmetry inclusion, and
for that reason their (h) holds in all of them.  This file enlarges the family: the inclusion of
the permutation prop is now the sign of a permutation, sent to a distinguished involution `s` of
the monoid.  That is the largest inclusion available in this collapsed setting, since every
group homomorphism out of `S n` for `n ≥ 2` factors through the abelianisation.

Even with a nontrivial symmetry the family stays blind to their (c) and (h): in every signed
graded-constant crop, their (a), (d), (e) and (g) already force `al x = 1`, after which (c) and
(h) both hold.  A crop separating either of them has to leave the family altogether.

The mechanism is a small piece of group theory.  Their (e) makes `y = C1 x` invertible with
`y⁻² = al x`, their (g) makes `y * s` of order three, and the resulting relations force
`al x = 1`.
-/

set_option autoImplicit false

namespace Crops

namespace Ctrl

/-! ### The group-theoretic core -/

/-- The core computation.  In a monoid, suppose `a` and `s` are commuting involutions,
`y` satisfies `a * y * (a * y) = a` — which is their (e) evaluated at the distinguished
involution, once (d) has been used to eliminate `C0` — and `y * (s * (y * (s * y))) = s`, which
is their (g).  Then `a = 1`.

The argument: `y` is invertible with inverse `z = a * y`; their (g) says `(y*s)³ = 1`, and
transporting it along `z` gives `(z*s)³ = 1`; but `z*s = a*(y*s)` with `a` central for `y` and
`s`, so `(z*s)³ = a³ * (y*s)³ = a`. -/
theorem alx_trivial_core {M : Type*} [Monoid M] {a s y : M}
    (haa : a * a = 1) (hss : s * s = 1) (has : a * s = s * a)
    (he : a * y * (a * y) = a) (hg : y * (s * (y * (s * y))) = s) : a = 1 := by
  -- `y` is invertible, with two-sided inverse `z = a * y`
  set z : M := a * y with hz
  -- after `set`, the hypothesis (e) reads `z * z = a`
  have haz : a * z = y := by rw [hz, ← mul_assoc, haa, one_mul]
  have hza : z * a = y := by rw [← he, ← mul_assoc, he, haz]
  have hyz : y * z = 1 := by
    calc y * z = a * z * z := by rw [haz]
      _ = a * (z * z) := by rw [mul_assoc]
      _ = a * a := by rw [he]
      _ = 1 := haa
  have hzy : z * y = 1 := by
    have h2 : z * a * z = 1 := by rw [hza]; exact hyz
    rw [mul_assoc, haz] at h2
    exact h2
  -- `a` commutes with `y`
  have hay : a * y = y * a := by
    have hya : y * a = z := by rw [← hza, mul_assoc, haa, mul_one]
    rw [← hz, hya]
  have haw : a * (y * s) = y * s * a := by
    calc a * (y * s) = a * y * s := by rw [mul_assoc]
      _ = y * a * s := by rw [hay]
      _ = y * (a * s) := by rw [mul_assoc]
      _ = y * (s * a) := by rw [has]
      _ = y * s * a := by rw [mul_assoc]
  -- their (g), rearranged: `w = y * s` has order dividing three
  have hw3 : y * s * (y * s) * (y * s) = 1 := by
    calc y * s * (y * s) * (y * s) = y * (s * (y * (s * y))) * s := by simp [mul_assoc]
      _ = s * s := by rw [hg]
      _ = 1 := hss
  -- `s * z` is the inverse of `w`, hence equals `w * w`
  have hszw : s * z * (y * s) = 1 := by
    calc s * z * (y * s) = s * (z * y) * s := by simp [mul_assoc]
      _ = s * s := by rw [hzy, mul_one]
      _ = 1 := hss
  have hsz : s * z = y * s * (y * s) := by
    calc s * z = s * z * (y * s * (y * s) * (y * s)) := by rw [hw3, mul_one]
      _ = (s * z * (y * s)) * (y * s * (y * s)) := by simp [mul_assoc]
      _ = y * s * (y * s) := by rw [hszw, one_mul]
  have hsz3 : s * z * (s * z) * (s * z) = 1 := by
    rw [hsz]
    calc y * s * (y * s) * (y * s * (y * s)) * (y * s * (y * s))
        = (y * s * (y * s) * (y * s)) * (y * s * (y * s) * (y * s)) := by simp [mul_assoc]
      _ = 1 := by rw [hw3, mul_one]
  -- hence `z * s` also has order dividing three
  have hzs3 : z * s * (z * s) * (z * s) = 1 := by
    calc z * s * (z * s) * (z * s) = z * s * (z * s) * (z * s) * (z * y) := by
          rw [hzy, mul_one]
      _ = z * (s * z * (s * z) * (s * z)) * y := by simp [mul_assoc]
      _ = z * y := by rw [hsz3, mul_one]
      _ = 1 := hzy
  -- but `z * s = a * (y * s)` and `a` commutes with `y * s`, so that product is `a`
  have hcube : ∀ t : M, t * t * t = t ^ 3 := fun t => by rw [pow_succ, pow_succ, pow_one]
  have hc : Commute a (y * s) := haw
  have h1 : z * s = a * (y * s) := by rw [hz, mul_assoc]
  have hfin : (1 : M) = a := by
    calc (1 : M) = z * s * (z * s) * (z * s) := hzs3.symm
      _ = (a * (y * s)) ^ 3 := by rw [h1, hcube]
      _ = a ^ 3 * (y * s) ^ 3 := hc.mul_pow 3
      _ = a ^ 3 * 1 := by rw [← hcube (y * s), hw3]
      _ = a * a * a := by rw [mul_one, ← hcube a]
      _ = a := by rw [haa, one_mul]
  exact hfin.symm

/-! ### First consequence: the unsigned graded-constant class, with no finiteness -/

/-- **Over *every* graded-constant crop — finite or not — their (c) follows from their (a),
(d), (e) and (g).**

This strengthens `eqC_of_finite_graded` (which uses only (a), (d), (e), but needs the hom-monoid
to be finite): here the finiteness hypothesis is traded for their equation (g). -/
theorem eqC_of_graded {M : Type} [Monoid M] (G : GradedData M) (c0 c1 : M → M)
    (ha : (G.ctrl c0 c1).EqA) (hd : (G.ctrl c0 c1).EqD) (he : (G.ctrl c0 c1).EqE)
    (hg : (G.ctrl c0 c1).EqG) : (G.ctrl c0 c1).EqC := by
  rw [G.eqA_iff] at ha
  rw [G.eqD_iff] at hd
  rw [G.eqE_iff] at he
  rw [G.eqG_iff] at hg
  obtain ⟨-, hd⟩ := hd
  set a : M := G.al G.x with hadef
  have haa : a * a = 1 := by rw [hadef, ← map_mul, G.x_invol, map_one]
  have hc0 : ∀ u : M, c0 u = a * c1 u * a := by
    intro u
    calc c0 u = 1 * c0 u * 1 := by rw [one_mul, mul_one]
      _ = a * a * c0 u * (a * a) := by rw [haa]
      _ = a * (a * c0 u * a) * a := by simp [mul_assoc]
      _ = a * c1 u * a := by rw [hd u]
  have hex : a * c1 G.x * (a * c1 G.x) = a := by
    have h := he G.x
    rw [hc0 G.x] at h
    calc a * c1 G.x * (a * c1 G.x) = a * c1 G.x * a * c1 G.x := by simp [mul_assoc]
      _ = a := h
  have hg' : c1 G.x * (1 * (c1 G.x * (1 * c1 G.x))) = 1 := by simpa using hg
  have ha1 : a = 1 := alx_trivial_core haa (one_mul (1 : M)) (by rw [one_mul, mul_one]) hex hg'
  have hc0' : ∀ u : M, c0 u = c1 u := by
    intro u
    rw [hc0 u, ha1, one_mul, mul_one]
  have hsq : ∀ u : M, c1 u * c1 u = G.al u := by
    intro u
    have := he u
    rwa [hc0' u] at this
  rw [G.eqC_iff]
  intro u
  calc c1 (G.al u) = c1 (c1 u * c1 u) := by rw [hsq]
    _ = c1 (c1 u) * c1 (c1 u) := ha _ _
    _ = G.al (c1 u) := hsq _

/-! ### Signed graded-constant crops -/

variable {M : Type} [Monoid M]

/-- A graded-constant crop together with a distinguished involution `s` in the image of `al`,
used as the value of the sign of a wire permutation. -/
structure SignedData (M : Type) [Monoid M] extends GradedData M where
  /-- the value of the sign -/
  s : M
  /-- it is an involution -/
  s_invol : s * s = 1
  /-- it lies in the image of `al` (hence commutes with that image) -/
  s_fix : al s = s

namespace SignedData

variable (S : SignedData M)

/-- The element of `M` attached to a sign. -/
def sgnElt (e : ℤˣ) : M := if e = 1 then 1 else S.s

@[simp] lemma sgnElt_one : S.sgnElt 1 = 1 := by simp [sgnElt]

@[simp] lemma sgnElt_neg_one : S.sgnElt (-1) = S.s := by
  simp [sgnElt, (by decide : (-1 : ℤˣ) ≠ 1)]

lemma sgnElt_mul (e f : ℤˣ) : S.sgnElt (e * f) = S.sgnElt e * S.sgnElt f := by
  rcases Int.units_eq_one_or e with rfl | rfl <;> rcases Int.units_eq_one_or f with rfl | rfl <;>
    simp [S.s_invol]

lemma al_sgnElt (e : ℤˣ) : S.al (S.sgnElt e) = S.sgnElt e := by
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp [S.s_fix]

lemma sgnElt_comm_al (e : ℤˣ) (u : M) : S.sgnElt e * S.al u = S.al u * S.sgnElt e := by
  rw [← S.al_sgnElt e]
  exact S.al_comm _ _

/-! #### The sign of a wire permutation, multiplicatively -/

lemma zElim_zMk_one (n : ℕ) : zElim n (zMk n (1 : M)) = 1 := by
  cases n <;> rfl

lemma phSign_tens {m n : ℕ} (a : PH m) (b : PH n) :
    phSign (PH.tens a b) = phSign a * phSign b := by
  have h : PH.tens a b = PH.emb (Nat.le_add_right m n) a * shiftPH m b := by
    apply PH.ext'
    simp
  rw [h, phSign_mul, phSign_emb, phSign_shiftPH]

lemma ph_zero_eq_one (p : PH 0) : p = 1 := by
  apply PH.ext'
  ext i
  exact p.2 i (Nat.zero_le i)

lemma phSign_zero (p : PH 0) : phSign p = 1 := by
  rw [ph_zero_eq_one p, phSign_one]

lemma phFin_swap11 : phFin (swapPH 1 1) = Equiv.swap 0 1 := by
  ext i
  fin_cases i <;> simp [phFin, swapPH_apply]

lemma phSign_swap11 : phSign (swapPH 1 1) = -1 := by
  rw [phSign, phFin_swap11]
  exact Equiv.Perm.sign_swap (by decide)

/-! #### The crop -/

/-- The endo-prop of a signed graded-constant crop: as in `GradedData.endoProp`, but the
permutation prop is included through the sign. -/
def endoProp : EndoProp :=
  { H := ZH M
    cmp := zCmp
    idm := zIdm
    tn := zTn S.al
    cmp_assoc := S.toGradedData.endoProp.cmp_assoc
    idm_cmp := S.toGradedData.endoProp.idm_cmp
    cmp_idm := S.toGradedData.endoProp.cmp_idm
    tn_cmp := S.toGradedData.endoProp.tn_cmp
    tn_idm := S.toGradedData.endoProp.tn_idm
    tn_assoc := S.toGradedData.endoProp.tn_assoc
    tn_idm_right := S.toGradedData.endoProp.tn_idm_right
    tn_idm_left := S.toGradedData.endoProp.tn_idm_left
    io := fun {n} p => zMk n (S.sgnElt (phSign p))
    io_cmp := by
      intro n p q
      refine z_ext ?_
      rw [zElim_zCmp]
      cases n with
      | zero => simp
      | succ k =>
        rw [zElim_zMk_pos (by omega), zElim_zMk_pos (by omega), zElim_zMk_pos (by omega),
          phSign_mul, S.sgnElt_mul]
    io_one := by
      intro n
      refine z_ext ?_
      cases n with
      | zero => simp
      | succ k => rw [zElim_zMk_pos (by omega), phSign_one, S.sgnElt_one, zElim_zIdm]
    io_tn := by
      intro m n p q
      refine z_ext ?_
      rw [zElim_zTn]
      by_cases hmn : m + n = 0
      · have hm : m = 0 := by omega
        have hn : n = 0 := by omega
        subst hm; subst hn; simp [tsel]
      · rw [zElim_zMk_pos hmn]
        by_cases hm : m = 0
        · subst hm
          have hn : n ≠ 0 := by omega
          rw [tsel_zero_left, zElim_zMk_pos hn, phSign_tens, phSign_zero p, one_mul]
        · by_cases hn : n = 0
          · subst hn
            rw [tsel_zero_right _ hm, zElim_zMk_pos hm, phSign_tens, phSign_zero q, mul_one]
          · rw [tsel_pos _ hm hn, zElim_zMk_pos hm, zElim_zMk_pos hn, S.al_sgnElt, S.al_sgnElt,
              phSign_tens, S.sgnElt_mul]
    io_swap_nat := by
      intro m n a b
      refine z_ext ?_
      simp only [zElim_zCmp, zElim_cst, zElim_zTn]
      by_cases hm : m = 0
      · subst hm
        rw [swapPH_zero_left]
        by_cases hn : n = 0
        · subst hn; simp [tsel]
        · rw [tsel_zero_left, tsel_zero_right _ hn, phSign_one, S.sgnElt_one, zElim_zMk_one,
            one_mul, mul_one]
      · by_cases hn : n = 0
        · subst hn
          rw [swapPH_zero_right]
          simp [tsel, hm]
        · rw [zElim_zMk_pos (by omega : m + n ≠ 0), tsel_pos _ hm hn, tsel_pos _ hn hm]
          calc S.sgnElt (phSign (swapPH m n)) * (S.al (zElim m a) * S.al (zElim n b))
              = S.al (zElim m a) * (S.sgnElt (phSign (swapPH m n)) * S.al (zElim n b)) := by
                rw [← mul_assoc, S.sgnElt_comm_al, mul_assoc]
            _ = S.al (zElim m a) * (S.al (zElim n b) * S.sgnElt (phSign (swapPH m n))) := by
                rw [S.sgnElt_comm_al]
            _ = S.al (zElim n b) * S.al (zElim m a) * S.sgnElt (phSign (swapPH m n)) := by
                rw [S.al_comm]; simp [mul_assoc] }

/-- The signed graded-constant crop. -/
def crop (S : SignedData M) : Crop where
  toEndoProp := S.endoProp
  invol := S.x
  invol_invol := by
    show zCmp (S.x : ZH M 1) S.x = zIdm 1
    exact z_ext (by simpa [zCmp, zIdm] using S.x_invol)

@[simp] lemma crop_cmp {n : ℕ} (a b : ZH M n) : (S.crop).cmp a b = zCmp a b := rfl

@[simp] lemma crop_idm (n : ℕ) : (S.crop).idm n = zIdm n := rfl

@[simp] lemma crop_tn {m n : ℕ} (a : ZH M m) (b : ZH M n) :
    (S.crop).tn a b = zTn S.al a b := rfl

@[simp] lemma crop_io {n : ℕ} (p : PH n) : (S.crop).io p = zMk n (S.sgnElt (phSign p)) := rfl

@[simp] lemma crop_invol : (S.crop).invol = S.x := rfl

/-- Control data on a signed graded-constant crop, given by two functions on the monoid. -/
def ctrl (S : SignedData M) (c0 c1 : M → M) : Data S.crop where
  C0 n a := zMk (1 + n) (c0 (zElim n a))
  C1 n a := zMk (1 + n) (c1 (zElim n a))

variable (c0 c1 : M → M)

@[simp] lemma zElim_C1' (n : ℕ) (a : ZH M n) :
    zElim (1 + n) ((S.ctrl c0 c1).C1 n a) = c1 (zElim n a) :=
  zElim_zMk_pos (by omega) _

@[simp] lemma zElim_C0' (n : ℕ) (a : ZH M n) :
    zElim (1 + n) ((S.ctrl c0 c1).C0 n a) = c0 (zElim n a) :=
  zElim_zMk_pos (by omega) _

/-! #### The eight equations over a signed graded-constant crop

Equations (a)–(f) do not mention the permutation inclusion, so they read exactly as in the
unsigned case; (g) and (h) do mention it, and pick up the element `s`. -/

lemma eqA_iff' : (S.ctrl c0 c1).EqA ↔ ∀ u v : M, c1 (v * u) = c1 v * c1 u :=
  S.toGradedData.eqA_iff c0 c1

lemma eqC_iff' : (S.ctrl c0 c1).EqC ↔ ∀ u : M, c1 (S.al u) = S.al (c1 u) :=
  S.toGradedData.eqC_iff c0 c1

lemma eqD_iff' : (S.ctrl c0 c1).EqD ↔
    ((S.x * c0 1 * S.x = c1 1) ∧ ∀ u : M, S.al S.x * c0 u * S.al S.x = c1 u) :=
  S.toGradedData.eqD_iff c0 c1

lemma eqE_iff' : (S.ctrl c0 c1).EqE ↔ ∀ u : M, c0 u * c1 u = S.al u :=
  S.toGradedData.eqE_iff c0 c1

lemma eqF_iff' : (S.ctrl c0 c1).EqF ↔ ∀ u v : M, c0 u * c1 v = c1 v * c0 u :=
  S.toGradedData.eqF_iff c0 c1

lemma zElim_sw : zElim (M := M) 2 (sw (P := S.crop)) = S.s := by
  show zElim (M := M) 2 (zMk 2 (S.sgnElt (phSign (swapPH 1 1)))) = S.s
  rw [phSign_swap11]
  simp

lemma zElim_cropCst' {m n : ℕ} (h : m = n) (a : ZH M m) :
    zElim n ((S.crop).cst h a) = zElim m a := by
  cases h; rfl

lemma zElim_sww (n : ℕ) : zElim (M := M) (1 + (1 + n)) (sww (P := S.crop) n) = S.s := by
  unfold sww
  rw [S.zElim_cropCst', crop_tn, crop_idm, zElim_zTn]
  by_cases hn : n = 0
  · subst hn
    rw [tsel_zero_right _ (by omega), S.zElim_sw]
  · rw [tsel_pos _ (by omega) hn, S.zElim_sw, zElim_zIdm, map_one, mul_one, S.s_fix]

lemma eqG_iff' :
    (S.ctrl c0 c1).EqG ↔ c1 S.x * (S.s * (c1 S.x * (S.s * c1 S.x))) = S.s := by
  have hcx : zElim (M := M) 2 ((S.ctrl c0 c1).C1 1 ((S.crop).invol)) = c1 S.x := by
    show zElim (M := M) (1 + 1) _ = _
    rw [zElim_C1']
    rfl
  unfold Data.EqG
  constructor
  · intro h
    have h' := congrArg (zElim (M := M) 2) h
    simpa only [crop_cmp, zElim_zCmp, S.zElim_sw, hcx] using h'
  · intro h
    refine z_ext (M := M) (n := 2) ?_
    simpa only [crop_cmp, zElim_zCmp, S.zElim_sw, hcx] using h

lemma eqH_iff' :
    (S.ctrl c0 c1).EqH ↔ ∀ u : M, S.s * c1 (c1 u) = c1 (c1 u) * S.s := by
  constructor
  · intro h u
    have h' := congrArg (zElim (M := M) (1 + (1 + 1))) (h 1 (zMk 1 u : ZH M 1))
    simpa only [crop_cmp, zElim_zCmp, S.zElim_sww, zElim_C1', zElim_zMk_pos (by omega : (1:ℕ) ≠ 0)]
      using h'
  · intro h n f
    refine z_ext ?_
    simp only [crop_cmp, zElim_zCmp, S.zElim_sww, zElim_C1']
    exact h (zElim n f)

/-! ### The blindness theorem -/

/-- **In every signed graded-constant crop, their (a), (d), (e) and (g) force `al x = 1`.**

This is the obstruction that makes the class blind to the independence of (c) and of (h): no
finiteness is assumed, and the class has a nontrivial symmetry inclusion. -/
theorem signed_alx_eq_one (hd : (S.ctrl c0 c1).EqD)
    (he : (S.ctrl c0 c1).EqE) (hg : (S.ctrl c0 c1).EqG) : S.al S.x = 1 := by
  rw [S.eqD_iff'] at hd
  rw [S.eqE_iff'] at he
  rw [S.eqG_iff'] at hg
  obtain ⟨-, hd⟩ := hd
  set a : M := S.al S.x with hadef
  have haa : a * a = 1 := by rw [hadef, ← map_mul, S.x_invol, map_one]
  have hc0 : ∀ u : M, c0 u = a * c1 u * a := by
    intro u
    calc c0 u = 1 * c0 u * 1 := by rw [one_mul, mul_one]
      _ = a * a * c0 u * (a * a) := by rw [haa]
      _ = a * (a * c0 u * a) * a := by simp [mul_assoc]
      _ = a * c1 u * a := by rw [hd u]
  have hex : a * c1 S.x * (a * c1 S.x) = a := by
    have h := he S.x
    rw [hc0 S.x] at h
    calc a * c1 S.x * (a * c1 S.x) = a * c1 S.x * a * c1 S.x := by simp [mul_assoc]
      _ = a := h
  have has : a * S.s = S.s * a := by
    rw [hadef, ← S.s_fix]
    exact S.al_comm _ _
  exact alx_trivial_core haa S.s_invol has hex hg

/-- **No signed graded-constant crop witnesses the independence of their (c):** over that class
(c) follows from (a), (d), (e) and (g). -/
theorem eqC_of_signed (ha : (S.ctrl c0 c1).EqA) (hd : (S.ctrl c0 c1).EqD)
    (he : (S.ctrl c0 c1).EqE) (hg : (S.ctrl c0 c1).EqG) : (S.ctrl c0 c1).EqC := by
  have ha1 := S.signed_alx_eq_one c0 c1 hd he hg
  rw [S.eqA_iff'] at ha
  rw [S.eqD_iff'] at hd
  rw [S.eqE_iff'] at he
  obtain ⟨-, hd⟩ := hd
  have hc0 : ∀ u : M, c0 u = c1 u := by
    intro u
    have := hd u
    rw [ha1, one_mul, mul_one] at this
    exact this
  have hsq : ∀ u : M, c1 u * c1 u = S.al u := by
    intro u
    have := he u
    rwa [hc0 u] at this
  rw [S.eqC_iff']
  intro u
  calc c1 (S.al u) = c1 (c1 u * c1 u) := by rw [hsq]
    _ = c1 (c1 u) * c1 (c1 u) := ha _ _
    _ = S.al (c1 u) := hsq _

/-- **No signed graded-constant crop witnesses the independence of their (h):** over that class
(h) follows from (a), (d), (e), (f) and (g).

Note that the class does have a nontrivial symmetry inclusion, so this is not the trivial
observation of `eqH_of_trivial_symmetry`. -/
theorem eqH_of_signed (hd : (S.ctrl c0 c1).EqD)
    (he : (S.ctrl c0 c1).EqE) (hf : (S.ctrl c0 c1).EqF) (hg : (S.ctrl c0 c1).EqG) :
    (S.ctrl c0 c1).EqH := by
  have ha1 := S.signed_alx_eq_one c0 c1 hd he hg
  rw [S.eqD_iff'] at hd
  rw [S.eqE_iff'] at he
  rw [S.eqF_iff'] at hf
  obtain ⟨-, hd⟩ := hd
  have hc0 : ∀ u : M, c0 u = c1 u := by
    intro u
    have := hd u
    rw [ha1, one_mul, mul_one] at this
    exact this
  have hcomm : ∀ u v : M, c1 u * c1 v = c1 v * c1 u := by
    intro u v
    have := hf u v
    rwa [hc0 u] at this
  have hsq : ∀ u : M, c1 u * c1 u = S.al u := by
    intro u
    have := he u
    rwa [hc0 u] at this
  -- `s` is in the image of `al`, hence a square of a value of `c1`
  have hs : S.s = c1 S.s * c1 S.s := by rw [hsq, S.s_fix]
  rw [S.eqH_iff']
  intro u
  calc S.s * c1 (c1 u) = c1 S.s * c1 S.s * c1 (c1 u) := by rw [← hs]
    _ = c1 S.s * (c1 S.s * c1 (c1 u)) := by rw [mul_assoc]
    _ = c1 S.s * (c1 (c1 u) * c1 S.s) := by rw [hcomm]
    _ = c1 S.s * c1 (c1 u) * c1 S.s := by rw [mul_assoc]
    _ = c1 (c1 u) * c1 S.s * c1 S.s := by rw [hcomm]
    _ = c1 (c1 u) * S.s := by rw [mul_assoc, ← hs]

/-! ### The class really does have a nontrivial symmetry

The blindness theorems above would be uninteresting if every signed graded-constant crop had a
trivial symmetry inclusion; it does not.  Here is one with `s ≠ 1`, whose symmetry `σ_{1,1}` is
therefore *not* the identity morphism. -/

/-- A signed graded-constant crop over `Multiplicative (ZMod 2)` whose sign element is the
nontrivial one. -/
def sigNontriv : SignedData (Multiplicative (ZMod 2)) where
  al := MonoidHom.id _
  al_idem _ := rfl
  al_comm g h := mul_comm g h
  x := 1
  x_invol := one_mul 1
  s := Multiplicative.ofAdd 1
  s_invol := by decide
  s_fix := rfl

/-- The symmetry inclusion of `sigNontriv.crop` is not trivial: `σ_{1,1}` is not the identity. -/
theorem sigNontriv_symmetry_nontrivial :
    (sigNontriv.crop).io (swapPH 1 1) ≠ (sigNontriv.crop).idm 2 := by
  intro h
  have h1 := sigNontriv.zElim_sw
  rw [sw, h] at h1
  simp only [crop_idm, zElim_zIdm] at h1
  exact absurd h1.symm (by decide)

end SignedData

end Ctrl

end Crops
