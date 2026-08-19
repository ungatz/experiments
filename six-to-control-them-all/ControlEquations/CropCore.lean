import ControlEquations.CropPerm

/-!
# Endo-props and crops

A prop whose morphisms are all endomorphisms, the underlying data of a crop in the sense of
Definition 4 of Heunen, Kaarsgaard and Lemonnier, *One rig to control them all* (LICS 2026,
arXiv:2510.05032v3), is the following algebraic gadget: a family of monoids `H n` of morphisms
on `n` wires, a monoidal product `tn : H m → H n → H (m+n)` satisfying interchange and the unit
laws, a strict monoidal inclusion `io` of the permutation prop, and naturality of the block
symmetries.  A crop adds a distinguished involution `x : H 1`.

These are exactly the prop axioms, so anything that typechecks as a `Crop` is a controllable
prop in their sense by construction, rather than by inspection of a model built some other way.
-/

set_option autoImplicit false

namespace Crops

/-- A prop all of whose morphisms are endomorphisms: the underlying data of a crop. -/
structure EndoProp where
  /-- morphisms on `n` wires -/
  H : ℕ → Type
  /-- composition -/
  cmp : {n : ℕ} → H n → H n → H n
  /-- identity -/
  idm : (n : ℕ) → H n
  /-- monoidal product -/
  tn : {m n : ℕ} → H m → H n → H (m + n)
  /-- the inclusion of the permutation prop -/
  io : {n : ℕ} → PH n → H n
  cmp_assoc : ∀ {n : ℕ} (a b c : H n), cmp (cmp a b) c = cmp a (cmp b c)
  idm_cmp : ∀ {n : ℕ} (a : H n), cmp (idm n) a = a
  cmp_idm : ∀ {n : ℕ} (a : H n), cmp a (idm n) = a
  tn_cmp : ∀ {m n : ℕ} (a b : H m) (c d : H n),
      tn (cmp a b) (cmp c d) = cmp (tn a c) (tn b d)
  tn_idm : ∀ (m n : ℕ), tn (idm m) (idm n) = idm (m + n)
  tn_assoc : ∀ {m n p : ℕ} (a : H m) (b : H n) (c : H p),
      (Nat.add_assoc m n p) ▸ (tn (tn a b) c) = tn a (tn b c)
  tn_idm_right : ∀ {m : ℕ} (a : H m), tn a (idm 0) = a
  tn_idm_left : ∀ {m : ℕ} (a : H m), (Nat.zero_add m) ▸ (tn (idm 0) a) = a
  io_cmp : ∀ {n : ℕ} (p q : PH n), io (p * q) = cmp (io p) (io q)
  io_one : ∀ (n : ℕ), io (1 : PH n) = idm n
  io_tn : ∀ {m n : ℕ} (p : PH m) (q : PH n), io (PH.tens p q) = tn (io p) (io q)
  io_swap_nat : ∀ {m n : ℕ} (a : H m) (b : H n),
      cmp (io (swapPH m n)) (tn a b) = cmp ((Nat.add_comm n m) ▸ (tn b a)) (io (swapPH m n))

/-- A crop: an endo-prop with a distinguished involution on one wire. -/
structure Crop extends EndoProp where
  /-- the distinguished involution -/
  invol : H 1
  invol_invol : cmp invol invol = idm 1

namespace EndoProp

variable (P : EndoProp)

/-- Transport a morphism along an equality of wire counts. -/
def cst {m n : ℕ} (h : m = n) (g : P.H m) : P.H n := h ▸ g

@[simp] lemma cst_rfl {m : ℕ} (g : P.H m) : P.cst rfl g = g := rfl

@[simp] lemma cst_cst {m n p : ℕ} (h : m = n) (h' : n = p) (g : P.H m) :
    P.cst h' (P.cst h g) = P.cst (h.trans h') g := by subst h; subst h'; rfl

@[simp] lemma cst_cmp {m n : ℕ} (h : m = n) (a b : P.H m) :
    P.cst h (P.cmp a b) = P.cmp (P.cst h a) (P.cst h b) := by subst h; rfl

@[simp] lemma cst_idm {m n : ℕ} (h : m = n) : P.cst h (P.idm m) = P.idm n := by subst h; rfl

lemma cst_inj {m n : ℕ} (h : m = n) {a b : P.H m} (e : P.cst h a = P.cst h b) : a = b := by
  subst h; exact e

lemma cst_eq_iff {m n : ℕ} (h : m = n) {a : P.H m} {b : P.H n} :
    P.cst h a = b ↔ a = P.cst h.symm b := by subst h; simp

/-- Whiskering a cast on the left of a tensor. -/
lemma tn_cst_left {m m' n : ℕ} (h : m = m') (a : P.H m) (b : P.H n) :
    P.tn (P.cst h a) b = P.cst (by rw [h]) (P.tn a b) := by subst h; rfl

/-- Whiskering a cast on the right of a tensor. -/
lemma tn_cst_right {m n n' : ℕ} (h : n = n') (a : P.H m) (b : P.H n) :
    P.tn a (P.cst h b) = P.cst (by rw [h]) (P.tn a b) := by subst h; rfl

/-- Associativity of the monoidal product, phrased with `cst`. -/
lemma tn_assoc' {m n p : ℕ} (a : P.H m) (b : P.H n) (c : P.H p) :
    P.cst (Nat.add_assoc m n p) (P.tn (P.tn a b) c) = P.tn a (P.tn b c) := P.tn_assoc a b c

/-- Left unit law, phrased with `cst`. -/
lemma tn_idm_left' {m : ℕ} (a : P.H m) : P.cst (Nat.zero_add m) (P.tn (P.idm 0) a) = a :=
  P.tn_idm_left a

lemma tn_cmp_idm_right {m n : ℕ} (a b : P.H m) :
    P.tn (P.cmp a b) (P.idm n) = P.cmp (P.tn a (P.idm n)) (P.tn b (P.idm n)) := by
  rw [← P.tn_cmp a b (P.idm n) (P.idm n), P.cmp_idm]

lemma tn_cmp_idm_left {m n : ℕ} (a b : P.H n) :
    P.tn (P.idm m) (P.cmp a b) = P.cmp (P.tn (P.idm m) a) (P.tn (P.idm m) b) := by
  rw [← P.tn_cmp (P.idm m) (P.idm m) a b, P.cmp_idm]

lemma io_tn_idm {m j : ℕ} (p : PH m) :
    P.tn (P.io p) (P.idm j) = P.io (PH.tens p (1 : PH j)) := by
  rw [P.io_tn p (1 : PH j), P.io_one]

lemma io_idm_tn {m j : ℕ} (p : PH j) :
    P.tn (P.idm m) (P.io p) = P.io (PH.tens (1 : PH m) p) := by
  rw [P.io_tn (1 : PH m) p, P.io_one]

lemma io_inv_cmp {n : ℕ} (p : PH n) : P.cmp (P.io p) (P.io p⁻¹) = P.idm n := by
  rw [← P.io_cmp, mul_inv_cancel, P.io_one]

lemma io_cmp_inv {n : ℕ} (p : PH n) : P.cmp (P.io p⁻¹) (P.io p) = P.idm n := by
  rw [← P.io_cmp, inv_mul_cancel, P.io_one]

end EndoProp

end Crops
