import Mathlib

/-!
# Wire permutations

The prop `PH` of wire permutations, in the form used throughout: a morphism on `n` wires is a
permutation of `ℕ` fixing everything from `n` upwards.  With this model, padding a morphism on
`n` wires with an unused wire on the right does not change the underlying data, which keeps the
arithmetic of wire counts out of the way.
-/

set_option autoImplicit false

namespace Crops

/-- Shift a permutation of `ℕ` up by `m`: it fixes `[0,m)` and acts as `σ` above `m`. -/
def shiftPerm (m : ℕ) (σ : Equiv.Perm ℕ) : Equiv.Perm ℕ where
  toFun i := if i < m then i else σ (i - m) + m
  invFun i := if i < m then i else σ.symm (i - m) + m
  left_inv := by
    intro i
    by_cases h : i < m
    · simp [h]
    · have h2 : ¬ (σ (i - m) + m < m) := by omega
      simp only [h, h2, if_false]
      have : σ (i - m) + m - m = σ (i - m) := by omega
      rw [this]; simp; omega
  right_inv := by
    intro i
    by_cases h : i < m
    · simp [h]
    · have h2 : ¬ (σ.symm (i - m) + m < m) := by omega
      simp only [h, h2, if_false]
      have : σ.symm (i - m) + m - m = σ.symm (i - m) := by omega
      rw [this]; simp; omega

@[simp] lemma shiftPerm_apply (m : ℕ) (σ : Equiv.Perm ℕ) (i : ℕ) :
    shiftPerm m σ i = if i < m then i else σ (i - m) + m := rfl

@[simp] lemma shiftPerm_symm_apply (m : ℕ) (σ : Equiv.Perm ℕ) (i : ℕ) :
    (shiftPerm m σ).symm i = if i < m then i else σ.symm (i - m) + m := rfl

@[simp] lemma shiftPerm_one (m : ℕ) : shiftPerm m (1 : Equiv.Perm ℕ) = 1 := by
  ext i; simp; omega

@[simp] lemma shiftPerm_zero (σ : Equiv.Perm ℕ) : shiftPerm 0 σ = σ := by
  ext i; simp

lemma shiftPerm_mul (m : ℕ) (σ τ : Equiv.Perm ℕ) :
    shiftPerm m (σ * τ) = shiftPerm m σ * shiftPerm m τ := by
  ext i
  by_cases h : i < m
  · simp [h]
  · have : ¬ (τ (i - m) + m < m) := by omega
    simp [h, this]

lemma shiftPerm_add (m m' : ℕ) (σ : Equiv.Perm ℕ) :
    shiftPerm (m + m') σ = shiftPerm m (shiftPerm m' σ) := by
  ext i
  simp only [shiftPerm_apply]
  by_cases h : i < m
  · have h1 : i < m + m' := by omega
    simp [h, h1]
  · by_cases h2 : i < m + m'
    · have h3 : i - m < m' := by omega
      simp only [h, h2, h3, if_false, if_true]
      congr 2
      omega
    · have h3 : ¬ (i - m < m') := by omega
      have h4 : i - m - m' = i - (m + m') := by omega
      simp [h, h2, h3, h4]; omega

/-- The subgroup of permutations of `ℕ` fixing everything `≥ n`: the hom-monoid of the
permutation prop on `n` wires. -/
def PHsub (n : ℕ) : Subgroup (Equiv.Perm ℕ) where
  carrier := {σ | ∀ i, n ≤ i → σ i = i}
  mul_mem' := by intro a b ha hb i hi; simp [Equiv.Perm.mul_apply, hb i hi, ha i hi]
  one_mem' := by intro i _; rfl
  inv_mem' := by intro a ha i hi; exact (Equiv.symm_apply_eq a).2 (ha i hi).symm

/-- Morphisms on `n` wires in the permutation prop. -/
abbrev PH (n : ℕ) := ↥(PHsub n)

lemma PH.fix {n : ℕ} (a : PH n) {i : ℕ} (hi : n ≤ i) : (a : Equiv.Perm ℕ) i = i := a.2 i hi

lemma PH.lt {n : ℕ} (a : PH n) {i : ℕ} (hi : i < n) : (a : Equiv.Perm ℕ) i < n := by
  by_contra h
  have h1 : (a : Equiv.Perm ℕ) ((a : Equiv.Perm ℕ) i) = (a : Equiv.Perm ℕ) i :=
    a.2 _ (by omega)
  have := (a : Equiv.Perm ℕ).injective h1
  omega

@[simp] lemma PH.coe_mul {n : ℕ} (a b : PH n) :
    ((a * b : PH n) : Equiv.Perm ℕ) = (a : Equiv.Perm ℕ) * b := rfl

@[simp] lemma PH.coe_inv {n : ℕ} (a : PH n) :
    ((a⁻¹ : PH n) : Equiv.Perm ℕ) = (a : Equiv.Perm ℕ)⁻¹ := rfl

lemma shiftPerm_inv (m : ℕ) (σ : Equiv.Perm ℕ) :
    shiftPerm m σ⁻¹ = (shiftPerm m σ)⁻¹ := by
  rw [eq_comm, inv_eq_iff_mul_eq_one, ← shiftPerm_mul, mul_inv_cancel, shiftPerm_one]

@[simp] lemma PH.coe_one (n : ℕ) : ((1 : PH n) : Equiv.Perm ℕ) = 1 := rfl

/-- Casting along an equality of wire counts does not change the underlying permutation. -/
@[simp] lemma PH.coe_cast {m n : ℕ} (h : m = n) (a : PH m) :
    ((h ▸ a : PH n) : Equiv.Perm ℕ) = (a : Equiv.Perm ℕ) := by subst h; rfl

lemma PH.ext' {n : ℕ} {a b : PH n} (h : (a : Equiv.Perm ℕ) = b) : a = b := Subtype.ext h

/-- Monoidal product of the permutation prop: `a` on the first `m` wires, `b` on the next `n`. -/
def PH.tens {m n : ℕ} (a : PH m) (b : PH n) : PH (m + n) :=
  ⟨(a : Equiv.Perm ℕ) * shiftPerm m (b : Equiv.Perm ℕ), by
    intro i hi
    have h1 : ¬ (i < m) := by omega
    simp only [Equiv.Perm.mul_apply, shiftPerm_apply, h1, if_false]
    rw [b.2 (i - m) (by omega)]
    have : i - m + m = i := by omega
    rw [this, a.2 i (by omega)]⟩

@[simp] lemma PH.coe_tens {m n : ℕ} (a : PH m) (b : PH n) :
    ((PH.tens a b : PH (m + n)) : Equiv.Perm ℕ) = (a : Equiv.Perm ℕ) * shiftPerm m b := rfl

lemma PH.tens_mul {m n : ℕ} (a b : PH m) (c d : PH n) :
    PH.tens (a * b) (c * d) = PH.tens a c * PH.tens b d := by
  apply PH.ext'
  simp only [PH.coe_tens, PH.coe_mul, shiftPerm_mul]
  -- `a b (c d)` versus `a c b d`; `b` and `c` act on disjoint blocks
  have hcomm : shiftPerm m (c : Equiv.Perm ℕ) * (b : Equiv.Perm ℕ)
      = (b : Equiv.Perm ℕ) * shiftPerm m (c : Equiv.Perm ℕ) := by
    ext i
    by_cases h : i < m
    · have hb : (b : Equiv.Perm ℕ) i < m := b.lt h
      simp [Equiv.Perm.mul_apply, h, hb]
    · have hb : (b : Equiv.Perm ℕ) i = i := b.2 i (by omega)
      have h2 : ¬ ((c : Equiv.Perm ℕ) (i - m) + m < m) := by omega
      simp only [Equiv.Perm.mul_apply, shiftPerm_apply, h, if_false, hb]
      rw [b.2 _ (by omega)]
    -- done
  calc (a : Equiv.Perm ℕ) * (b : Equiv.Perm ℕ) *
          (shiftPerm m (c : Equiv.Perm ℕ) * shiftPerm m (d : Equiv.Perm ℕ))
      = (a : Equiv.Perm ℕ) * ((b : Equiv.Perm ℕ) * shiftPerm m (c : Equiv.Perm ℕ)) *
          shiftPerm m (d : Equiv.Perm ℕ) := by group
    _ = (a : Equiv.Perm ℕ) * (shiftPerm m (c : Equiv.Perm ℕ) * (b : Equiv.Perm ℕ)) *
          shiftPerm m (d : Equiv.Perm ℕ) := by rw [hcomm]
    _ = (a : Equiv.Perm ℕ) * shiftPerm m (c : Equiv.Perm ℕ) *
          ((b : Equiv.Perm ℕ) * shiftPerm m (d : Equiv.Perm ℕ)) := by group

@[simp] lemma PH.tens_one_one (m n : ℕ) : PH.tens (1 : PH m) (1 : PH n) = 1 := by
  apply PH.ext'; simp

lemma PH.tens_assoc {m n p : ℕ} (a : PH m) (b : PH n) (c : PH p) :
    (Nat.add_assoc m n p) ▸ (PH.tens (PH.tens a b) c) = PH.tens a (PH.tens b c) := by
  apply PH.ext'
  simp [shiftPerm_add, shiftPerm_mul, mul_assoc]

@[simp] lemma PH.tens_id_right {m : ℕ} (a : PH m) : PH.tens a (1 : PH 0) = a := by
  apply PH.ext'; simp

lemma PH.tens_id_left {m : ℕ} (a : PH m) :
    (Nat.zero_add m) ▸ (PH.tens (1 : PH 0) a) = a := by
  apply PH.ext'; simp

/-- Block swap: the symmetry `σ_{m,n}` of the permutation prop. -/
def swapPH (m n : ℕ) : PH (m + n) := by
  refine ⟨⟨fun i => if i < m then i + n else if i < m + n then i - m else i,
           fun i => if i < n then i + m else if i < m + n then i - n else i, ?_, ?_⟩, ?_⟩
  · intro i; dsimp only
    by_cases h : i < m
    · simp only [h, if_true]
      have h2 : ¬ (i + n < n) := by omega
      simp only [h2, if_false]
      have : i + n < m + n := by omega
      simp [this]
    · by_cases h3 : i < m + n
      · simp only [h, if_false, h3, if_true]
        have : i - m < n := by omega
        simp [this]; omega
      · simp [h, h3]; omega
  · intro i; dsimp only
    by_cases h : i < n
    · simp only [h, if_true]
      have h2 : ¬ (i + m < m) := by omega
      simp only [h2, if_false]
      have : i + m < m + n := by omega
      simp [this]
    · by_cases h3 : i < m + n
      · simp only [h, if_false, h3, if_true]
        have : i - n < m := by omega
        simp [this]; omega
      · simp [h, h3]; omega
  · intro i hi
    have h1 : ¬ (i < m) := by omega
    have h2 : ¬ (i < m + n) := by omega
    simp [h1, h2]

@[simp] lemma swapPH_apply (m n i : ℕ) :
    ((swapPH m n : PH (m + n)) : Equiv.Perm ℕ) i =
      if i < m then i + n else if i < m + n then i - m else i := rfl

lemma PH.tens_apply {m n : ℕ} (a : PH m) (b : PH n) (i : ℕ) :
    ((PH.tens a b : PH (m + n)) : Equiv.Perm ℕ) i =
      if i < m then (a : Equiv.Perm ℕ) i
      else if i < m + n then (b : Equiv.Perm ℕ) (i - m) + m else i := by
  simp only [PH.coe_tens, Equiv.Perm.mul_apply, shiftPerm_apply]
  by_cases h : i < m
  · simp [h]
  · by_cases h2 : i < m + n
    · have hb : (b : Equiv.Perm ℕ) (i - m) < n := b.lt (by omega)
      simp only [h, if_false, h2, if_true]
      exact a.2 _ (by omega)
    · have hb : (b : Equiv.Perm ℕ) (i - m) = i - m := b.2 _ (by omega)
      have e : i - m + m = i := by omega
      simp only [h, if_false, h2, hb, e]
      simp [h2, a.2 i (by omega)]

lemma shiftPerm_swap (m a b : ℕ) :
    shiftPerm m (Equiv.swap a b) = Equiv.swap (a + m) (b + m) := by
  ext i
  simp only [shiftPerm_apply, Equiv.swap_apply_def]
  split_ifs <;> omega

@[simp] lemma swapPH_symm_apply (m n i : ℕ) :
    ((swapPH m n : PH (m + n)) : Equiv.Perm ℕ).symm i =
      if i < n then i + m else if i < m + n then i - n else i := rfl

@[simp] lemma swapPH_zero_right (m : ℕ) : swapPH m 0 = 1 := by
  apply PH.ext'; ext i; simp; omega

@[simp] lemma swapPH_zero_left (n : ℕ) : swapPH 0 n = 1 := by
  apply PH.ext'; ext i; simp

lemma swapPH_nat {m n : ℕ} (a : PH m) (b : PH n) :
    swapPH m n * PH.tens a b = ((Nat.add_comm n m) ▸ PH.tens b a) * swapPH m n := by
  apply PH.ext'
  ext i
  have hA : (a : Equiv.Perm ℕ) (i + n - n) = (a : Equiv.Perm ℕ) i := by congr 1; omega
  have ha1 : i < m → (a : Equiv.Perm ℕ) i < m := fun h => a.lt h
  have ha2 : m ≤ i → (a : Equiv.Perm ℕ) i = i := fun h => a.2 i h
  have hb1 : i - m < n → (b : Equiv.Perm ℕ) (i - m) < n := fun h => b.lt h
  have hb2 : n ≤ i - m → (b : Equiv.Perm ℕ) (i - m) = i - m := fun h => b.2 _ h
  simp only [PH.coe_mul, PH.coe_cast, Equiv.Perm.mul_apply, swapPH_apply, PH.tens_apply, hA]
  split_ifs <;> omega

end Crops
