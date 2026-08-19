import ControlEquations.CropCore

/-!
# The sign of a wire permutation

The inclusion of the permutation prop into a signed graded-constant crop (`CtrlSigned`) factors
through the sign, so this file records the sign of a wire permutation together with the two
facts about it that the construction needs: it is multiplicative, and it is unchanged by padding
a permutation with unused wires on either side.
-/

set_option autoImplicit false

namespace Crops

/-! ### The inclusion of one wire count into a larger one -/

/-- The inclusion `PH k ↪ PH K` for `k ≤ K`: a permutation of the first `k` wires is one of
the first `K`. -/
def PH.emb {k K : ℕ} (h : k ≤ K) (a : PH k) : PH K :=
  ⟨(a : Equiv.Perm ℕ), fun i hi => a.2 i (by omega)⟩

@[simp] lemma PH.coe_emb {k K : ℕ} (h : k ≤ K) (a : PH k) :
    ((PH.emb h a : PH K) : Equiv.Perm ℕ) = (a : Equiv.Perm ℕ) := rfl

lemma PH.emb_mul {k K : ℕ} (h : k ≤ K) (a b : PH k) :
    PH.emb h (a * b) = PH.emb h a * PH.emb h b := rfl

lemma PH.tens_one_eq_emb {k j : ℕ} (a : PH k) :
    PH.tens a (1 : PH j) = PH.emb (by omega) a := by
  apply PH.ext'; simp

lemma PH.cast_tens_one {k j K : ℕ} (hk : k + j = K) (h : k ≤ K) (a : PH k) :
    (hk ▸ (PH.tens a (1 : PH j)) : PH K) = PH.emb h a := by
  apply PH.ext'
  rw [PH.coe_cast]
  simp

/-! ### The sign of a wire permutation -/

/-- The restriction of a wire permutation on `n` wires to `Fin n`. -/
def phFin {n : ℕ} (a : PH n) : Equiv.Perm (Fin n) where
  toFun i := ⟨(a : Equiv.Perm ℕ) i, PH.lt a i.2⟩
  invFun i := ⟨((a⁻¹ : PH n) : Equiv.Perm ℕ) i, PH.lt a⁻¹ i.2⟩
  left_inv := by
    intro i
    ext
    show ((a⁻¹ : PH n) : Equiv.Perm ℕ) ((a : Equiv.Perm ℕ) i) = i
    simp
  right_inv := by
    intro i
    ext
    show (a : Equiv.Perm ℕ) (((a⁻¹ : PH n) : Equiv.Perm ℕ) i) = i
    simp

@[simp] lemma phFin_apply {n : ℕ} (a : PH n) (i : Fin n) :
    ((phFin a i : Fin n) : ℕ) = (a : Equiv.Perm ℕ) i := rfl

lemma phFin_mul {n : ℕ} (a b : PH n) : phFin (a * b) = phFin a * phFin b := by
  ext i
  simp [Equiv.Perm.mul_apply]

/-- The sign of a wire permutation. -/
def phSign {n : ℕ} (a : PH n) : ℤˣ := Equiv.Perm.sign (phFin a)

@[simp] lemma phSign_one (n : ℕ) : phSign (1 : PH n) = 1 := by
  have h : phFin (1 : PH n) = 1 := by ext i; rfl
  rw [phSign, h, map_one]

lemma phSign_mul {n : ℕ} (a b : PH n) : phSign (a * b) = phSign a * phSign b := by
  rw [phSign, phFin_mul, map_mul, phSign, phSign]

lemma phSign_inv {n : ℕ} (a : PH n) : phSign a⁻¹ = (phSign a)⁻¹ := by
  have h := phSign_mul a a⁻¹
  rw [mul_inv_cancel, phSign_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma phSign_conj {N : ℕ} (u v : PH N) : phSign (u * v * u⁻¹) = phSign v := by
  rw [phSign_mul, phSign_mul, phSign_inv, mul_comm (phSign u) (phSign v), mul_assoc,
    mul_inv_cancel, mul_one]

/-! ### Sign is stable under adding wires -/

/-- The first `k` places of `Fin K` form a copy of `Fin k`. -/
def finRestrictLt (k K : ℕ) (h : k ≤ K) : {x : Fin K // ((x : ℕ) < k)} ≃ Fin k where
  toFun x := ⟨(x.1 : ℕ), x.2⟩
  invFun i := ⟨⟨(i : ℕ), by omega⟩, i.2⟩
  left_inv := by intro x; ext; rfl
  right_inv := by intro i; ext; rfl

/-- The last `k` places of `Fin (m+k)` form a copy of `Fin k`. -/
def finRestrictGe (m k : ℕ) : {x : Fin (m + k) // m ≤ ((x : ℕ))} ≃ Fin k where
  toFun x := ⟨(x.1 : ℕ) - m, by have h3 := x.1.2; have h4 := x.2; omega⟩
  invFun i := ⟨⟨(i : ℕ) + m, by have h3 := i.2; omega⟩, by simp⟩
  left_inv := by
    intro x
    have h4 := x.2
    ext
    show (x.1 : ℕ) - m + m = (x.1 : ℕ)
    omega
  right_inv := by
    intro i
    ext
    show (i : ℕ) + m - m = (i : ℕ)
    omega

/-- Adding unused wires **at the end** does not change the sign. -/
lemma phSign_emb {k K : ℕ} (h : k ≤ K) (a : PH k) : phSign (PH.emb h a) = phSign a := by
  classical
  have hfix : ∀ x : Fin K, ¬ ((x : ℕ) < k) →
      (a : Equiv.Perm ℕ) (x : ℕ) = (x : ℕ) := fun x hx => PH.fix a (by omega)
  have hlt : ∀ x : Fin K, ((x : ℕ) < k) → (a : Equiv.Perm ℕ) (x : ℕ) < k :=
    fun x hx => PH.lt a hx
  have h₁ : ∀ x : Fin K, ((phFin (PH.emb h a) x : Fin K) : ℕ) < k ↔ ((x : ℕ) < k) := by
    intro x
    show ((a : Equiv.Perm ℕ) (x : ℕ) < k) ↔ _
    refine ⟨fun hx => ?_, hlt x⟩
    by_contra hc
    rw [hfix x hc] at hx
    exact hc hx
  have h₂ : ∀ x : Fin K, phFin (PH.emb h a) x ≠ x → ((x : ℕ) < k) := by
    intro x hx
    by_contra hc
    exact hx (Fin.ext (hfix x hc))
  have e1 := Equiv.Perm.sign_subtypePerm (p := fun x : Fin K => ((x : ℕ) < k))
    (phFin (PH.emb h a)) (fun x => h₁ x) h₂
  have e2 : Equiv.Perm.sign (Equiv.Perm.subtypePerm (p := fun x : Fin K => ((x : ℕ) < k))
        (phFin (PH.emb h a)) (fun x => h₁ x))
      = Equiv.Perm.sign (phFin a) := by
    refine Equiv.Perm.sign_eq_sign_of_equiv _ _ (finRestrictLt k K h) ?_
    intro x
    ext
    rfl
  rw [phSign, ← e1, e2, phSign]

/-- Wire permutations with the same underlying permutation of `ℕ` have the same sign, whatever
their arities. -/
lemma phSign_eq_of_coe {k K : ℕ} (a : PH k) (b : PH K)
    (hab : (a : Equiv.Perm ℕ) = (b : Equiv.Perm ℕ)) : phSign a = phSign b := by
  rcases le_total k K with h | h
  · have : b = PH.emb h a := PH.ext' hab.symm
    rw [this, phSign_emb]
  · have : a = PH.emb h b := PH.ext' hab
    rw [this, phSign_emb]

/-- Shift a wire permutation up by `m` unused wires. -/
def shiftPH (m : ℕ) {k : ℕ} (a : PH k) : PH (m + k) :=
  ⟨shiftPerm m (a : Equiv.Perm ℕ), by
    intro i hi
    have h1 : ¬ (i < m) := by omega
    have h2 : (a : Equiv.Perm ℕ) (i - m) = i - m := PH.fix a (by omega)
    simp only [shiftPerm_apply, h1, if_false, h2]
    omega⟩

@[simp] lemma shiftPH_coe (m : ℕ) {k : ℕ} (a : PH k) :
    ((shiftPH m a : PH (m + k)) : Equiv.Perm ℕ) = shiftPerm m (a : Equiv.Perm ℕ) := rfl

/-- Adding unused wires **at the front** does not change the sign. -/
lemma phSign_shiftPH (m : ℕ) {k : ℕ} (a : PH k) : phSign (shiftPH m a) = phSign a := by
  classical
  set b : PH (m + k) := shiftPH m a with hbdef
  have hsmall : ∀ x : Fin (m + k), (x : ℕ) < m → (b : Equiv.Perm ℕ) (x : ℕ) = (x : ℕ) := by
    intro x hx
    simp [hbdef, hx]
  have hbig : ∀ x : Fin (m + k), m ≤ (x : ℕ) →
      (b : Equiv.Perm ℕ) (x : ℕ) = (a : Equiv.Perm ℕ) ((x : ℕ) - m) + m := by
    intro x hx
    simp only [hbdef, shiftPH_coe, shiftPerm_apply, if_neg (by omega : ¬ ((x : ℕ) < m))]
  have h₁ : ∀ x : Fin (m + k), m ≤ ((phFin b x : Fin (m + k)) : ℕ) ↔ m ≤ ((x : ℕ)) := by
    intro x
    show m ≤ (b : Equiv.Perm ℕ) (x : ℕ) ↔ _
    rcases Nat.lt_or_ge (x : ℕ) m with hx | hx
    · rw [hsmall x hx]
    · rw [hbig x hx]; omega
  have h₂ : ∀ x : Fin (m + k), phFin b x ≠ x → m ≤ (x : ℕ) := by
    intro x hx
    by_contra hc
    exact hx (Fin.ext (hsmall x (by omega)))
  have e1 := Equiv.Perm.sign_subtypePerm (p := fun x : Fin (m + k) => m ≤ ((x : ℕ)))
    (phFin b) (fun x => h₁ x) h₂
  have e2 : Equiv.Perm.sign (Equiv.Perm.subtypePerm (p := fun x : Fin (m + k) => m ≤ ((x : ℕ)))
      (phFin b) (fun x => h₁ x)) = Equiv.Perm.sign (phFin a) := by
    refine Equiv.Perm.sign_eq_sign_of_equiv _ _ (finRestrictGe m k) ?_
    intro x
    ext
    show (b : Equiv.Perm ℕ) (x.1 : ℕ) - m = (a : Equiv.Perm ℕ) ((x.1 : ℕ) - m)
    rw [hbig x.1 x.2]
    omega
  rw [phSign, ← e1, e2, phSign]

end Crops
