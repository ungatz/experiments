import ControlEquations.CtrlSigned

/-!
# A crop with a nontrivial symmetry and a nontrivial scalar

The crop used in `ControlEquations.CtrlSepH` to separate their equation (h) from the other
seven.

Its shape is forced by `invol_tens_trivial_of_symmetric` together with `eqH_of_trivial_symmetry`:
a witness for (h) needs a symmetry that is not the identity, and a place where the two control
wires can be told apart.  Here that place is the hom-monoid `S₃` in positive arity, and what
feeds it is a scalar: the arity-zero hom-monoid is `ℤ/2` and its control is a transposition.

    H 0 = Bool, that is ℤ/2 under xor,     H n = S₃ for n ≥ 1,

with composition the group operation, and a monoidal product that discards everything except a
degree-zero factor:

    a + b = a * b  (both in degree 0),     a + b = b  (degree of a is 0),
    a + b = a      (degree of b is 0),     a + b = id (both degrees positive).

The permutation prop is included through the sign in degrees at most two and trivially above.
That truncation is forced, because in degrees three and up every morphism in the image of the
monoidal product is an identity, so a nontrivial inclusion there would break monoidality of
`io`.

Padding is therefore not injective, and the morphisms that padding kills are exactly what makes
(h) fail while (c), every instance of which compares padded morphisms, holds.
-/

set_option autoImplicit false

namespace Crops

namespace Sm

open Ctrl Ctrl.SignedData

/-- The group `S₃`, used in every positive degree. -/
abbrev P3 := Equiv.Perm (Fin 3)

/-- The value type: a scalar bit and a permutation of three letters.  Only one of the two
components is visible in each degree. -/
abbrev SV := Bool × P3

/-- Multiplication of values. -/
def vmul (u v : SV) : SV := (xor u.1 v.1, u.2 * v.2)

/-- The unit value. -/
def vone : SV := (false, 1)

@[simp] lemma vmul_vone (u : SV) : vmul u vone = u := by
  cases u; simp [vmul, vone]

@[simp] lemma vone_vmul (u : SV) : vmul vone u = u := by
  cases u; simp [vmul, vone]

lemma vmul_assoc (u v w : SV) : vmul (vmul u v) w = vmul u (vmul v w) := by
  simp [vmul, mul_assoc]

/-- The hom-types: `ℤ/2` in degree `0`, `S₃` in every positive degree. -/
def SH : ℕ → Type
  | 0 => Bool
  | _ + 1 => P3

/-- The value of a morphism. -/
def sElim : (N : ℕ) → SH N → SV
  | 0, a => (a, 1)
  | _ + 1, a => (false, a)

/-- The morphism with a given value. -/
def sMk : (N : ℕ) → SV → SH N
  | 0, u => u.1
  | _ + 1, u => u.2

/-- The part of a value visible in degree `N`. -/
def sProj (N : ℕ) (u : SV) : SV := if N = 0 then (u.1, 1) else (false, u.2)

@[simp] lemma sProj_zero (u : SV) : sProj 0 u = (u.1, 1) := if_pos rfl

lemma sProj_pos {N : ℕ} (h : N ≠ 0) (u : SV) : sProj N u = (false, u.2) := if_neg h

lemma sMk_sElim : ∀ (N : ℕ) (a : SH N), sMk N (sElim N a) = a
  | 0, _ => rfl
  | _ + 1, _ => rfl

lemma sElim_sMk : ∀ (N : ℕ) (u : SV), sElim N (sMk N u) = sProj N u
  | 0, _ => rfl
  | k + 1, u => by rw [sProj_pos (Nat.succ_ne_zero k)]; rfl

/-- Morphisms are determined by their value. -/
lemma s_ext {N : ℕ} {a b : SH N} (h : sElim N a = sElim N b) : a = b := by
  rw [← sMk_sElim N a, h, sMk_sElim]

lemma sProj_sElim : ∀ (N : ℕ) (a : SH N), sProj N (sElim N a) = sElim N a
  | 0, _ => rfl
  | k + 1, a => by rw [sProj_pos (Nat.succ_ne_zero k)]; rfl

@[simp] lemma sProj_vone (N : ℕ) : sProj N vone = vone := by
  by_cases h : N = 0 <;> simp [sProj, h, vone]

lemma sProj_vmul (N : ℕ) (u v : SV) : sProj N (vmul u v) = vmul (sProj N u) (sProj N v) := by
  by_cases h : N = 0 <;> simp [sProj, h, vmul]

@[simp] lemma sProj_sProj (N : ℕ) (u : SV) : sProj N (sProj N u) = sProj N u := by
  by_cases h : N = 0 <;> simp [sProj, h]

lemma sProj_eq_of_pos {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (u : SV) : sProj M u = sProj N u := by
  rw [sProj_pos hM, sProj_pos hN]

lemma sElim_zero (a : SH 0) : sElim 0 a = (a, 1) := rfl

lemma pair_sElim {N : ℕ} (h : N ≠ 0) (a : SH N) : ((false, (sElim N a).2) : SV) = sElim N a := by
  conv_rhs => rw [← sProj_sElim N a, sProj_pos h]

lemma sElim_cst {M N : ℕ} (h : M = N) (a : SH M) : sElim N (h ▸ a) = sElim M a := by
  cases h; rfl

/-- There is only one wire permutation on one wire. -/
lemma ph_one_eq_one (p : PH 1) : p = 1 := by
  apply PH.ext'
  ext i
  rcases Nat.lt_or_ge i 1 with hi | hi
  · have h0 : i = 0 := by omega
    have := PH.lt p (show i < 1 by omega)
    subst h0
    show (p : Equiv.Perm ℕ) 0 = 0
    omega
  · exact p.2 i hi

/-! ### The structure maps -/

/-- Composition. -/
def sCmp {N : ℕ} (a b : SH N) : SH N := sMk N (vmul (sElim N a) (sElim N b))

/-- Identity. -/
def sIdm (N : ℕ) : SH N := sMk N vone

/-- The monoidal product, on values: everything is discarded unless one side has degree `0`. -/
def vTn (m n : ℕ) (u v : SV) : SV :=
  if m = 0 then (if n = 0 then vmul u v else v) else (if n = 0 then u else vone)

lemma vTn_zz (u v : SV) : vTn 0 0 u v = vmul u v := rfl

lemma vTn_zp {n : ℕ} (hn : n ≠ 0) (u v : SV) : vTn 0 n u v = v := by simp [vTn, hn]

lemma vTn_pz {m : ℕ} (hm : m ≠ 0) (u v : SV) : vTn m 0 u v = u := by simp [vTn, hm]

lemma vTn_pp {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (u v : SV) : vTn m n u v = vone := by
  simp [vTn, hm, hn]

/-- The monoidal product. -/
def sTn {m n : ℕ} (a : SH m) (b : SH n) : SH (m + n) :=
  sMk (m + n) (vTn m n (sElim m a) (sElim n b))

/-- The image of a unit of `ℤˣ` in `S₃`. -/
def sgnP (u : ℤˣ) : P3 := if u = 1 then 1 else Equiv.swap 0 1

@[simp] lemma sgnP_one : sgnP 1 = 1 := by simp [sgnP]

lemma sgnP_mul (u v : ℤˣ) : sgnP (u * v) = sgnP u * sgnP v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp [sgnP, Equiv.swap_mul_self]

/-- The value of the included permutation: the sign in degrees `≤ 2`, trivial above. -/
def vIo (N : ℕ) (p : PH N) : SV := if N ≤ 2 then (false, sgnP (phSign p)) else vone

/-- The inclusion of the permutation prop. -/
def sIo {N : ℕ} (p : PH N) : SH N := sMk N (vIo N p)

lemma vIo_one (N : ℕ) : vIo N (1 : PH N) = vone := by
  by_cases h : N ≤ 2 <;> simp [vIo, h, vone]

lemma vIo_mul {N : ℕ} (p q : PH N) : vIo N (p * q) = vmul (vIo N p) (vIo N q) := by
  by_cases h : N ≤ 2
  · simp [vIo, h, vmul, phSign_mul, sgnP_mul]
  · simp [vIo, h, vone, vmul]

@[simp] lemma sElim_sCmp {N : ℕ} (a b : SH N) :
    sElim N (sCmp a b) = vmul (sElim N a) (sElim N b) := by
  rw [sCmp, sElim_sMk, sProj_vmul, sProj_sElim, sProj_sElim]

@[simp] lemma sElim_sIdm (N : ℕ) : sElim N (sIdm N) = vone := by
  rw [sIdm, sElim_sMk, sProj_vone]

lemma sElim_sTn {m n : ℕ} (a : SH m) (b : SH n) :
    sElim (m + n) (sTn a b) = sProj (m + n) (vTn m n (sElim m a) (sElim n b)) := by
  rw [sTn, sElim_sMk]

lemma sElim_sIo {N : ℕ} (p : PH N) : sElim N (sIo p) = sProj N (vIo N p) := by
  rw [sIo, sElim_sMk]

/-! #### The four cases of the monoidal product -/

lemma sTn_zz (a b : SH 0) : sElim (0 + 0) (sTn a b) = vmul (sElim 0 a) (sElim 0 b) := by
  rw [sElim_sTn, vTn_zz]
  rw [sElim_zero, sElim_zero]
  simp [vmul, sProj]

lemma sTn_zp {n : ℕ} (hn : n ≠ 0) (a : SH 0) (b : SH n) :
    sElim (0 + n) (sTn a b) = sElim n b := by
  rw [sElim_sTn, vTn_zp hn, sProj_eq_of_pos (by omega) hn, sProj_sElim]

lemma sTn_pz {m : ℕ} (hm : m ≠ 0) (a : SH m) (b : SH 0) :
    sElim (m + 0) (sTn a b) = sElim m a := by
  rw [sElim_sTn, vTn_pz hm, sProj_eq_of_pos (by omega) hm, sProj_sElim]

lemma sTn_pp {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (a : SH m) (b : SH n) :
    sElim (m + n) (sTn a b) = vone := by
  rw [sElim_sTn, vTn_pp hm hn, sProj_vone]

/-! ### The endo-prop -/

/-- The small endo-prop. -/
def SmProp : EndoProp where
  H := SH
  cmp := sCmp
  idm := sIdm
  tn := sTn
  io := sIo
  cmp_assoc a b c := s_ext (by simp [vmul_assoc])
  idm_cmp a := s_ext (by simp)
  cmp_idm a := s_ext (by simp)
  tn_cmp {m n} a b c d := by
    refine s_ext ?_
    simp only [sElim_sTn, sElim_sCmp]
    rcases eq_or_ne m 0 with rfl | hm <;> rcases eq_or_ne n 0 with rfl | hn <;>
      simp [sProj, vTn, vmul, vone, sElim_zero, Bool.xor_left_comm, *]
  tn_idm m n := by
    refine s_ext ?_
    simp only [sElim_sTn, sElim_sIdm]
    rcases eq_or_ne m 0 with rfl | hm <;> rcases eq_or_ne n 0 with rfl | hn <;>
      simp [sProj, vTn, vmul, vone, *]
  tn_assoc {m n p} a b c := by
    refine s_ext ?_
    simp only [sElim_cst, sElim_sTn]
    rcases eq_or_ne m 0 with rfl | hm <;> rcases eq_or_ne n 0 with rfl | hn <;>
      rcases eq_or_ne p 0 with rfl | hp <;>
      simp [sProj, vTn, vmul, vone, sElim_zero, *]
  tn_idm_right {m} a := by
    refine s_ext ?_
    simp only [sElim_sTn, sElim_sIdm]
    rcases eq_or_ne m 0 with rfl | hm
    · simp [sProj, vTn, vmul, vone, sElim_zero]
    · simp [sProj, vTn, hm, pair_sElim hm]
  tn_idm_left {m} a := by
    refine s_ext ?_
    simp only [sElim_cst, sElim_sTn, sElim_sIdm]
    rcases eq_or_ne m 0 with rfl | hm
    · simp [sProj, vTn, vmul, vone, sElim_zero]
    · simp [sProj, vTn, hm, pair_sElim hm]
  io_cmp p q := by
    refine s_ext ?_
    rw [sElim_sIo, sElim_sCmp, sElim_sIo, sElim_sIo, ← sProj_vmul, vIo_mul]
  io_one N := by
    refine s_ext ?_
    rw [sElim_sIo, sElim_sIdm, vIo_one, sProj_vone]
  io_tn {m n} p q := by
    refine s_ext ?_
    rw [sElim_sIo, sElim_sTn, sElim_sIo, sElim_sIo]
    rcases eq_or_ne m 0 with rfl | hm <;> rcases eq_or_ne n 0 with rfl | hn
    · rw [vTn_zz]
      simp [vIo, vmul, sProj, phSign_zero]
    · rw [vTn_zp hn]
      have hz : phSign p = 1 := phSign_zero p
      by_cases h2 : n ≤ 2
      · have h2' : 0 + n ≤ 2 := by omega
        simp only [vIo, if_pos h2, if_pos h2', phSign_tens, hz, one_mul]
        rw [sProj_pos hn]
      · have h2' : ¬ (0 + n ≤ 2) := by omega
        simp only [vIo, if_neg h2, if_neg h2', sProj_vone]
    · rw [vTn_pz hm]
      have hz : phSign q = 1 := phSign_zero q
      by_cases h2 : m ≤ 2
      · have h2' : m + 0 ≤ 2 := by omega
        simp only [vIo, if_pos h2, if_pos h2', phSign_tens, hz, mul_one]
        rw [sProj_pos hm]
      · have h2' : ¬ (m + 0 ≤ 2) := by omega
        simp only [vIo, if_neg h2, if_neg h2', sProj_vone]
    · rw [vTn_pp hm hn, sProj_vone]
      rcases Nat.lt_or_ge (m + n) 3 with h3 | h3
      · obtain rfl : m = 1 := by omega
        obtain rfl : n = 1 := by omega
        rw [ph_one_eq_one p, ph_one_eq_one q,
          show PH.tens (1 : PH 1) (1 : PH 1) = 1 from PH.ext' (by simp [PH.tens]),
          vIo_one, sProj_vone]
      · have h2' : ¬ ((m + n) ≤ 2) := by omega
        simp only [vIo, if_neg h2', sProj_vone]
  io_swap_nat {m n} a b := by
    refine s_ext ?_
    rw [sElim_sCmp, sElim_sCmp, sElim_sIo, sElim_cst]
    simp only [sElim_sTn]
    rcases eq_or_ne m 0 with rfl | hm <;> rcases eq_or_ne n 0 with rfl | hn
    · rw [swapPH_zero_left, vIo_one]
      simp [sProj, vTn, vmul, vone, sElim_zero, Bool.xor_comm]
    · rw [swapPH_zero_left, vIo_one]
      simp [sProj, vTn, vmul, vone, hn]
    · rw [swapPH_zero_right, vIo_one]
      simp [sProj, vTn, vmul, vone, hm]
    · simp [sProj, vTn, vmul, vone, hm, hn]


@[simp] lemma SmProp_cmp {N : ℕ} (a b : SH N) : SmProp.cmp a b = sCmp a b := rfl

@[simp] lemma SmProp_idm (N : ℕ) : SmProp.idm N = sIdm N := rfl

@[simp] lemma SmProp_tn {m n : ℕ} (a : SH m) (b : SH n) : SmProp.tn a b = sTn a b := rfl

@[simp] lemma SmProp_io {N : ℕ} (p : PH N) : SmProp.io p = sIo p := rfl

/-- The distinguished involution: the transposition `(0 1)` of `S₃`, in degree one. -/
def sX : SH 1 := Equiv.swap 0 1

/-- The small crop. -/
def SmCrop : Crop where
  toEndoProp := SmProp
  invol := sX
  invol_invol := by
    show sCmp sX sX = sIdm 1
    refine s_ext ?_
    rw [sElim_sCmp, sElim_sIdm]
    show vmul (false, Equiv.swap (0 : Fin 3) 1) (false, Equiv.swap (0 : Fin 3) 1) = vone
    simp [vmul, vone, Equiv.swap_mul_self]

@[simp] lemma SmCrop_H (N : ℕ) : SmCrop.H N = SH N := rfl

@[simp] lemma SmCrop_cmp {N : ℕ} (a b : SH N) : SmCrop.cmp a b = sCmp a b := rfl

@[simp] lemma SmCrop_idm (N : ℕ) : SmCrop.idm N = sIdm N := rfl

@[simp] lemma SmCrop_tn {m n : ℕ} (a : SH m) (b : SH n) : SmCrop.tn a b = sTn a b := rfl

@[simp] lemma SmCrop_io {N : ℕ} (p : PH N) : SmCrop.io p = sIo p := rfl

@[simp] lemma SmCrop_invol : SmCrop.invol = sX := rfl


/-! ### The second-component calculus

Every hom-set of positive degree is `S₃`, and a morphism there is determined by the second
component of its value.  These lemmas compute that component through each structure map, and are
what the verification of the control equations runs on.
-/

lemma s_ext2 {N : ℕ} (h : N ≠ 0) {a b : SH N} (hh : (sElim N a).2 = (sElim N b).2) : a = b := by
  refine s_ext ?_
  rw [← sProj_sElim N a, ← sProj_sElim N b, sProj_pos h, sProj_pos h, hh]

@[simp] lemma snd_sCmp {N : ℕ} (a b : SH N) :
    (sElim N (sCmp a b)).2 = (sElim N a).2 * (sElim N b).2 := by
  rw [sElim_sCmp]; rfl

@[simp] lemma snd_sIdm (N : ℕ) : (sElim N (sIdm N)).2 = 1 := by
  rw [sElim_sIdm]; rfl

lemma snd_sTn_zz (a b : SH 0) : (sElim (0 + 0) (sTn a b)).2 = 1 := by
  rw [sTn_zz]; rfl

lemma snd_sTn_zp {n : ℕ} (hn : n ≠ 0) (a : SH 0) (b : SH n) :
    (sElim (0 + n) (sTn a b)).2 = (sElim n b).2 := by
  rw [sTn_zp hn]

lemma snd_sTn_pz {m : ℕ} (hm : m ≠ 0) (a : SH m) (b : SH 0) :
    (sElim (m + 0) (sTn a b)).2 = (sElim m a).2 := by
  rw [sTn_pz hm]

lemma snd_sTn_pp {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (a : SH m) (b : SH n) :
    (sElim (m + n) (sTn a b)).2 = 1 := by
  rw [sTn_pp hm hn]; rfl

lemma snd_cst {M N : ℕ} (h : M = N) (a : SH M) :
    (sElim N (SmCrop.cst h a)).2 = (sElim M a).2 := by
  rw [show SmCrop.cst h a = h ▸ a from rfl, sElim_cst]

lemma snd_sIo {N : ℕ} (hN : N ≠ 0) (h2 : N ≤ 2) (p : PH N) :
    (sElim N (sIo p)).2 = sgnP (phSign p) := by
  rw [sElim_sIo, sProj_pos hN, vIo, if_pos h2]

end Sm

end Crops
