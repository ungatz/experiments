import ControlEquations.CropSmall
import ControlEquations.CtrlDefs

/-!
# A model of seven of the eight control equations, failing (h)

A crop with control data satisfying their (a), (b), (c), (d), (e), (f) and (g), for which their
(h) fails.  So (h) is not derivable from the other seven.

The crop is `SmCrop` of `ControlEquations.CropSmall`.  The control data is

* `C1` in degree `0`: the scalar bit `a : ℤ/2` goes to `x = (0 1) ∈ S₃`, so control sees the
  scalar;
* `C1` in positive degree: `g : S₃` goes to `1` or to `(1 2) ∈ S₃` according to the sign of `g`;
* `C0` is the `x`-conjugate of `C1`, which makes their (d) hold by construction.

Their (h) fails at arity `0`: `C1 (C1 1) = (1 2)` while the symmetry `σ₁,₁` is `(0 1)`, and these
two transpositions of `S₃` do not commute.  Every other equation survives because the monoidal
product of the crop discards all positive-degree information, so every padded morphism is an
identity, which is exactly why their (c), whose every instance compares padded morphisms, holds
here while (h) does not.

Every hom-monoid of `SmCrop` is a group, so the crop is reversible and (h) is independent inside
the reversible class as well.
-/

set_option autoImplicit false

namespace Crops

namespace Sm

open Ctrl

/-- The transposition `(0 1)` of `S₃`: the distinguished involution and the image of the
symmetry. -/
def wP : P3 := Equiv.swap 0 1

/-- The transposition `(1 2)` of `S₃`: the value of the doubly-controlled involution. -/
def vP : P3 := Equiv.swap 1 2

/-- Control in degree zero: the scalar bit goes to `wP`. -/
def bv (a : Bool) : P3 := if a then wP else 1

/-- Control in positive degree: the sign goes to `vP`. -/
def cv (g : P3) : P3 := if Equiv.Perm.sign g = 1 then 1 else vP

@[simp] lemma bv_false : bv false = 1 := rfl

@[simp] lemma cv_one : cv 1 = 1 := by simp [cv]

lemma bv_xor (a b : Bool) : bv (xor a b) = bv a * bv b := by
  cases a <;> cases b <;> simp [bv, wP]

lemma cv_mul (g h : P3) : cv (g * h) = cv g * cv h := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh <;>
    simp [cv, map_mul, hg, hh, vP]

lemma bv_sq (a : Bool) : bv a * bv a = 1 := by cases a <;> simp [bv, wP]

lemma cv_sq (g : P3) : cv g * cv g = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg <;> simp [cv, hg, vP]

/-- The two values of `bv` commute with each other and with `wP`. -/
lemma bv_comm_wP (a : Bool) : wP * bv a = bv a * wP := by cases a <;> simp [bv]

lemma bv_comm (a b : Bool) : bv a * bv b = bv b * bv a := by
  cases a <;> cases b <;> simp [bv]

lemma cv_comm (g h : P3) : cv g * cv h = cv h * cv g := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh <;> simp [cv, hg, hh]

lemma cv_wP : cv wP = vP := by
  have : Equiv.Perm.sign wP = -1 := by decide
  simp [cv, this]

/-! ### The control data -/

/-- The `S₃`-component of `C1` in degree `n`. -/
def c1v (n : ℕ) (u : SV) : P3 := if n = 0 then bv u.1 else cv u.2

/-- The `S₃`-component of the distinguished involution padded with `n` wires. -/
def xv (n : ℕ) : P3 := if n = 0 then wP else 1

lemma c1v_pos {n : ℕ} (hn : n ≠ 0) (u : SV) : c1v n u = cv u.2 := if_neg hn

lemma c1v_one (n : ℕ) : c1v n vone = 1 := by
  by_cases h : n = 0 <;> simp [c1v, h, vone]

lemma c1v_mul (n : ℕ) (u v : SV) : c1v n (vmul u v) = c1v n u * c1v n v := by
  by_cases h : n = 0 <;> simp [c1v, h, vmul, bv_xor, cv_mul]

lemma c1v_sq (n : ℕ) (u : SV) : c1v n u * c1v n u = 1 := by
  by_cases h : n = 0 <;> simp [c1v, h, bv_sq, cv_sq]

lemma c1v_comm (n : ℕ) (u v : SV) : c1v n u * c1v n v = c1v n v * c1v n u := by
  by_cases h : n = 0 <;> simp [c1v, h, bv_comm, cv_comm]

lemma xv_comm (n : ℕ) (u : SV) : xv n * c1v n u = c1v n u * xv n := by
  by_cases h : n = 0
  · subst h; simpa [xv, c1v] using bv_comm_wP u.1
  · simp [xv, c1v, h]

lemma xv_sq (n : ℕ) : xv n * xv n = 1 := by
  by_cases h : n = 0 <;> simp [xv, h, wP]

/-- `C1`, as a map on morphisms. -/
def smC1 (n : ℕ) (a : SH n) : SH (1 + n) := sMk (1 + n) (false, c1v n (sElim n a))

/-- `C0`, as a map on morphisms: the `x`-conjugate of `C1`, which makes (d) hold by
construction. -/
def smC0 (n : ℕ) (a : SH n) : SH (1 + n) :=
  sMk (1 + n) (false, xv n * c1v n (sElim n a) * xv n)

lemma snd_smC1 (n : ℕ) (a : SH n) :
    (sElim (1 + n) (smC1 n a)).2 = c1v n (sElim n a) := by
  rw [smC1, sElim_sMk, sProj_pos (by omega)]

lemma snd_smC0 (n : ℕ) (a : SH n) :
    (sElim (1 + n) (smC0 n a)).2 = xv n * c1v n (sElim n a) * xv n := by
  rw [smC0, sElim_sMk, sProj_pos (by omega)]

/-- The control data on the small crop. -/
def smData : Ctrl.Data SmCrop where
  C0 := smC0
  C1 := smC1

@[simp] lemma smData_C0 (n : ℕ) (a : SH n) : smData.C0 n a = smC0 n a := rfl

@[simp] lemma smData_C1 (n : ℕ) (a : SH n) : smData.C1 n a = smC1 n a := rfl

/-! ### The value of the padded involution and of the symmetry -/

@[simp] lemma sElim_sX : sElim 1 sX = (false, wP) := rfl

lemma snd_xw (n : ℕ) : (sElim (1 + n) (xw (P := SmCrop) n)).2 = xv n := by
  show (sElim (1 + n) (sTn sX (sIdm n))).2 = xv n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [snd_sTn_pz (by omega), sElim_sX, xv]
    simp
  · rw [snd_sTn_pp (by omega) hn, xv, if_neg hn]

lemma snd_sw : (sElim 2 (sw (P := SmCrop))).2 = wP := by
  show (sElim 2 (sIo (swapPH 1 1))).2 = wP
  rw [snd_sIo (by omega) (by omega), Ctrl.SignedData.phSign_swap11]
  simp [sgnP, wP]

lemma snd_sww_zero : (sElim 2 (sww (P := SmCrop) 0)).2 = wP := by
  rw [sww]
  simp only [SmCrop_tn, SmCrop_idm]
  rw [snd_cst, snd_sTn_pz (by omega), snd_sw]

/-! ### The seven equations that hold -/

theorem smData_EqA : smData.EqA := by
  intro n f g
  refine s_ext2 (by omega) ?_
  show (sElim (1 + n) (smC1 n (sCmp g f))).2
      = (sElim (1 + n) (sCmp (smC1 n g) (smC1 n f))).2
  rw [snd_smC1, snd_sCmp, snd_smC1, snd_smC1, sElim_sCmp, c1v_mul]

theorem smData_EqB : smData.EqB := by
  intro n
  refine s_ext2 (by omega) ?_
  show (sElim (1 + n) (smC1 n (sIdm n))).2 = (sElim (1 + n) (sIdm (1 + n))).2
  rw [snd_smC1, snd_sIdm, sElim_sIdm, c1v_one]

theorem smData_EqC : smData.EqC := by
  intro n m f
  refine s_ext2 (by omega) ?_
  show (sElim (1 + (n + m)) (smC1 (n + m) (sTn f (sIdm m)))).2
      = (sElim (1 + (n + m)) (SmCrop.cst (by omega) (sTn (smC1 n f) (sIdm m)))).2
  rw [snd_smC1, snd_cst]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [snd_sTn_pz (by omega), snd_smC1,
      show sTn f (sIdm 0) = f from SmProp.tn_idm_right f]
    rfl
  · rw [snd_sTn_pp (by omega) hm, c1v_pos (by omega)]
    have h1 : (sElim (n + m) (sTn f (sIdm m))).2 = 1 := by
      rcases eq_or_ne n 0 with rfl | hn
      · rw [snd_sTn_zp hm, snd_sIdm]
      · rw [snd_sTn_pp hn hm]
    rw [h1, cv_one]

theorem smData_EqD : smData.EqD := by
  intro n f
  refine s_ext2 (by omega) ?_
  show (sElim (1 + n) (sCmp (xw (P := SmCrop) n)
      (sCmp (smC0 n f) (xw (P := SmCrop) n)))).2 = (sElim (1 + n) (smC1 n f)).2
  rw [snd_sCmp, snd_sCmp, snd_xw, snd_smC0, snd_smC1]
  calc xv n * (xv n * c1v n (sElim n f) * xv n * xv n)
      = (xv n * xv n) * c1v n (sElim n f) * (xv n * xv n) := by group
    _ = c1v n (sElim n f) := by rw [xv_sq, one_mul, mul_one]

theorem smData_EqE : smData.EqE := by
  intro n f
  refine s_ext2 (by omega) ?_
  show (sElim (1 + n) (sCmp (smC0 n f) (smC1 n f))).2 = (sElim (1 + n) (sTn (sIdm 1) f)).2
  rw [snd_sCmp, snd_smC0, snd_smC1]
  have key : xv n * c1v n (sElim n f) * xv n * c1v n (sElim n f) = 1 := by
    calc xv n * c1v n (sElim n f) * xv n * c1v n (sElim n f)
        = xv n * (c1v n (sElim n f) * xv n) * c1v n (sElim n f) := by group
      _ = xv n * (xv n * c1v n (sElim n f)) * c1v n (sElim n f) := by
            rw [xv_comm n (sElim n f)]
      _ = (xv n * xv n) * (c1v n (sElim n f) * c1v n (sElim n f)) := by group
      _ = 1 := by rw [xv_sq, c1v_sq, one_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [snd_sTn_pz (by omega), snd_sIdm, key]
  · rw [snd_sTn_pp (by omega) hn, key]

theorem smData_EqF : smData.EqF := by
  intro n f₁ f₂
  refine s_ext2 (by omega) ?_
  show (sElim (1 + n) (sCmp (smC0 n f₁) (smC1 n f₂))).2
      = (sElim (1 + n) (sCmp (smC1 n f₂) (smC0 n f₁))).2
  rw [snd_sCmp, snd_sCmp, snd_smC0, snd_smC1]
  have cAC : Commute (xv n) (c1v n (sElim n f₂)) := xv_comm n _
  have cBC : Commute (c1v n (sElim n f₁)) (c1v n (sElim n f₂)) := c1v_comm n _ _
  exact (cAC.mul_left cBC).mul_left cAC

theorem smData_EqG : smData.EqG := by
  refine s_ext2 (N := 2) (by omega) ?_
  show (sElim 2 (sCmp (smC1 1 sX) (sCmp (sw (P := SmCrop))
      (sCmp (smC1 1 sX) (sCmp (sw (P := SmCrop)) (smC1 1 sX)))))).2
      = (sElim 2 (sw (P := SmCrop))).2
  have hC : (sElim 2 (smC1 1 sX)).2 = vP := by
    show (sElim (1 + 1) (smC1 1 sX)).2 = vP
    rw [snd_smC1, sElim_sX, c1v_pos (n := 1) (by omega), cv_wP]
  rw [snd_sCmp, snd_sCmp, snd_sCmp, snd_sCmp, hC, snd_sw]
  show vP * (wP * (vP * (wP * vP))) = wP
  decide

/-! ### Their (h) fails -/

theorem smData_not_EqH : ¬ smData.EqH := by
  intro h
  have h0 := h 0 (true : SH 0)
  have hval := congrArg (fun z : SH 2 => (sElim 2 z).2) h0
  simp only at hval
  have hX : (sElim 2 (smC1 (1 + 0) (smC1 0 (true : SH 0)))).2 = vP := by
    show (sElim (1 + (1 + 0)) (smC1 (1 + 0) (smC1 0 (true : SH 0)))).2 = vP
    rw [snd_smC1, c1v_pos (n := 1 + 0) (by omega), snd_smC1, c1v]
    show cv (bv true) = vP
    rw [bv, if_pos rfl, cv_wP]
  rw [show SmCrop.cmp (sww (P := SmCrop) 0) (smData.C1 (1 + 0) (smData.C1 0 (true : SH 0)))
        = sCmp (sww (P := SmCrop) 0) (smC1 (1 + 0) (smC1 0 (true : SH 0))) from rfl,
    show SmCrop.cmp (smData.C1 (1 + 0) (smData.C1 0 (true : SH 0))) (sww (P := SmCrop) 0)
        = sCmp (smC1 (1 + 0) (smC1 0 (true : SH 0))) (sww (P := SmCrop) 0) from rfl,
    snd_sCmp, snd_sCmp, snd_sww_zero, hX] at hval
  revert hval
  show ¬ (wP * vP = vP * wP)
  decide

/-! ### The headline -/

/-- **Their equation (h) is not derivable from their other seven.**  There is a crop with
control data satisfying (a), (b), (c), (d), (e), (f) and (g), and failing (h).

Reading: `C0` and `C1` are bare arity-indexed maps on morphisms, as in
`ControlEquations.CtrlDefs`.  Under the alternative reading in which `C0`, `C1` are given as
functors, (a) and (b) are part of the data rather than equations; the statement below is
unaffected, since the model satisfies (a) and (b) anyway.

Scope: logical independence of the equational presentation only; nothing here bears on the
structural minimality of their construction. -/
theorem Ctrl.eqH_not_derivable_from_seven :
    ∃ (P : Crop) (D : Ctrl.Data P),
      D.EqA ∧ D.EqB ∧ D.EqC ∧ D.EqD ∧ D.EqE ∧ D.EqF ∧ D.EqG ∧ ¬ D.EqH :=
  ⟨SmCrop, smData, smData_EqA, smData_EqB, smData_EqC, smData_EqD, smData_EqE, smData_EqF,
    smData_EqG, smData_not_EqH⟩

end Sm

end Crops
