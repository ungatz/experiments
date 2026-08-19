{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Kelly's unit lemma
--
-- Over the library's MonoidalStr:
--
--   η-cancel  : id ⊗ f ≡ id ⊗ g  →  f ≡ g
--   kellyλ    : α⟨1,x,y⟩ ∘ (η⟨x⟩ ⊗ id) ≡ η⟨x ⊗ y⟩
--   kellyλ⁻   : the same with the associator moved to the other side,
--               which is the form the right-unit steps below consume.
--
-- The derivation is the classical one (Kelly 1964; Mac Lane VII): tensor both
-- sides with the unit, expand by naturality of the associator, collapse by the
-- triangle, apply the pentagon, slide the unitor out by naturality again,
-- cancel, and finish with the triangle.
------------------------------------------------------------------------

module Poly.Monoidal.Kelly where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.NaturalTransformation.Base

module KellyUnit {ℓ ℓ' : Level} (C : Category ℓ ℓ') (M : MonoidalStr C) where

  open Category C
  open MonoidalStr M
  open Functor

  private
    ⊗-idSeq : {x y y' y'' : ob} (u : Hom[ y , y' ]) (v : Hom[ y' , y'' ])
            → (id {x} ⊗ₕ u) ⋆ (id ⊗ₕ v) ≡ id ⊗ₕ (u ⋆ v)
    ⊗-idSeq u v =
      sym (─⊗─ .F-seq (id , u) (id , v))
      ∙ cong (λ w → ─⊗─ .F-hom (w , u ⋆ v)) (⋆IdL id)

    ⊗-idSeqL : {x x' x'' y : ob} (u : Hom[ x , x' ]) (v : Hom[ x' , x'' ])
             → (u ⊗ₕ id {y}) ⋆ (v ⊗ₕ id) ≡ (u ⋆ v) ⊗ₕ id
    ⊗-idSeqL u v =
      sym (─⊗─ .F-seq (u , id) (v , id))
      ∙ cong (λ w → ─⊗─ .F-hom (u ⋆ v , w)) (⋆IdL id)

    α-nat : {x x' y y' z z' : ob}
            (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
          → (f ⊗ₕ (g ⊗ₕ h)) ⋆ α⟨ x' , y' , z' ⟩
          ≡ α⟨ x , y , z ⟩ ⋆ ((f ⊗ₕ g) ⊗ₕ h)
    α-nat f g h = α .NatIso.trans .NatTrans.N-hom (f , g , h)

    η-nat : {x y : ob} (f : Hom[ x , y ])
          → (id ⊗ₕ f) ⋆ η⟨ y ⟩ ≡ η⟨ x ⟩ ⋆ f
    η-nat f = η .NatIso.trans .NatTrans.N-hom f

  ----------------------------------------------------------------------
  -- Cancelling id ⊗ −
  ----------------------------------------------------------------------

  η-cancel : {a b : ob} (f g : Hom[ a , b ])
           → id ⊗ₕ f ≡ id ⊗ₕ g → f ≡ g
  η-cancel {a} {b} f g p =
      sym (⋆IdL f)
    ∙ cong (_⋆ f) (sym (η .NatIso.nIso a .isIso.sec))
    ∙ ⋆Assoc η⁻¹⟨ a ⟩ η⟨ a ⟩ f
    ∙ cong (η⁻¹⟨ a ⟩ ⋆_) (sym (η-nat f) ∙ cong (_⋆ η⟨ b ⟩) p ∙ η-nat g)
    ∙ sym (⋆Assoc η⁻¹⟨ a ⟩ η⟨ a ⟩ g)
    ∙ cong (_⋆ g) (η .NatIso.nIso a .isIso.sec)
    ∙ ⋆IdL g

  ----------------------------------------------------------------------
  -- Kelly's λ-lemma
  ----------------------------------------------------------------------

  kellyλ : (x y : ob)
         → α⟨ unit , x , y ⟩ ⋆ (η⟨ x ⟩ ⊗ₕ id) ≡ η⟨ x ⊗ y ⟩
  kellyλ x y = η-cancel _ _ chain
    where
    a1  = α⟨ unit , x , y ⟩
    aM  = α⟨ unit , unit ⊗ x , y ⟩
    aL  = α⟨ unit , unit , x ⟩
    aT  = α⟨ unit , unit , x ⊗ y ⟩
    aU  = α⟨ unit ⊗ unit , x , y ⟩
    ρ₁  = ρ⟨ unit ⟩
    D   = ((ρ₁ ⊗ₕ id {x}) ⊗ₕ id {y}) ⋆ α⁻¹⟨ unit , x , y ⟩

    -- id ⊗ (η ⊗ id)  ≡  aM ⋆ ((aL ⊗ id) ⋆ D)
    natSwap : id ⊗ₕ (η⟨ x ⟩ ⊗ₕ id)
            ≡ aM ⋆ ((aL ⊗ₕ id) ⋆ D)
    natSwap =
        sym (⋆IdR _)
      ∙ cong ((id ⊗ₕ (η⟨ x ⟩ ⊗ₕ id)) ⋆_)
             (sym (α .NatIso.nIso (unit , x , y) .isIso.ret))
      ∙ sym (⋆Assoc _ a1 α⁻¹⟨ unit , x , y ⟩)
      ∙ cong (_⋆ α⁻¹⟨ unit , x , y ⟩) (α-nat id η⟨ x ⟩ id)
      ∙ ⋆Assoc aM ((id ⊗ₕ η⟨ x ⟩) ⊗ₕ id) α⁻¹⟨ unit , x , y ⟩
      ∙ cong (λ u → aM ⋆ ((u ⊗ₕ id) ⋆ α⁻¹⟨ unit , x , y ⟩))
             (sym (triangle unit x))
      ∙ cong (aM ⋆_)
          ( cong (_⋆ α⁻¹⟨ unit , x , y ⟩)
                 (sym (⊗-idSeqL aL (ρ₁ ⊗ₕ id)))
          ∙ ⋆Assoc (aL ⊗ₕ id) ((ρ₁ ⊗ₕ id) ⊗ₕ id) α⁻¹⟨ unit , x , y ⟩ )

    -- aU ⋆ ((ρ₁ ⊗ id) ⊗ id)  ≡  (ρ₁ ⊗ id) ⋆ a1
    αnatρ : aU ⋆ ((ρ₁ ⊗ₕ id) ⊗ₕ id) ≡ (ρ₁ ⊗ₕ id) ⋆ a1
    αnatρ =
        sym (α-nat ρ₁ id id)
      ∙ cong (λ u → (ρ₁ ⊗ₕ u) ⋆ a1) (─⊗─ .F-id)

    chain : id ⊗ₕ (a1 ⋆ (η⟨ x ⟩ ⊗ₕ id)) ≡ id ⊗ₕ η⟨ x ⊗ y ⟩
    chain =
        sym (⊗-idSeq a1 (η⟨ x ⟩ ⊗ₕ id))
      ∙ cong ((id ⊗ₕ a1) ⋆_) natSwap
      ∙ sym (⋆Assoc (id ⊗ₕ a1) aM ((aL ⊗ₕ id) ⋆ D))
      ∙ sym (⋆Assoc ((id ⊗ₕ a1) ⋆ aM) (aL ⊗ₕ id) D)
      ∙ cong (_⋆ D)
          ( ⋆Assoc (id ⊗ₕ a1) aM (aL ⊗ₕ id)
          ∙ pentagon unit unit x y )
      ∙ sym (⋆Assoc (aT ⋆ aU) ((ρ₁ ⊗ₕ id) ⊗ₕ id) α⁻¹⟨ unit , x , y ⟩)
      ∙ cong (_⋆ α⁻¹⟨ unit , x , y ⟩)
          ( ⋆Assoc aT aU ((ρ₁ ⊗ₕ id) ⊗ₕ id)
          ∙ cong (aT ⋆_) αnatρ
          ∙ sym (⋆Assoc aT (ρ₁ ⊗ₕ id) a1) )
      ∙ ⋆Assoc (aT ⋆ (ρ₁ ⊗ₕ id)) a1 α⁻¹⟨ unit , x , y ⟩
      ∙ cong ((aT ⋆ (ρ₁ ⊗ₕ id)) ⋆_)
             (α .NatIso.nIso (unit , x , y) .isIso.ret)
      ∙ ⋆IdR (aT ⋆ (ρ₁ ⊗ₕ id))
      ∙ triangle unit (x ⊗ y)

  kellyλ⁻ : (x y : ob)
          → η⟨ x ⟩ ⊗ₕ id ≡ α⁻¹⟨ unit , x , y ⟩ ⋆ η⟨ x ⊗ y ⟩
  kellyλ⁻ x y =
      sym (⋆IdL _)
    ∙ cong (_⋆ (η⟨ x ⟩ ⊗ₕ id))
           (sym (α .NatIso.nIso (unit , x , y) .isIso.sec))
    ∙ ⋆Assoc α⁻¹⟨ unit , x , y ⟩ α⟨ unit , x , y ⟩ (η⟨ x ⟩ ⊗ₕ id)
    ∙ cong (α⁻¹⟨ unit , x , y ⟩ ⋆_) (kellyλ x y)
