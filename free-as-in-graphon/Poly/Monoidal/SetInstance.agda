{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Sets as a distributive symmetric monoidal category
--
-- (SET, ×, ⊎, ⊥) as a DistSMC, so that the record is not vacuous.  Every
-- coherence is refl or a funExt of refls: the structure maps are projection
-- lambdas, so the pentagon, the triangle, the hexagon and the distributor
-- coherences all hold by computation.
--
-- The carrier is hSet, that is a type together with a proof that it is a set.
------------------------------------------------------------------------

module Poly.Monoidal.SetInstance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; isSet⊎)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty using (⊥*)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct using (_×C_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.NaturalTransformation.Base

open import Poly.Monoidal.Symmetric
open import Poly.Monoidal.Distributive

open Category
open Functor

module _ (ℓ : Level) where

  private
    _×h_ : hSet ℓ → hSet ℓ → hSet ℓ
    X ×h Y = (X .fst × Y .fst) , isSet× (X .snd) (Y .snd)

    _⊎h_ : hSet ℓ → hSet ℓ → hSet ℓ
    X ⊎h Y = (X .fst ⊎ Y .fst) , isSet⊎ (X .snd) (Y .snd)

  ----------------------------------------------------------------------
  -- The tensor and the monoidal structure
  ----------------------------------------------------------------------

  ⊗S : Functor (SET ℓ ×C SET ℓ) (SET ℓ)
  ⊗S .F-ob (X , Y)   = X ×h Y
  ⊗S .F-hom (f , g) p = f (p .fst) , g (p .snd)
  ⊗S .F-id           = refl
  ⊗S .F-seq _ _      = refl

  TS : TensorStr (SET ℓ)
  TS .TensorStr.─⊗─  = ⊗S
  TS .TensorStr.unit = Unit* , isSetUnit*

  MS : MonoidalStr (SET ℓ)
  MS .MonoidalStr.tenstr = TS
  MS .MonoidalStr.α = record
    { trans = record
        { N-ob  = λ _ p → (p .fst , p .snd .fst) , p .snd .snd
        ; N-hom = λ _ → refl }
    ; nIso = λ _ → isiso
        (λ p → p .fst .fst , (p .fst .snd , p .snd)) refl refl }
  MS .MonoidalStr.η = record
    { trans = record { N-ob = λ _ p → p .snd ; N-hom = λ _ → refl }
    ; nIso = λ _ → isiso (λ x → tt* , x) refl refl }
  MS .MonoidalStr.ρ = record
    { trans = record { N-ob = λ _ p → p .fst ; N-hom = λ _ → refl }
    ; nIso = λ _ → isiso (λ x → x , tt*) refl refl }
  MS .MonoidalStr.pentagon = λ _ _ _ _ → refl
  MS .MonoidalStr.triangle = λ _ _ → refl

  ----------------------------------------------------------------------
  -- The symmetry
  ----------------------------------------------------------------------

  SS : SymmetricStr (SET ℓ) MS
  SS .SymmetricStr.B⟨_,_⟩  = λ _ _ p → p .snd , p .fst
  SS .SymmetricStr.B-nat   = λ _ _ → refl
  SS .SymmetricStr.B-invol = λ _ _ → refl
  SS .SymmetricStr.hexagon = λ _ _ _ → refl

  ----------------------------------------------------------------------
  -- Coproducts, initial object, distributor, annihilator
  ----------------------------------------------------------------------

  coprodS : BinCoproducts (SET ℓ)
  coprodS X Y .BinCoproduct.binCoprodOb   = X ⊎h Y
  coprodS X Y .BinCoproduct.binCoprodInj₁ = Sum.inl
  coprodS X Y .BinCoproduct.binCoprodInj₂ = Sum.inr
  coprodS X Y .BinCoproduct.univProp {z = Z} f₁ f₂ =
    (Sum.rec f₁ f₂ , refl , refl) , uniq
    where
    uniq : (t : Σ[ g ∈ _ ] _) → (Sum.rec f₁ f₂ , refl , refl) ≡ t
    uniq (g , p₁ , p₂) = Σ≡Prop
      (λ h → isProp×
        (isSetΠ (λ _ → Z .snd) _ _) (isSetΠ (λ _ → Z .snd) _ _))
      (funExt λ { (Sum.inl x) → sym (funExt⁻ p₁ x)
                ; (Sum.inr y) → sym (funExt⁻ p₂ y) })

  initS : Initial (SET ℓ)
  initS = (⊥* , isProp→isSet (λ x → Empty.rec (Empty.rec* x)))
        , λ Y → (λ x → Empty.rec (Empty.rec* x))
        , λ f → funExt (λ x → Empty.rec (Empty.rec* x))

  ----------------------------------------------------------------------
  -- The distributor, componentwise
  ----------------------------------------------------------------------

  δfun : (X Y Z : hSet ℓ)
       → ((X ×h Y) ⊎h (X ×h Z)) .fst → (X ×h (Y ⊎h Z)) .fst
  δfun X Y Z = Sum.rec (λ p → p .fst , Sum.inl (p .snd))
                       (λ p → p .fst , Sum.inr (p .snd))

  δinv : (X Y Z : hSet ℓ)
       → (X ×h (Y ⊎h Z)) .fst → ((X ×h Y) ⊎h (X ×h Z)) .fst
  δinv X Y Z p = Sum.rec (λ y → Sum.inl (p .fst , y))
                         (λ z → Sum.inr (p .fst , z)) (p .snd)

  δsec : (X Y Z : hSet ℓ) (x : X .fst) (s : (Y ⊎h Z) .fst)
       → δfun X Y Z (δinv X Y Z (x , s)) ≡ (x , s)
  δsec X Y Z x (Sum.inl y) = refl
  δsec X Y Z x (Sum.inr z) = refl

  δret : (X Y Z : hSet ℓ) (q : ((X ×h Y) ⊎h (X ×h Z)) .fst)
       → δinv X Y Z (δfun X Y Z q) ≡ q
  δret X Y Z (Sum.inl p) = refl
  δret X Y Z (Sum.inr p) = refl

  ----------------------------------------------------------------------
  -- The assembled instance
  ----------------------------------------------------------------------

  SetDistSMC : DistSMC (ℓ-suc ℓ) ℓ
  SetDistSMC .DistSMC.C = SET ℓ
  SetDistSMC .DistSMC.M = MS
  SetDistSMC .DistSMC.S = SS
  SetDistSMC .DistSMC.coprods  = coprodS
  SetDistSMC .DistSMC.initialD = initS
  SetDistSMC .DistSMC.δ⟨_,_,_⟩ = λ X Y Z →
    δfun X Y Z
    , isiso (δinv X Y Z)
        (funExt (λ p → δsec X Y Z (p .fst) (p .snd)))
        (funExt (δret X Y Z))
  SetDistSMC .DistSMC.δ-nat = λ f g h →
    funExt (λ { (Sum.inl p) → refl ; (Sum.inr p) → refl })
  SetDistSMC .DistSMC.δ-ι₁ = λ X Y Z → refl
  SetDistSMC .DistSMC.annih = λ X Y →
    (λ p → Empty.rec (Empty.rec* (p .snd)))
    , λ f → funExt (λ p → Empty.rec (Empty.rec* (p .snd)))
