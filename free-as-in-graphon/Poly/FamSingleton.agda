{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- The singleton inclusion
--
-- D -> Fam(D) sending an object to the one-block list, as an ordinary functor.
--
-- What it is careful not to claim.  The inclusion is NOT monoidal for list
-- concatenation: the concatenation of [A] and [B] has two blocks, while the
-- list of a single tensor has one.  Conflating those two tensors looks
-- harmless and is not; it is the step that makes a comparison with the free
-- finite-family completion appear to work when it does not.  Monoidality for
-- the original index has to be imposed separately, and is absent here.
--
-- Cubical Agda does not support the indexed match on Fin 1 that the obvious
-- definition wants, so components are transported along the contraction of
-- Fin 1 and the two transport coherences are proved by explicit path induction.
--
-- No full faithfulness and no point-extension theorem is proved here.
------------------------------------------------------------------------

module Poly.FamSingleton where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Data.Sigma
open import Cubical.Data.List.Base using ([_])
open import Cubical.Data.List.FinData using (lookup)
open import Cubical.Data.FinData using (Fin; zero)
open import Cubical.Data.FinData.Properties using (isContrFin1)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Poly.Fam

open Category
open Functor

module Singleton {ℓo ℓh : Level} (D : Category ℓo ℓh) where

  open FiniteList D

  singletonComponent : {A B : D .ob}
                     → Category.Hom[_,_] D A B
                     → (i : Fin 1)
                     → Category.Hom[_,_] D (lookup [ A ] i) (lookup [ B ] i)
  singletonComponent {A} {B} f i =
    subst
      (λ j → Category.Hom[_,_] D (lookup [ A ] j) (lookup [ B ] j))
      (isContrFin1 .snd i) f

  singletonHom : {A B : D .ob}
               → Category.Hom[_,_] D A B → ListFamHom [ A ] [ B ]
  singletonHom f = idfun _ , singletonComponent f

  singletonComponent-id : {A : D .ob} (i : Fin 1)
                        → singletonComponent (D .id {x = A}) i ≡ D .id
  singletonComponent-id {A} i =
    J {x = zero}
      (λ j p →
        subst
          (λ k → Category.Hom[_,_] D (lookup [ A ] k) (lookup [ A ] k))
          p (D .id)
        ≡ D .id)
      (substRefl
        {B = λ k → Category.Hom[_,_] D (lookup [ A ] k) (lookup [ A ] k)}
        {x = zero}
        (D .id))
      (isContrFin1 .snd i)

  singletonComponent-seq : {A B C : D .ob}
                         (f : Category.Hom[_,_] D A B)
                         (g : Category.Hom[_,_] D B C)
                         (i : Fin 1)
                       → singletonComponent (f ⋆⟨ D ⟩ g) i
                       ≡ singletonComponent f i ⋆⟨ D ⟩ singletonComponent g i
  singletonComponent-seq {A} {B} {C} f g i =
    J {x = zero}
      (λ j p →
        subst
          (λ k → Category.Hom[_,_] D (lookup [ A ] k) (lookup [ C ] k))
          p (f ⋆⟨ D ⟩ g)
        ≡
        subst
          (λ k → Category.Hom[_,_] D (lookup [ A ] k) (lookup [ B ] k))
          p f
        ⋆⟨ D ⟩
        subst
          (λ k → Category.Hom[_,_] D (lookup [ B ] k) (lookup [ C ] k))
          p g)
      ( substRefl
          {B = λ k → Category.Hom[_,_] D (lookup [ A ] k) (lookup [ C ] k)}
          {x = zero}
          (f ⋆⟨ D ⟩ g)
      ∙ sym
          (cong₂ (Category._⋆_ D)
            (substRefl
              {B = λ k → Category.Hom[_,_] D (lookup [ A ] k) (lookup [ B ] k)}
              {x = zero}
              f)
            (substRefl
              {B = λ k → Category.Hom[_,_] D (lookup [ B ] k) (lookup [ C ] k)}
              {x = zero}
              g)) )
      (isContrFin1 .snd i)

  record SingletonFunctorLaws : Type (ℓ-max ℓo ℓh) where
    field
      singleton-id : {A : D .ob}
                   → singletonHom (D .id {x = A}) ≡ idListFam [ A ]
      singleton-seq : {A B C : D .ob}
                    (f : Category.Hom[_,_] D A B)
                    (g : Category.Hom[_,_] D B C)
                  → singletonHom (f ⋆⟨ D ⟩ g)
                  ≡ _⋆ListFam_ {[ A ]} {[ B ]} {[ C ]}
                      (singletonHom f) (singletonHom g)

  singletonFunctor : SingletonFunctorLaws → Functor D ListFamCat
  singletonFunctor laws .F-ob A = [ A ]
  singletonFunctor laws .F-hom = singletonHom
  singletonFunctor laws .F-id = laws .SingletonFunctorLaws.singleton-id
  singletonFunctor laws .F-seq = laws .SingletonFunctorLaws.singleton-seq

  singletonLaws : SingletonFunctorLaws
  singletonLaws .SingletonFunctorLaws.singleton-id =
    ΣPathP (refl , funExt singletonComponent-id)
  singletonLaws .SingletonFunctorLaws.singleton-seq f g =
    ΣPathP (refl , funExt (singletonComponent-seq f g))

  singletonInclusion : Functor D ListFamCat
  singletonInclusion = singletonFunctor singletonLaws
