{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Fam(D) by finite lists
--
-- The free finite coproduct completion, presented concretely.  An object is a
-- finite list of objects of D.  A morphism A -> B chooses, for every source
-- block, a target block together with a D-morphism into that block.  That is
-- the block-function variance used by Ackerman, Freer, Kaddar, Karwowski,
-- Moss, Roy, Staton and Yang when they build their base, and getting the
-- direction of the component maps right is most of the work of reading their
-- construction.
--
-- This module packages the category and nothing else.  List append is not
-- constructed as a symmetric monoidal product, the opposite family action is
-- absent, there is no point extension or restriction, and no polynomial
-- quotient is taken over it.  The index is finite lists rather than arbitrary
-- finite index types.
------------------------------------------------------------------------

module Poly.Fam where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Foundations.HLevels using (isSetΣ; isSetΠ)
open import Cubical.Data.Sigma
open import Cubical.Data.List.Base using (List; length)
open import Cubical.Data.List.FinData using (lookup)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.FinData.Properties using (isSetFin)
open import Cubical.Categories.Category

open Category

module FiniteList {ℓo ℓh : Level} (D : Category ℓo ℓh) where

  ListFamOb : Type ℓo
  ListFamOb = List (D .ob)

  ListFamHom : ListFamOb → ListFamOb → Type ℓh
  ListFamHom A B =
    Σ[ block ∈ (Fin (length A) → Fin (length B)) ]
      ((i : Fin (length A)) → D [ lookup A i , lookup B (block i) ])

  idListFam : (A : ListFamOb) → ListFamHom A A
  idListFam A = idfun _ , λ i → D .id

  _⋆ListFam_ : {A B C : ListFamOb}
             → ListFamHom A B → ListFamHom B C → ListFamHom A C
  _⋆ListFam_ {A} {B} {C} f g =
    (λ i → g .fst (f .fst i))
    , λ i → (f .snd i) ⋆⟨ D ⟩ (g .snd (f .fst i))

  ⋆IdLListFam : {A B : ListFamOb} (f : ListFamHom A B)
              → _⋆ListFam_ {A} {A} {B} (idListFam A) f ≡ f
  ⋆IdLListFam f =
    ΣPathP (refl , funExt λ i → D .⋆IdL (f .snd i))

  ⋆IdRListFam : {A B : ListFamOb} (f : ListFamHom A B)
              → _⋆ListFam_ {A} {B} {B} f (idListFam B) ≡ f
  ⋆IdRListFam f =
    ΣPathP (refl , funExt λ i → D .⋆IdR (f .snd i))

  ⋆AssocListFam : {A B C E : ListFamOb}
                (f : ListFamHom A B)
                (g : ListFamHom B C)
                (h : ListFamHom C E)
              → _⋆ListFam_ {A} {C} {E}
                  (_⋆ListFam_ {A} {B} {C} f g) h
                ≡ _⋆ListFam_ {A} {B} {E} f
                    (_⋆ListFam_ {B} {C} {E} g h)
  ⋆AssocListFam f g h =
    ΣPathP
      ( refl
      , funExt λ i →
          D .⋆Assoc (f .snd i) (g .snd (f .fst i))
            (h .snd (g .fst (f .fst i))) )

  isSetListFamHom : (A B : ListFamOb) → isSet (ListFamHom A B)
  isSetListFamHom A B =
    isSetΣ (isSetΠ λ _ → isSetFin)
      (λ block → isSetΠ λ _ → D .isSetHom)

  ListFamCat : Category ℓo ℓh
  ListFamCat .ob = ListFamOb
  ListFamCat .Hom[_,_] = ListFamHom
  ListFamCat .id {x = A} = idListFam A
  ListFamCat ._⋆_ {x = A} {y = B} {z = C} =
    _⋆ListFam_ {A} {B} {C}
  ListFamCat .⋆IdL {x = A} {y = B} f =
    ⋆IdLListFam {A = A} {B = B} f
  ListFamCat .⋆IdR {x = A} {y = B} f =
    ⋆IdRListFam {A = A} {B = B} f
  ListFamCat .⋆Assoc {x = A} {y = B} {z = C} {w = E} f g h =
    ⋆AssocListFam {A = A} {B = B} {C = C} {E = E} f g h
  ListFamCat .isSetHom {x = A} {y = B} = isSetListFamHom A B
