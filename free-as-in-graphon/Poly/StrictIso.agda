{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Isomorphism of categories, in the strict sense
--
-- A functor that is an equivalence on objects and fully faithful on every
-- hom-set.  The cubical library packages the weaker adjoint and weak notions,
-- so the strict one is fielded directly here.
--
-- In every instance below the object action is definitionally the identity, so
-- each instance witnesses an identity-on-objects isomorphism of categories on
-- the nose rather than up to a comparison.
--
-- Upstream: Cubical.Categories.{Category,Functor}.
------------------------------------------------------------------------

module Poly.StrictIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private variable
  ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

-- A strict isomorphism of categories: the underlying functor together
-- with equivalence proofs for its object action and each hom action.
-- (Cubical.Categories.Equivalence packages the weaker adjoint/weak
-- notions; both theorems here assert the strict one, so we field it
-- directly.)
record CatIsoStrict (C : Category ℓC ℓC') (D : Category ℓD ℓD')
       : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  field
    F     : Functor C D
    obEq  : isEquiv (F .F-ob)
    homEq : Functor.isFullyFaithful F

  -- Each hom action, repackaged as an isomorphism of hom-sets.
  homIso : (x y : C .ob) → Iso (C [ x , y ]) (D [ F .F-ob x , F .F-ob y ])
  homIso x y = equivToIso (F .F-hom , homEq x y)

open CatIsoStrict public
