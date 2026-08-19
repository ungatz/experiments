{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- The zigzag quotient
--
-- A step relation on representatives, its reflexive-symmetric-transitive
-- closure as an inductive family, and the quotient of the representatives by
-- that closure as a set-quotient.  Quotienting by the family is then
-- definitionally quotienting by the closure, which is what makes the
-- generating identification a path.
--
-- Also here: symmetry of the closure, the packaging of the closure as an
-- equivalence relation, and the fact that two step relations generating each
-- other's closures give the same quotient.  That last one is what lets a
-- construction be presented by one set of generators and reasoned about
-- through another.
--
-- Upstream: Cubical.HITs.SetQuotients, Cubical.Relation.Binary.Base.
------------------------------------------------------------------------

module Poly.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum hiding (rec ; elim ; map)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary.Base

open BinaryRelation

private variable
  ℓ ℓ' : Level
  A B H G Rep : Type ℓ

-- A representative: one concrete implementation with hidden wires.
-- A representative: run : H ⊕ A → G ⊗ B, hidden input H, residual G.
record Boundary (H G A B : Type ℓ) : Type ℓ where
  constructor boundary
  field run : H ⊎ A → G × B
open Boundary public

-- The mediator zig-zag closure of a one-step relation.
-- A `Step x y` is a single mediator
-- step (an input step or an output step, depending on the
-- instantiation); the closure adds reflexivity, symmetry (zz-back),
-- and transitivity.
data ZigZag {Rep : Type ℓ} (Step : Rep → Rep → Type ℓ')
            : Rep → Rep → Type (ℓ-max ℓ ℓ') where
  zz-refl  : ∀ {x} → ZigZag Step x x
  zz-step  : ∀ {x y} → Step x y → ZigZag Step x y
  zz-back  : ∀ {x y} → Step x y → ZigZag Step y x
  zz-trans : ∀ {x y z} → ZigZag Step x y → ZigZag Step y z → ZigZag Step x z

-- Symmetry is admissible: flip every step and reverse the composite.
zz-sym : {Step : Rep → Rep → Type ℓ'} → ∀ {x y}
       → ZigZag Step x y → ZigZag Step y x
zz-sym zz-refl        = zz-refl
zz-sym (zz-step s)    = zz-back s
zz-sym (zz-back s)    = zz-step s
zz-sym (zz-trans p q) = zz-trans (zz-sym q) (zz-sym p)

-- The closure is an equivalence relation.  Downstream this feeds
-- quotient-effectivity arguments (the presentation theorem faithfulness via
-- isEquivRel→TruncIso); it must NOT be used to conclude
-- zigzag-completeness of the generating relation — see the Bool
-- counterexample ¬Universal→ZigZag in Cubical.Relation.ZigZag.Base,
-- which shows induced PERs do not imply zigzag-completeness.
zigzagIsEquivRel : {Step : Rep → Rep → Type ℓ'}
                 → isEquivRel (ZigZag Step)
zigzagIsEquivRel = equivRel (λ _ → zz-refl)
                            (λ _ _ → zz-sym)
                            (λ _ _ _ → zz-trans)

-- The mediator quotient at a fixed hom, as a set-quotient HIT.
-- The representatives at a fixed hom, quotiented by the closure.
ZigZagQuotient : {Rep : Type ℓ} → (Rep → Rep → Type ℓ') → Type (ℓ-max ℓ ℓ')
ZigZagQuotient {Rep = Rep} Step = Rep / ZigZag Step

[_]mq : {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'}
      → Rep → ZigZagQuotient Step
[_]mq = [_]

-- One mediator step yields a path between classes.
mediator-path : {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'}
              → ∀ {x y} → Step x y → [ x ]mq ≡ [ y ]mq
mediator-path {Step = Step} s = eq/ _ _ (zz-step {Step = Step} s)

-- A zig-zag also yields a path (closure of mediator-path).
zigzag-path : {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'}
            → ∀ {x y} → ZigZag Step x y → [ x ]mq ≡ [ y ]mq
zigzag-path z = eq/ _ _ z

-- Lift "every R-step is an S-zigzag" through the closure.
mapZigZag : {X : Type ℓ} {R : X → X → Type ℓ'} {ℓ'' : Level} {S : X → X → Type ℓ''}
          → (∀ x y → R x y → ZigZag S x y)
          → ∀ {x y} → ZigZag R x y → ZigZag S x y
mapZigZag h zz-refl        = zz-refl
mapZigZag h (zz-step r)    = h _ _ r
mapZigZag h (zz-back r)    = zz-sym (h _ _ r)
mapZigZag h (zz-trans p q) = zz-trans (mapZigZag h p) (mapZigZag h q)

-- If two step relations generate each other's zig-zag closures, the
-- mediator quotients coincide.  This is the engine behind the completion comparison (each
-- Heunen–Kaarsgaard generating identification is a three-step pure
-- mediator zig-zag, and conversely) and reusable for the presentation theorem.
interderivable→quotIso : {X : Type ℓ} {R : X → X → Type ℓ'} {ℓ'' : Level} {S : X → X → Type ℓ''}
  → (∀ x y → R x y → ZigZag S x y)
  → (∀ x y → S x y → ZigZag R x y)
  → Iso (ZigZagQuotient R) (ZigZagQuotient S)
interderivable→quotIso {R = R} {S = S} r→s s→r = theIso
  where
  theIso : Iso (ZigZagQuotient R) (ZigZagQuotient S)
  Iso.fun theIso =
    rec squash/ [_] (λ x y z → eq/ x y (mapZigZag r→s z))
  Iso.inv theIso =
    rec squash/ [_] (λ x y z → eq/ x y (mapZigZag s→r z))
  Iso.rightInv theIso =
    elimProp (λ _ → squash/ _ _) (λ _ → refl)
  Iso.leftInv theIso =
    elimProp (λ _ → squash/ _ _) (λ _ → refl)

-- Fold a zig-zag through any reflexive-symmetric-transitive structure
-- on a relation: if S already carries refl/sym/trans, its closure adds
-- nothing.
zigzagFold : {X : Type ℓ} {S : X → X → Type ℓ'}
  → (∀ x → S x x)
  → (∀ x y → S x y → S y x)
  → (∀ x y z → S x y → S y z → S x z)
  → ∀ {x y} → ZigZag S x y → S x y
zigzagFold r s t zz-refl = r _
zigzagFold r s t (zz-step w) = w
zigzagFold r s t (zz-back w) = s _ _ w
zigzagFold r s t (zz-trans p q) =
  t _ _ _ (zigzagFold r s t p) (zigzagFold r s t q)

-- Quotienting by an equivalence-structured relation is the same as
-- quotienting by its zig-zag closure.
closure-collapseIso : {X : Type ℓ} {S : X → X → Type ℓ'}
  → (∀ x → S x x)
  → (∀ x y → S x y → S y x)
  → (∀ x y z → S x y → S y z → S x z)
  → Iso (ZigZagQuotient S) (X / S)
closure-collapseIso {X = X} {S = S} r s t = theIso
  where
  theIso : Iso (ZigZagQuotient S) (X / S)
  Iso.fun theIso =
    rec squash/ [_] (λ x y z → eq/ x y (zigzagFold r s t z))
  Iso.inv theIso =
    rec squash/ [_] (λ x y w → eq/ x y (zz-step w))
  Iso.rightInv theIso =
    elimProp (λ _ → squash/ _ _) (λ _ → refl)
  Iso.leftInv theIso =
    elimProp (λ _ → squash/ _ _) (λ _ → refl)
