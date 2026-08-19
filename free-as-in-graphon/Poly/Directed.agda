{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Coproducts and an initial object in the polynomial category
--
-- For an index that is directed, meaning proposition-valued homs, at least one
-- object, and a chosen common source on every pair, the comparison of the
-- previous module is assembled into an isomorphism here.  If in addition the canonical left distributor of the base is
-- invertible, that comparison packages the base coproduct objects as genuine
-- coproducts in the polynomial category.  The base initial object stays
-- initial for the same reason.
--
-- The distributor field of DistSMC is deliberately not used: its second
-- injection leg is not determined by the rest of the record, so the canonical
-- left comparison is built directly.
--
-- This module proves binary coproducts and an initial object for the
-- polynomial category, and carries each canonical base distributor
-- isomorphism through the adjoining functor.  It does not construct the
-- symmetric monoidal structure upstairs, so it does not package a
-- distributive base for the polynomial category, and the image of the base
-- distributor is not identified with a distributor upstairs.  Directedness is
-- sufficient and is not claimed necessary; no characterisation by siftedness
-- is claimed either.
--
-- Sources: Hermida and Tennent, ENTCS 249 (2009); Adamek, Rosicky and Vitale,
-- TAC 23 (2010), section 1.
------------------------------------------------------------------------

module Poly.Directed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet× ; isProp×)
open import Cubical.Foundations.Isomorphism using (Iso ; compIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.Initial
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/)

open import Poly.Base
open import Poly.Monoidal.Symmetric
open import Poly.Monoidal.Distributive
open import Poly.Kit
open import Poly.Category
open import Poly.DirectedColimit

private
  variable
    ℓΣ ℓΣ' ℓC ℓC' : Level

------------------------------------------------------------------------
-- The exact extra hypotheses
------------------------------------------------------------------------

BaseSMC : DistSMC ℓC ℓC' → SymmMonCategory ℓC ℓC'
BaseSMC D .SymmMonCategory.C = D .DistSMC.C
BaseSMC D .SymmMonCategory.M = D .DistSMC.M
BaseSMC D .SymmMonCategory.S = D .DistSMC.S

record DirectedIndex (Σb : SymmMonCategory ℓΣ ℓΣ')
       : Type (ℓ-max ℓΣ ℓΣ') where
  module ΣM = SymmMonCategory Σb
  field
    hom-prop   : {u v : ΣM.ob} → isProp ΣM.Hom[ u , v ]
    inhabitant : ΣM.ob
    meet       : ΣM.ob → ΣM.ob → ΣM.ob
    meet-l     : (u v : ΣM.ob) → ΣM.Hom[ meet u v , u ]
    meet-r     : (u v : ΣM.ob) → ΣM.Hom[ meet u v , v ]

module _ (D : DistSMC ℓC ℓC') where
  open DistSMC D

  -- The canonical direct left comparison.  DistSMC's existing
  -- distributor field is intentionally not used: its second injection
  -- leg is not determined by the current API.
  dmL : (a b z : ob) → Hom[ (a ⊗ z) ⊕ (b ⊗ z) , (a ⊕ b) ⊗ z ]
  dmL a b z = copair (ι₁ ⊗ₕ id) (ι₂ ⊗ₕ id)

  record CanonicalDistributorIso : Type (ℓ-max ℓC ℓC') where
    field
      dmL-iso : (a b z : ob) → isIso C (dmL a b z)

------------------------------------------------------------------------
-- Directed polynomial homs and the product comparison
------------------------------------------------------------------------

module DirectedPolynomial
       (D   : DistSMC ℓC ℓC')
       (Σb  : SymmMonCategory ℓΣ ℓΣ')
       (j   : StrongMonoFunctor Σb (BaseSMC D))
       (dir : DirectedIndex Σb)
       (can : CanonicalDistributorIso D) where

  module C = DistSMC D
  module ΣM = SymmMonCategory Σb
  module J = StrongMonoFunctor j
  module DI = DirectedIndex dir
  module Can = CanonicalDistributorIso can
  module P = PolyOver Σb (BaseSMC D) j
  module K = Kit D

  Γ : DirectedGraph ℓΣ ℓΣ'
  Γ .DirectedGraph.Heap = ΣM.ob
  Γ .DirectedGraph.Med = ΣM.Hom[_,_]
  Γ .DirectedGraph.Med-prop = DI.hom-prop
  Γ .DirectedGraph.Med-trans r s = r ΣM.⋆ s
  Γ .DirectedGraph.meet = DI.meet
  Γ .DirectedGraph.meet-l = DI.meet-l
  Γ .DirectedGraph.meet-r = DI.meet-r

  CoreF : (A Y : C.ob) → DirectedFamily Γ ℓC'
  CoreF A Y .DirectedFamily.Core w =
    C.Hom[ A C.⊗ J.F₀ w , Y ]
  CoreF A Y .DirectedFamily.isSetCore = C.isSetHom
  CoreF A Y .DirectedFamily.pull r f =
    (C.id C.⊗ₕ J.F₁ r) C.⋆ f
  CoreF A Y .DirectedFamily.pull-∘ r s t f =
      sym (C.⋆Assoc _ _ f)
    ∙ cong (C._⋆ f) (P.id⊗Cs (J.F₁ r) (J.F₁ s))
    ∙ cong (λ q → (C.id C.⊗ₕ q) C.⋆ f) (sym (J.F-seq r s))
    ∙ cong (λ q → (C.id C.⊗ₕ J.F₁ q) C.⋆ f)
        (DI.hom-prop (r ΣM.⋆ s) t)

  module DirectedProduct (A B Y : C.ob) where
    F : DirectedFamily Γ ℓC'
    F = CoreF A Y

    G : DirectedFamily Γ ℓC'
    G = CoreF B Y

    module DC = Comparison Γ F G
    module FQ = Over Γ F
    module GQ = Over Γ G
    module PQ = Over Γ DC.pairF

    pack : FQ.Rep → GQ.Rep → PQ.Quot
    pack (a , u) (b , v) =
      [ ( DI.meet a b
        , ( F .DirectedFamily.pull (DI.meet-l a b) u
          , G .DirectedFamily.pull (DI.meet-r a b) v ) ) ]

    pack-left :
        {x x' : FQ.Rep} (y : GQ.Rep)
      → ZigZag FQ.Step x x'
      → pack x y ≡ pack x' y
    pack-left {x = a , u} {x' = a' , u'} (b , v) pf =
      DC.align
        (zz-trans
          (zz-step (DI.meet-l a b , refl))
          (zz-trans pf (zz-back (DI.meet-l a' b , refl))))
        (zz-trans
          (zz-step (DI.meet-r a b , refl))
          (zz-back (DI.meet-r a' b , refl)))

    pack-right :
        (x : FQ.Rep) {y y' : GQ.Rep}
      → ZigZag GQ.Step y y'
      → pack x y ≡ pack x y'
    pack-right (a , u) {y = b , v} {y' = b' , v'} pg =
      DC.align
        (zz-trans
          (zz-step (DI.meet-l a b , refl))
          (zz-back (DI.meet-l a b' , refl)))
        (zz-trans
          (zz-step (DI.meet-r a b , refl))
          (zz-trans pg (zz-back (DI.meet-r a b' , refl))))

    uncompare₂ : FQ.Quot → GQ.Quot → PQ.Quot
    uncompare₂ = SQ.rec2 squash/ pack
      (λ x x' y pf → pack-left y pf)
      (λ x y y' pg → pack-right x pg)

    uncompare : FQ.Quot × GQ.Quot → PQ.Quot
    uncompare (qF , qG) = uncompare₂ qF qG

    compare-uncompare :
        (qF : FQ.Quot) (qG : GQ.Quot)
      → DC.compare (uncompare₂ qF qG) ≡ (qF , qG)
    compare-uncompare =
      SQ.elimProp2
        (λ _ _ → isSet× squash/ squash/ _ _)
        (λ (a , u) (b , v) → DC.compare-surj a b u v)

    uncompare-compare :
        (q : PQ.Quot)
      → uncompare (DC.compare q) ≡ q
    uncompare-compare =
      SQ.elimProp
        (λ _ → squash/ _ _)
        (λ (w , (u , v)) →
          DC.align
            (zz-step (DI.meet-l w w , refl))
            (zz-step (DI.meet-r w w , refl)))

    directedProductIso : Iso PQ.Quot (FQ.Quot × GQ.Quot)
    directedProductIso .Iso.fun = DC.compare
    directedProductIso .Iso.inv = uncompare
    directedProductIso .Iso.rightInv (qF , qG) =
      compare-uncompare qF qG
    directedProductIso .Iso.leftInv = uncompare-compare

  ----------------------------------------------------------------------
  -- Canonical left distributor calculus
  ----------------------------------------------------------------------

  dmL⁻¹ : (A B X : C.ob)
        → C.Hom[ (A C.⊕ B) C.⊗ X , (A C.⊗ X) C.⊕ (B C.⊗ X) ]
  dmL⁻¹ A B X = isIso.inv (Can.dmL-iso A B X)

  dmL-sec : (A B X : C.ob)
          → dmL⁻¹ A B X C.⋆ dmL D A B X ≡ C.id
  dmL-sec A B X = isIso.sec (Can.dmL-iso A B X)

  dmL-ret : (A B X : C.ob)
          → dmL D A B X C.⋆ dmL⁻¹ A B X ≡ C.id
  dmL-ret A B X = isIso.ret (Can.dmL-iso A B X)

  dmL-β₁ : (A B X : C.ob)
         → C.ι₁ C.⋆ dmL D A B X
         ≡ C.ι₁ C.⊗ₕ C.id {X}
  dmL-β₁ A B X =
    K.β₁ (C.ι₁ C.⊗ₕ C.id {X}) (C.ι₂ C.⊗ₕ C.id {X})

  dmL-β₂ : (A B X : C.ob)
         → C.ι₂ C.⋆ dmL D A B X
         ≡ C.ι₂ C.⊗ₕ C.id {X}
  dmL-β₂ A B X =
    K.β₂ (C.ι₁ C.⊗ₕ C.id {X}) (C.ι₂ C.⊗ₕ C.id {X})

  -- Naturality square for tensoring a visible precomposition with a
  -- heap map.  Both sides are the same tensor r ⊗ k.
  tensor-square :
      {A B X X' : C.ob}
      (r : C.Hom[ A , B ]) (k : C.Hom[ X , X' ])
    → (r C.⊗ₕ C.id {X}) C.⋆ (C.id {B} C.⊗ₕ k)
    ≡ (C.id {A} C.⊗ₕ k) C.⋆ (r C.⊗ₕ C.id {X'})
  tensor-square r k =
      P.⊗C-seq r C.id C.id k
    ∙ cong₂ C._⊗ₕ_ (C.⋆IdR r) (C.⋆IdL k)
    ∙ sym (cong₂ C._⊗ₕ_ (C.⋆IdL r) (C.⋆IdR k))
    ∙ sym (P.⊗C-seq C.id r k C.id)

  tensor-precompose-nat :
      {A B X X' Y : C.ob}
      (r : C.Hom[ A , B ]) (k : C.Hom[ X , X' ])
      (f : C.Hom[ B C.⊗ X' , Y ])
    → (r C.⊗ₕ C.id {X}) C.⋆ ((C.id {B} C.⊗ₕ k) C.⋆ f)
    ≡ (C.id {A} C.⊗ₕ k) C.⋆ ((r C.⊗ₕ C.id {X'}) C.⋆ f)
  tensor-precompose-nat r k f =
      sym (C.⋆Assoc _ _ f)
    ∙ cong (C._⋆ f) (tensor-square r k)
    ∙ C.⋆Assoc _ _ f

  -- Naturality of the canonical distributor follows from coproduct
  -- extensionality; no naturality field of DistSMC's abstract
  -- distributor is used.
  dmL-nat :
      {A B X X' : C.ob} (k : C.Hom[ X , X' ])
    → ((C.id {A} C.⊗ₕ k) C.⊕₁ (C.id {B} C.⊗ₕ k))
        C.⋆ dmL D A B X'
    ≡ dmL D A B X C.⋆ (C.id {A C.⊕ B} C.⊗ₕ k)
  dmL-nat {A} {B} {X} {X'} k =
    K.⊕-ext _ _ leg₁ leg₂
    where
    p = C.id {A} C.⊗ₕ k
    q = C.id {B} C.⊗ₕ k
    h = C.id {A C.⊕ B} C.⊗ₕ k

    leg₁ :
      C.ι₁ C.⋆ (((p C.⊕₁ q) C.⋆ dmL D A B X'))
      ≡ C.ι₁ C.⋆ (dmL D A B X C.⋆ h)
    leg₁ =
        K.push₁ p q (dmL D A B X')
      ∙ cong (p C.⋆_) (dmL-β₁ A B X')
      ∙ sym (tensor-square C.ι₁ k)
      ∙ cong (C._⋆ h) (sym (dmL-β₁ A B X))
      ∙ C.⋆Assoc C.ι₁ (dmL D A B X) h

    leg₂ :
      C.ι₂ C.⋆ (((p C.⊕₁ q) C.⋆ dmL D A B X'))
      ≡ C.ι₂ C.⋆ (dmL D A B X C.⋆ h)
    leg₂ =
        K.push₂ p q (dmL D A B X')
      ∙ cong (q C.⋆_) (dmL-β₂ A B X')
      ∙ sym (tensor-square C.ι₂ k)
      ∙ cong (C._⋆ h) (sym (dmL-β₂ A B X))
      ∙ C.⋆Assoc C.ι₂ (dmL D A B X) h

  dmL⁻¹-nat :
      {A B X X' : C.ob} (k : C.Hom[ X , X' ])
    → dmL⁻¹ A B X
        C.⋆ ((C.id {A} C.⊗ₕ k) C.⊕₁ (C.id {B} C.⊗ₕ k))
    ≡ (C.id {A C.⊕ B} C.⊗ₕ k) C.⋆ dmL⁻¹ A B X'
  dmL⁻¹-nat {A} {B} {X} {X'} k =
    P.cancel-post (Can.dmL-iso A B X') (
        C.⋆Assoc inv p (dmL D A B X')
      ∙ cong (inv C.⋆_) (dmL-nat k)
      ∙ sym (C.⋆Assoc inv (dmL D A B X) h)
      ∙ cong (C._⋆ h) (dmL-sec A B X)
      ∙ C.⋆IdL h
      ∙ sym (
          C.⋆Assoc h inv' (dmL D A B X')
        ∙ cong (h C.⋆_) (dmL-sec A B X')
        ∙ C.⋆IdR h))
    where
    inv = dmL⁻¹ A B X
    inv' = dmL⁻¹ A B X'
    p = (C.id {A} C.⊗ₕ k) C.⊕₁ (C.id {B} C.⊗ₕ k)
    h = C.id {A C.⊕ B} C.⊗ₕ k

  ----------------------------------------------------------------------
  -- Same-heap splitting and joining, descended to the quotient
  ----------------------------------------------------------------------

  module CoreCoproduct (A B Y : C.ob) where
    module DP = DirectedProduct A B Y

    splitCore :
        (w : ΣM.ob)
      → C.Hom[ (A C.⊕ B) C.⊗ J.F₀ w , Y ]
      → DP.DC.pairF .DirectedFamily.Core w
    splitCore w f =
      ( (C.ι₁ C.⊗ₕ C.id {J.F₀ w}) C.⋆ f
      , (C.ι₂ C.⊗ₕ C.id {J.F₀ w}) C.⋆ f )

    joinCore :
        (w : ΣM.ob)
      → DP.DC.pairF .DirectedFamily.Core w
      → C.Hom[ (A C.⊕ B) C.⊗ J.F₀ w , Y ]
    joinCore w (u , v) =
      dmL⁻¹ A B (J.F₀ w) C.⋆ C.copair u v

    splitRep : P.Repr (A C.⊕ B) Y → DP.PQ.Rep
    splitRep (w , f) = w , splitCore w f

    joinRep : DP.PQ.Rep → P.Repr (A C.⊕ B) Y
    joinRep (w , p) = w , joinCore w p

    splitStep :
        {x x' : P.Repr (A C.⊕ B) Y}
      → P.PStep (A C.⊕ B) Y x x'
      → DP.PQ.Step (splitRep x) (splitRep x')
    splitStep {x = w , f} {x' = w' , f'} (h , e) =
      h , λ i → e₁ i , e₂ i
      where
      e₁ :
          (C.ι₁ C.⊗ₕ C.id {J.F₀ w}) C.⋆ f
        ≡ (C.id {A} C.⊗ₕ J.F₁ h)
            C.⋆ ((C.ι₁ C.⊗ₕ C.id {J.F₀ w'}) C.⋆ f')
      e₁ =
          cong ((C.ι₁ C.⊗ₕ C.id {J.F₀ w}) C.⋆_) e
        ∙ tensor-precompose-nat C.ι₁ (J.F₁ h) f'

      e₂ :
          (C.ι₂ C.⊗ₕ C.id {J.F₀ w}) C.⋆ f
        ≡ (C.id {B} C.⊗ₕ J.F₁ h)
            C.⋆ ((C.ι₂ C.⊗ₕ C.id {J.F₀ w'}) C.⋆ f')
      e₂ =
          cong ((C.ι₂ C.⊗ₕ C.id {J.F₀ w}) C.⋆_) e
        ∙ tensor-precompose-nat C.ι₂ (J.F₁ h) f'

    joinStep :
        {x x' : DP.PQ.Rep}
      → DP.PQ.Step x x'
      → P.PStep (A C.⊕ B) Y (joinRep x) (joinRep x')
    joinStep {x = w , u , v} {x' = w' , u' , v'} (h , e) =
      h , eq
      where
      p = C.id {A} C.⊗ₕ J.F₁ h
      q = C.id {B} C.⊗ₕ J.F₁ h
      k = C.id {A C.⊕ B} C.⊗ₕ J.F₁ h
      cp = C.copair u' v'

      eq :
          dmL⁻¹ A B (J.F₀ w) C.⋆ C.copair u v
        ≡ k C.⋆ (dmL⁻¹ A B (J.F₀ w') C.⋆ cp)
      eq =
          cong (λ z → dmL⁻¹ A B (J.F₀ w)
            C.⋆ C.copair (fst z) (snd z)) e
        ∙ cong (dmL⁻¹ A B (J.F₀ w) C.⋆_)
            (sym (K.⊕₁-copair p q u' v'))
        ∙ sym (C.⋆Assoc (dmL⁻¹ A B (J.F₀ w)) (p C.⊕₁ q) cp)
        ∙ cong (C._⋆ cp) (dmL⁻¹-nat (J.F₁ h))
        ∙ C.⋆Assoc k (dmL⁻¹ A B (J.F₀ w')) cp

    splitQ : P.PQuot (A C.⊕ B) Y → DP.PQ.Quot
    splitQ =
      SQ.rec squash/ (λ x → [ splitRep x ])
        (λ x x' zz → eq/ _ _
          (P.mapFenceP splitRep splitStep zz))

    joinQ : DP.PQ.Quot → P.PQuot (A C.⊕ B) Y
    joinQ =
      SQ.rec squash/ (λ x → [ joinRep x ])
        (λ x x' zz → eq/ _ _
          (P.mapFenceP joinRep joinStep zz))

    leg₁-inv :
        (w : ΣM.ob)
      → (C.ι₁ C.⊗ₕ C.id {J.F₀ w})
          C.⋆ dmL⁻¹ A B (J.F₀ w)
      ≡ C.ι₁
    leg₁-inv w =
        cong (C._⋆ dmL⁻¹ A B (J.F₀ w))
          (sym (dmL-β₁ A B (J.F₀ w)))
      ∙ C.⋆Assoc C.ι₁ (dmL D A B (J.F₀ w))
          (dmL⁻¹ A B (J.F₀ w))
      ∙ cong (C.ι₁ C.⋆_) (dmL-ret A B (J.F₀ w))
      ∙ C.⋆IdR C.ι₁

    leg₂-inv :
        (w : ΣM.ob)
      → (C.ι₂ C.⊗ₕ C.id {J.F₀ w})
          C.⋆ dmL⁻¹ A B (J.F₀ w)
      ≡ C.ι₂
    leg₂-inv w =
        cong (C._⋆ dmL⁻¹ A B (J.F₀ w))
          (sym (dmL-β₂ A B (J.F₀ w)))
      ∙ C.⋆Assoc C.ι₂ (dmL D A B (J.F₀ w))
          (dmL⁻¹ A B (J.F₀ w))
      ∙ cong (C.ι₂ C.⋆_) (dmL-ret A B (J.F₀ w))
      ∙ C.⋆IdR C.ι₂

    split-join-core :
        (w : ΣM.ob) (p : DP.DC.pairF .DirectedFamily.Core w)
      → splitCore w (joinCore w p) ≡ p
    split-join-core w (u , v) i = e₁ i , e₂ i
      where
      e₁ :
          (C.ι₁ C.⊗ₕ C.id {J.F₀ w})
            C.⋆ (dmL⁻¹ A B (J.F₀ w) C.⋆ C.copair u v)
        ≡ u
      e₁ =
          sym (C.⋆Assoc _ _ (C.copair u v))
        ∙ cong (C._⋆ C.copair u v) (leg₁-inv w)
        ∙ K.β₁ u v

      e₂ :
          (C.ι₂ C.⊗ₕ C.id {J.F₀ w})
            C.⋆ (dmL⁻¹ A B (J.F₀ w) C.⋆ C.copair u v)
        ≡ v
      e₂ =
          sym (C.⋆Assoc _ _ (C.copair u v))
        ∙ cong (C._⋆ C.copair u v) (leg₂-inv w)
        ∙ K.β₂ u v

    join-split-core :
        (w : ΣM.ob) (f : C.Hom[ (A C.⊕ B) C.⊗ J.F₀ w , Y ])
      → joinCore w (splitCore w f) ≡ f
    join-split-core w f =
        cong (dmL⁻¹ A B (J.F₀ w) C.⋆_)
          (sym (K.copair-post
            (C.ι₁ C.⊗ₕ C.id {J.F₀ w})
            (C.ι₂ C.⊗ₕ C.id {J.F₀ w}) f))
      ∙ sym (C.⋆Assoc (dmL⁻¹ A B (J.F₀ w))
          (dmL D A B (J.F₀ w)) f)
      ∙ cong (C._⋆ f) (dmL-sec A B (J.F₀ w))
      ∙ C.⋆IdL f

    boxPair :
        (w : ΣM.ob)
      → DP.DC.pairF .DirectedFamily.Core w
      → DP.PQ.Quot
    boxPair w z = [ (w , z) ]

    boxPoly :
        (w : ΣM.ob)
      → C.Hom[ (A C.⊕ B) C.⊗ J.F₀ w , Y ]
      → P.PQuot (A C.⊕ B) Y
    boxPoly w z = [ (w , z) ]

    split-joinQ : (q : DP.PQ.Quot) → splitQ (joinQ q) ≡ q
    split-joinQ =
      SQ.elimProp
        (λ _ → squash/ _ _)
        (λ (w , p) → cong (boxPair w)
          (split-join-core w p))

    join-splitQ :
        (q : P.PQuot (A C.⊕ B) Y)
      → joinQ (splitQ q) ≡ q
    join-splitQ =
      SQ.elimProp
        (λ _ → squash/ _ _)
        (λ (w , f) → cong (boxPoly w)
          (join-split-core w f))

    coreProductIso :
      Iso (P.PQuot (A C.⊕ B) Y) DP.PQ.Quot
    coreProductIso .Iso.fun = splitQ
    coreProductIso .Iso.inv = joinQ
    coreProductIso .Iso.rightInv = split-joinQ
    coreProductIso .Iso.leftInv = join-splitQ

    restrictIso :
      Iso (P.PQuot (A C.⊕ B) Y)
          (P.PQuot A Y × P.PQuot B Y)
    restrictIso = compIso coreProductIso DP.directedProductIso

  ----------------------------------------------------------------------
  -- Precomposition by a raw base arrow
  ----------------------------------------------------------------------

  preRep :
      {A B Y : C.ob} (r : C.Hom[ A , B ])
    → P.Repr B Y → P.Repr A Y
  preRep r (w , f) =
    w , (r C.⊗ₕ C.id {J.F₀ w}) C.⋆ f

  preStep :
      {A B Y : C.ob} (r : C.Hom[ A , B ])
      {x x' : P.Repr B Y}
    → P.PStep B Y x x'
    → P.PStep A Y (preRep r x) (preRep r x')
  preStep r {x = w , f} {x' = w' , f'} (h , e) =
    h ,
      ( cong ((r C.⊗ₕ C.id {J.F₀ w}) C.⋆_) e
      ∙ tensor-precompose-nat r (J.F₁ h) f' )

  preQ :
      {A B Y : C.ob} (r : C.Hom[ A , B ])
    → P.PQuot B Y → P.PQuot A Y
  preQ r =
    SQ.rec squash/ (λ x → [ preRep r x ])
      (λ x x' zz → eq/ _ _
        (P.mapFenceP (preRep r) (preStep r) zz))

  raw-factor :
      {A B : C.ob} (r : C.Hom[ A , B ])
    → P.rawRep r .snd ≡ P.idRepr A .snd C.⋆ r
  raw-factor {A} r =
    sym (C.⋆Assoc
      (C.id {A} C.⊗ₕ P.γ⁻¹)
      C.ρ⟨ A ⟩ r)

  raw-precompose-inner :
      {A B Y : C.ob}
      (r : C.Hom[ A , B ]) (w : ΣM.ob)
      (f : C.Hom[ B C.⊗ J.F₀ w , Y ])
    → (P.rawRep r .snd C.⊗ₕ C.id {J.F₀ w}) C.⋆ f
    ≡ (P.idRepr A .snd C.⊗ₕ C.id {J.F₀ w})
        C.⋆ ((r C.⊗ₕ C.id {J.F₀ w}) C.⋆ f)
  raw-precompose-inner {A} r w f =
      cong (λ q → (q C.⊗ₕ C.id {J.F₀ w}) C.⋆ f)
        (raw-factor r)
    ∙ cong (C._⋆ f) (P.split⊗id (P.idRepr A .snd) r)
    ∙ C.⋆Assoc
        (P.idRepr A .snd C.⊗ₕ C.id {J.F₀ w})
        (r C.⊗ₕ C.id {J.F₀ w}) f

  raw-precompose-core :
      {A B Y : C.ob}
      (r : C.Hom[ A , B ]) (w : ΣM.ob)
      (f : C.Hom[ B C.⊗ J.F₀ w , Y ])
    → P.compPCore (w , f) (P.rawRep r) .snd
    ≡ P.compPCore
        (w , (r C.⊗ₕ C.id {J.F₀ w}) C.⋆ f)
        (P.idRepr A) .snd
  raw-precompose-core {A} r w f =
    cong
      (λ q →
        (C.id {A} C.⊗ₕ P.δ⁻¹⟨ ΣM.unit , w ⟩)
          C.⋆ C.α⟨ A , J.F₀ ΣM.unit , J.F₀ w ⟩ C.⋆ q)
      (raw-precompose-inner r w f)

  -- Sharpening found during implementation: the general bridge is the
  -- existing idlStepP after factoring a raw core as idRepr followed by
  -- r.  No copy of the unit diagram chase is needed.
  raw-precompose-step :
      {A B Y : C.ob}
      (r : C.Hom[ A , B ]) (w : ΣM.ob)
      (f : C.Hom[ B C.⊗ J.F₀ w , Y ])
    → P.PStep A Y
        (P.compPCore (w , f) (P.rawRep r))
        (preRep r (w , f))
  raw-precompose-step r w f =
    fst unit-step , raw-precompose-core r w f ∙ snd unit-step
    where
    unit-step =
      P.idlStepP
        (w , (r C.⊗ₕ C.id {J.F₀ w}) C.⋆ f)

  raw-precompose :
      {A B Y : C.ob} (r : C.Hom[ A , B ])
      (q : P.PQuot B Y)
    → P.compPQuot (P.RΣ .Functor.F-hom r) q
    ≡ preQ r q
  raw-precompose r =
    SQ.elimProp
      (λ _ → squash/ _ _)
      (λ (w , f) → eq/ _ _
        (zz-step (raw-precompose-step r w f)))

  ----------------------------------------------------------------------
  -- The categorical binary coproduct universal property
  ----------------------------------------------------------------------

  module CoproductHom (A B Y : C.ob) where
    module CC = CoreCoproduct A B Y

    inj₁P : P.PQuot A (A C.⊕ B)
    inj₁P = P.RΣ .Functor.F-hom (C.ι₁ {x = A} {y = B})

    inj₂P : P.PQuot B (A C.⊕ B)
    inj₂P = P.RΣ .Functor.F-hom (C.ι₂ {x = A} {y = B})

    restrictIso-fun :
        (q : P.PQuot (A C.⊕ B) Y)
      → CC.restrictIso .Iso.fun q
      ≡ ( preQ (C.ι₁ {x = A} {y = B}) q
        , preQ (C.ι₂ {x = A} {y = B}) q )
    restrictIso-fun =
      SQ.elimProp
        (λ _ → isSet× squash/ squash/ _ _)
        (λ _ → refl)

    copairP :
      P.PQuot A Y → P.PQuot B Y → P.PQuot (A C.⊕ B) Y
    copairP f g = CC.restrictIso .Iso.inv (f , g)

    copairP-β₁ :
        (f : P.PQuot A Y) (g : P.PQuot B Y)
      → P.compPQuot inj₁P (copairP f g) ≡ f
    copairP-β₁ f g =
        raw-precompose C.ι₁ (copairP f g)
      ∙ sym (cong fst (restrictIso-fun (copairP f g)))
      ∙ cong fst (CC.restrictIso .Iso.rightInv (f , g))

    copairP-β₂ :
        (f : P.PQuot A Y) (g : P.PQuot B Y)
      → P.compPQuot inj₂P (copairP f g) ≡ g
    copairP-β₂ f g =
        raw-precompose C.ι₂ (copairP f g)
      ∙ sym (cong snd (restrictIso-fun (copairP f g)))
      ∙ cong snd (CC.restrictIso .Iso.rightInv (f , g))

    copairP-η :
        (h : P.PQuot (A C.⊕ B) Y)
      → copairP
          (P.compPQuot inj₁P h)
          (P.compPQuot inj₂P h)
      ≡ h
    copairP-η h =
        cong₂ copairP
          (raw-precompose C.ι₁ h)
          (raw-precompose C.ι₂ h)
      ∙ cong (CC.restrictIso .Iso.inv)
          (sym (restrictIso-fun h))
      ∙ CC.restrictIso .Iso.leftInv h

  polyCoproduct : (A B : C.ob) → BinCoproduct P.PolyCat A B
  polyCoproduct A B .BinCoproduct.binCoprodOb = A C.⊕ B
  polyCoproduct A B .BinCoproduct.binCoprodInj₁ =
    P.RΣ .Functor.F-hom C.ι₁
  polyCoproduct A B .BinCoproduct.binCoprodInj₂ =
    P.RΣ .Functor.F-hom C.ι₂
  polyCoproduct A B .BinCoproduct.univProp {z = Y} f g =
    (CH.copairP f g , CH.copairP-β₁ f g , CH.copairP-β₂ f g) , uniq
    where
    module CH = CoproductHom A B Y

    uniq :
        (t : Σ[ h ∈ P.PQuot (A C.⊕ B) Y ]
          (P.compPQuot CH.inj₁P h ≡ f)
          × (P.compPQuot CH.inj₂P h ≡ g))
      → (CH.copairP f g , CH.copairP-β₁ f g , CH.copairP-β₂ f g)
        ≡ t
    uniq (h , p , q) =
      Σ≡Prop
        (λ _ → isProp×
          (P.PolyCat .Category.isSetHom _ _)
          (P.PolyCat .Category.isSetHom _ _))
        (cong₂ CH.copairP (sym p) (sym q) ∙ CH.copairP-η h)

  polyCoproducts : BinCoproducts P.PolyCat
  polyCoproducts = polyCoproduct

  ----------------------------------------------------------------------
  -- The base initial object remains initial upstairs
  ----------------------------------------------------------------------

  braid-iso : (X Y : C.ob) → isIso C.C C.B⟨ X , Y ⟩
  braid-iso X Y =
    isiso C.B⟨ Y , X ⟩ (C.B-invol Y X) (C.B-invol X Y)

  -- DistSMC fields right annihilation X ⊗ 0.  Braiding transports it
  -- to the left annihilation required by polynomial cores 0 ⊗ j(w).
  leftInitial : (X : C.ob) → isInitial C.C (C.𝟘 C.⊗ X)
  leftInitial X Y .fst =
    C.B⟨ C.𝟘 , X ⟩ C.⋆ (C.annih X Y .fst)
  leftInitial X Y .snd f =
    P.cancel-pre (braid-iso X C.𝟘)
      (isContr→isProp (C.annih X Y)
        (C.B⟨ X , C.𝟘 ⟩
          C.⋆ (C.B⟨ C.𝟘 , X ⟩ C.⋆ (C.annih X Y .fst)))
        (C.B⟨ X , C.𝟘 ⟩ C.⋆ f))

  zeroP : (Y : C.ob) → P.PQuot C.𝟘 Y
  zeroP Y =
    [ ( DI.inhabitant
      , leftInitial (J.F₀ DI.inhabitant) Y .fst ) ]

  boxZero :
      (Y : C.ob) (w : ΣM.ob)
    → C.Hom[ C.𝟘 C.⊗ J.F₀ w , Y ]
    → P.PQuot C.𝟘 Y
  boxZero Y w f = [ (w , f) ]

  zeroP-unique-rep :
      (Y : C.ob) (x : P.Repr C.𝟘 Y)
    → zeroP Y ≡ [ x ]
  zeroP-unique-rep Y (w , f) =
      eq/ _ _ (zz-back (DI.meet-l DI.inhabitant w , refl))
    ∙ cong (boxZero Y c)
        (isContr→isProp (leftInitial (J.F₀ c) Y) zc fc)
    ∙ eq/ _ _ (zz-step (DI.meet-r DI.inhabitant w , refl))
    where
    c = DI.meet DI.inhabitant w
    zc =
      (C.id {C.𝟘} C.⊗ₕ J.F₁ (DI.meet-l DI.inhabitant w))
        C.⋆ (leftInitial (J.F₀ DI.inhabitant) Y .fst)
    fc =
      (C.id {C.𝟘} C.⊗ₕ J.F₁ (DI.meet-r DI.inhabitant w))
        C.⋆ f

  zeroP-unique :
      (Y : C.ob) (q : P.PQuot C.𝟘 Y)
    → zeroP Y ≡ q
  zeroP-unique Y =
    SQ.elimProp
      (λ _ → squash/ _ _)
      (zeroP-unique-rep Y)

  polyInitial : Initial P.PolyCat
  polyInitial .fst = C.𝟘
  polyInitial .snd Y .fst = zeroP Y
  polyInitial .snd Y .snd = zeroP-unique Y

  ----------------------------------------------------------------------
  -- The image of the canonical base distributor
  ----------------------------------------------------------------------

  imageDistributor :
      (A B X : C.ob)
    → CatIso P.PolyCat
        ((A C.⊗ X) C.⊕ (B C.⊗ X))
        ((A C.⊕ B) C.⊗ X)
  imageDistributor A B X =
    P.RΣ .Functor.F-hom d ,
    isiso
      (P.RΣ .Functor.F-hom d⁻¹)
      ( sym (P.RΣ .Functor.F-seq d⁻¹ d)
      ∙ cong (P.RΣ .Functor.F-hom) (dmL-sec A B X)
      ∙ P.RΣ .Functor.F-id )
      ( sym (P.RΣ .Functor.F-seq d d⁻¹)
      ∙ cong (P.RΣ .Functor.F-hom) (dmL-ret A B X)
      ∙ P.RΣ .Functor.F-id )
    where
    d = dmL D A B X
    d⁻¹ = dmL⁻¹ A B X
