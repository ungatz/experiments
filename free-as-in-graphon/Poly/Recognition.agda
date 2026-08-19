{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- C[x : id] is R[C]
--
-- The polynomial category at the cocartesian instance, where the base is
-- bundled with its chosen coproduct as tensor and its chosen initial object as
-- unit, is isomorphic to the cocartesian polynomial category of
-- Poly.Cocartesian.  The hom comparison moves the heap from the right to the
-- left by the coproduct swap, and its inverse swaps back.
--
-- The coherence the instance needs is proved from scratch, since it is stated
-- in the library for a monoidal structure and not for a chosen coproduct: the
-- pentagon and triangle for the coproduct, naturality and involution of the
-- swap, and the hexagon.
--
-- This is an isomorphism of categories.  It proves neither distributivity of
-- the polynomial category under a siftedness hypothesis nor the free
-- distributive completion.
------------------------------------------------------------------------

module Poly.Recognition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/)

open import Poly.Base
open import Poly.Monoidal.Symmetric
open import Poly.Monoidal.Distributive
open import Poly.Kit using (module Kit)
open import Poly.Category
open import Poly.Cocartesian using (module AllocationCompletion)
open import Poly.StrictIso

module Recognition {ℓ ℓ' : Level} (D : DistSMC ℓ ℓ') where

  open DistSMC D
  open Kit D

  ----------------------------------------------------------------------
  -- Right-associated coproduct extensionality
  ----------------------------------------------------------------------

  ⊕-extR3 : {x y z w : ob} (f g : Hom[ x ⊕ (y ⊕ z) , w ])
          → ι₁ ⋆ f ≡ ι₁ ⋆ g
          → ι₁ ⋆ (ι₂ ⋆ f) ≡ ι₁ ⋆ (ι₂ ⋆ g)
          → ι₂ ⋆ (ι₂ ⋆ f) ≡ ι₂ ⋆ (ι₂ ⋆ g)
          → f ≡ g
  ⊕-extR3 f g px py pz =
    ⊕-ext f g px (⊕-ext (ι₂ ⋆ f) (ι₂ ⋆ g) py pz)

  ⊕-extR4 : {v w x y z : ob}
            (f g : Hom[ v ⊕ (w ⊕ (x ⊕ y)) , z ])
          → ι₁ ⋆ f ≡ ι₁ ⋆ g
          → ι₁ ⋆ (ι₂ ⋆ f) ≡ ι₁ ⋆ (ι₂ ⋆ g)
          → ι₁ ⋆ (ι₂ ⋆ (ι₂ ⋆ f)) ≡ ι₁ ⋆ (ι₂ ⋆ (ι₂ ⋆ g))
          → ι₂ ⋆ (ι₂ ⋆ (ι₂ ⋆ f)) ≡ ι₂ ⋆ (ι₂ ⋆ (ι₂ ⋆ g))
          → f ≡ g
  ⊕-extR4 f g pv pw px py =
    ⊕-ext f g pv (⊕-extR3 (ι₂ ⋆ f) (ι₂ ⋆ g) pw px py)

  ----------------------------------------------------------------------
  -- The chosen coproduct as a tensor functor
  ----------------------------------------------------------------------

  CoprodF : Functor (C ×C C) C
  CoprodF .Functor.F-ob (x , y) = x ⊕ y
  CoprodF .Functor.F-hom (f , g) = f ⊕₁ g
  CoprodF .Functor.F-id = ⊕₁-id
  CoprodF .Functor.F-seq (f , g) (f' , g') =
    sym (⊕₁-seq f f' g g')

  CocartTensor : TensorStr C
  CocartTensor .TensorStr.─⊗─ = CoprodF
  CocartTensor .TensorStr.unit = 𝟘

  ----------------------------------------------------------------------
  -- Structural maps and their restrictions
  ----------------------------------------------------------------------

  aLR : {x y z : ob} → Hom[ x ⊕ (y ⊕ z) , (x ⊕ y) ⊕ z ]
  aLR {x} {y} {z} =
    copair
      (ι₁ {x = x} {y = y} ⋆ ι₁ {x = x ⊕ y} {y = z})
      (copair
        (ι₂ {x = x} {y = y} ⋆ ι₁ {x = x ⊕ y} {y = z})
        (ι₂ {x = x ⊕ y} {y = z}))

  swap : {x y : ob} → Hom[ x ⊕ y , y ⊕ x ]
  swap {x} {y} =
    copair (ι₂ {x = y} {y = x}) (ι₁ {x = y} {y = x})

  swap-ι₁ : {x y : ob}
          → ι₁ {x = x} {y = y} ⋆ swap {x} {y}
          ≡ ι₂ {x = y} {y = x}
  swap-ι₁ = β₁ _ _

  swap-ι₂ : {x y : ob}
          → ι₂ {x = x} {y = y} ⋆ swap {x} {y}
          ≡ ι₁ {x = y} {y = x}
  swap-ι₂ = β₂ _ _

  aLR-x : {x y z : ob}
        → ι₁ {x = x} {y = y ⊕ z} ⋆ aLR {x} {y} {z}
        ≡ ι₁ {x = x} {y = y} ⋆ ι₁ {x = x ⊕ y} {y = z}
  aLR-x = β₁ _ _

  aLR-y : {x y z : ob}
        → ι₁ {x = y} {y = z} ⋆
            (ι₂ {x = x} {y = y ⊕ z} ⋆ aLR {x} {y} {z})
        ≡ ι₂ {x = x} {y = y} ⋆ ι₁ {x = x ⊕ y} {y = z}
  aLR-y =
      cong (ι₁ ⋆_) (β₂ _ _)
    ∙ β₁ _ _

  aLR-z : {x y z : ob}
        → ι₂ {x = y} {y = z} ⋆
            (ι₂ {x = x} {y = y ⊕ z} ⋆ aLR {x} {y} {z})
        ≡ ι₂ {x = x ⊕ y} {y = z}
  aLR-z =
      cong (ι₂ ⋆_) (β₂ _ _)
    ∙ β₂ _ _

  swap-post₁ : {x y z : ob} (M : Hom[ y ⊕ x , z ])
             → ι₁ {x = x} {y = y} ⋆ (swap {x} {y} ⋆ M)
             ≡ ι₂ {x = y} {y = x} ⋆ M
  swap-post₁ M =
      sym (⋆Assoc ι₁ swap M)
    ∙ cong (_⋆ M) swap-ι₁

  swap-post₂ : {x y z : ob} (M : Hom[ y ⊕ x , z ])
             → ι₂ {x = x} {y = y} ⋆ (swap {x} {y} ⋆ M)
             ≡ ι₁ {x = y} {y = x} ⋆ M
  swap-post₂ M =
      sym (⋆Assoc ι₂ swap M)
    ∙ cong (_⋆ M) swap-ι₂

  aLR-post-x : {x y z w : ob} (M : Hom[ (x ⊕ y) ⊕ z , w ])
             → ι₁ {x = x} {y = y ⊕ z} ⋆ (aLR ⋆ M)
             ≡ (ι₁ {x = x} {y = y} ⋆ ι₁ {x = x ⊕ y} {y = z}) ⋆ M
  aLR-post-x M =
      sym (⋆Assoc ι₁ aLR M)
    ∙ cong (_⋆ M) aLR-x

  aLR-post-y : {x y z w : ob} (M : Hom[ (x ⊕ y) ⊕ z , w ])
             → ι₁ {x = y} {y = z} ⋆
                 (ι₂ {x = x} {y = y ⊕ z} ⋆ (aLR ⋆ M))
             ≡ (ι₂ {x = x} {y = y} ⋆ ι₁ {x = x ⊕ y} {y = z}) ⋆ M
  aLR-post-y M =
      cong (ι₁ ⋆_) (sym (⋆Assoc ι₂ aLR M))
    ∙ sym (⋆Assoc ι₁ (ι₂ ⋆ aLR) M)
    ∙ cong (_⋆ M) aLR-y

  aLR-post-z : {x y z w : ob} (M : Hom[ (x ⊕ y) ⊕ z , w ])
             → ι₂ {x = y} {y = z} ⋆
                 (ι₂ {x = x} {y = y ⊕ z} ⋆ (aLR ⋆ M))
             ≡ ι₂ {x = x ⊕ y} {y = z} ⋆ M
  aLR-post-z M =
      cong (ι₂ ⋆_) (sym (⋆Assoc ι₂ aLR M))
    ∙ sym (⋆Assoc ι₂ (ι₂ ⋆ aLR) M)
    ∙ cong (_⋆ M) aLR-z

  ----------------------------------------------------------------------
  -- The coproduct associator is a natural isomorphism
  ----------------------------------------------------------------------

  aRL-aLR : {x y z : ob}
          → aRL {x} {y} {z} ⋆ aLR {x} {y} {z} ≡ id
  aRL-aLR {x} {y} {z} = ⊕-ext3 _ _ cX cY cZ
    where
    cX =
        aRL-post-x (aLR {x} {y} {z})
      ∙ aLR-x
      ∙ sym (cong (ι₁ {x = x} {y = y} ⋆_)
          (⋆IdR (ι₁ {x = x ⊕ y} {y = z})))
    cY =
        aRL-post-y (aLR {x} {y} {z})
      ∙ ⋆Assoc
          (ι₁ {x = y} {y = z})
          (ι₂ {x = x} {y = y ⊕ z})
          aLR
      ∙ aLR-y
      ∙ sym (cong (ι₂ {x = x} {y = y} ⋆_)
          (⋆IdR (ι₁ {x = x ⊕ y} {y = z})))
    cZ =
        aRL-post-z (aLR {x} {y} {z})
      ∙ ⋆Assoc
          (ι₂ {x = y} {y = z})
          (ι₂ {x = x} {y = y ⊕ z})
          aLR
      ∙ aLR-z
      ∙ sym (⋆IdR (ι₂ {x = x ⊕ y} {y = z}))

  aLR-aRL : {x y z : ob}
          → aLR {x} {y} {z} ⋆ aRL {x} {y} {z} ≡ id
  aLR-aRL {x} {y} {z} = ⊕-extR3 _ _ cX cY cZ
    where
    cX =
        aLR-post-x (aRL {x} {y} {z})
      ∙ ⋆Assoc
          (ι₁ {x = x} {y = y})
          (ι₁ {x = x ⊕ y} {y = z})
          aRL
      ∙ aRL-x
      ∙ sym (⋆IdR (ι₁ {x = x} {y = y ⊕ z}))
    cY =
        aLR-post-y (aRL {x} {y} {z})
      ∙ ⋆Assoc
          (ι₂ {x = x} {y = y})
          (ι₁ {x = x ⊕ y} {y = z})
          aRL
      ∙ aRL-y
      ∙ sym (cong (ι₁ {x = y} {y = z} ⋆_)
          (⋆IdR (ι₂ {x = x} {y = y ⊕ z})))
    cZ =
        aLR-post-z (aRL {x} {y} {z})
      ∙ aRL-z
      ∙ sym (cong (ι₂ {x = y} {y = z} ⋆_)
          (⋆IdR (ι₂ {x = x} {y = y ⊕ z})))

  aLR-nat : {x x' y y' z z' : ob}
            (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
          → (f ⊕₁ (g ⊕₁ h)) ⋆ aLR {x'} {y'} {z'}
          ≡ aLR {x} {y} {z} ⋆ ((f ⊕₁ g) ⊕₁ h)
  aLR-nat {x} {x'} {y} {y'} {z} {z'} f g h =
    ⊕-extR3 _ _ cX cY cZ
    where
    T = (f ⊕₁ g) ⊕₁ h

    cXL :
      ι₁ {x = x} {y = y ⊕ z} ⋆
        ((f ⊕₁ (g ⊕₁ h)) ⋆ aLR {x'} {y'} {z'})
      ≡ f ⋆
          (ι₁ {x = x'} {y = y'} ⋆
            ι₁ {x = x' ⊕ y'} {y = z'})
    cXL =
        push₁ f (g ⊕₁ h) aLR
      ∙ cong (f ⋆_) aLR-x

    cXR :
      ι₁ {x = x} {y = y ⊕ z} ⋆
        (aLR {x} {y} {z} ⋆ T)
      ≡ f ⋆
          (ι₁ {x = x'} {y = y'} ⋆
            ι₁ {x = x' ⊕ y'} {y = z'})
    cXR =
        aLR-post-x T
      ∙ ⋆Assoc ι₁ ι₁ T
      ∙ cong (ι₁ {x = x} {y = y} ⋆_) (⊕₁-ι₁ (f ⊕₁ g) h)
      ∙ sym (⋆Assoc ι₁ (f ⊕₁ g) ι₁)
      ∙ cong (_⋆ ι₁ {x = x' ⊕ y'} {y = z'}) (⊕₁-ι₁ f g)
      ∙ ⋆Assoc f ι₁ ι₁

    cX = cXL ∙ sym cXR

    cYL :
      ι₁ {x = y} {y = z} ⋆
        (ι₂ {x = x} {y = y ⊕ z} ⋆
          ((f ⊕₁ (g ⊕₁ h)) ⋆ aLR {x'} {y'} {z'}))
      ≡ g ⋆
          (ι₂ {x = x'} {y = y'} ⋆
            ι₁ {x = x' ⊕ y'} {y = z'})
    cYL =
        cong (ι₁ ⋆_) (push₂ f (g ⊕₁ h) aLR)
      ∙ sym (⋆Assoc ι₁ (g ⊕₁ h) (ι₂ ⋆ aLR))
      ∙ cong (_⋆ (ι₂ ⋆ aLR)) (⊕₁-ι₁ g h)
      ∙ ⋆Assoc g ι₁ (ι₂ ⋆ aLR)
      ∙ cong (g ⋆_) aLR-y

    cYR :
      ι₁ {x = y} {y = z} ⋆
        (ι₂ {x = x} {y = y ⊕ z} ⋆
          (aLR {x} {y} {z} ⋆ T))
      ≡ g ⋆
          (ι₂ {x = x'} {y = y'} ⋆
            ι₁ {x = x' ⊕ y'} {y = z'})
    cYR =
        aLR-post-y T
      ∙ ⋆Assoc ι₂ ι₁ T
      ∙ cong (ι₂ {x = x} {y = y} ⋆_) (⊕₁-ι₁ (f ⊕₁ g) h)
      ∙ sym (⋆Assoc ι₂ (f ⊕₁ g) ι₁)
      ∙ cong (_⋆ ι₁ {x = x' ⊕ y'} {y = z'}) (⊕₁-ι₂ f g)
      ∙ ⋆Assoc g ι₂ ι₁

    cY = cYL ∙ sym cYR

    cZL :
      ι₂ {x = y} {y = z} ⋆
        (ι₂ {x = x} {y = y ⊕ z} ⋆
          ((f ⊕₁ (g ⊕₁ h)) ⋆ aLR {x'} {y'} {z'}))
      ≡ h ⋆ ι₂ {x = x' ⊕ y'} {y = z'}
    cZL =
        cong (ι₂ ⋆_) (push₂ f (g ⊕₁ h) aLR)
      ∙ sym (⋆Assoc ι₂ (g ⊕₁ h) (ι₂ ⋆ aLR))
      ∙ cong (_⋆ (ι₂ ⋆ aLR)) (⊕₁-ι₂ g h)
      ∙ ⋆Assoc h ι₂ (ι₂ ⋆ aLR)
      ∙ cong (h ⋆_) aLR-z

    cZR :
      ι₂ {x = y} {y = z} ⋆
        (ι₂ {x = x} {y = y ⊕ z} ⋆
          (aLR {x} {y} {z} ⋆ T))
      ≡ h ⋆ ι₂ {x = x' ⊕ y'} {y = z'}
    cZR =
        aLR-post-z T
      ∙ ⊕₁-ι₂ (f ⊕₁ g) h

    cZ = cZL ∙ sym cZR

  ----------------------------------------------------------------------
  -- Coproduct unitors
  ----------------------------------------------------------------------

  lu-sec : {x : ob} → (ι₂ {x = 𝟘} {y = x} ⋆ lu {x}) ≡ id
  lu-sec = β₂ !→ id

  lu-ret : {x : ob} → lu {x} ⋆ ι₂ {x = 𝟘} {y = x} ≡ id
  lu-ret {x} = ⊕-ext _ _ c0 cX
    where
    c0 = init⊘ _ _
    cX =
        sym (⋆Assoc ι₂ lu ι₂)
      ∙ cong (_⋆ ι₂) (β₂ !→ id)
      ∙ ⋆IdL ι₂
      ∙ sym (⋆IdR ι₂)

  lu-nat : {x y : ob} (f : Hom[ x , y ])
         → (id {𝟘} ⊕₁ f) ⋆ lu {y} ≡ lu {x} ⋆ f
  lu-nat f = ⊕-ext _ _ (init⊘ _ _) cX
    where
    cX =
        push₂ (id {𝟘}) f lu
      ∙ cong (f ⋆_) (β₂ !→ id)
      ∙ ⋆IdR f
      ∙ sym (cp₂ !→ id f ∙ ⋆IdL f)

  ru-sec : {x : ob} → (ι₁ {x = x} {y = 𝟘} ⋆ ru {x}) ≡ id
  ru-sec = β₁ id !→

  ru-ret : {x : ob} → ru {x} ⋆ ι₁ {x = x} {y = 𝟘} ≡ id
  ru-ret {x} = ⊕-ext _ _ cX c0
    where
    cX =
        sym (⋆Assoc ι₁ ru ι₁)
      ∙ cong (_⋆ ι₁) (β₁ id !→)
      ∙ ⋆IdL ι₁
      ∙ sym (⋆IdR ι₁)
    c0 = init⊘ _ _

  ru-nat : {x y : ob} (f : Hom[ x , y ])
         → (f ⊕₁ id {𝟘}) ⋆ ru {y} ≡ ru {x} ⋆ f
  ru-nat f = ⊕-ext _ _ cX (init⊘ _ _)
    where
    cX =
        push₁ f (id {𝟘}) ru
      ∙ cong (f ⋆_) (β₁ id !→)
      ∙ ⋆IdR f
      ∙ sym (cp₁ id !→ f ∙ ⋆IdL f)

  ----------------------------------------------------------------------
  -- Cocartesian pentagon and triangle
  ----------------------------------------------------------------------

  pentagon⊕LR : (w x y z : ob)
      → (id {w} ⊕₁ aLR {x} {y} {z})
          ⋆ (aLR {w} {x ⊕ y} {z}
          ⋆ (aLR {w} {x} {y} ⊕₁ id {z}))
      ≡ aLR {w} {x} {y ⊕ z}
          ⋆ aLR {w ⊕ x} {y} {z}
  pentagon⊕LR w x y z = ⊕-extR4 L R
    (lW ∙ sym rW) (lX ∙ sym rX) (lY ∙ sym rY) (lZ ∙ sym rZ)
    where
    Axyz = aLR {x} {y} {z}
    AwXYz = aLR {w} {x ⊕ y} {z}
    Awxy = aLR {w} {x} {y}
    AwxYZ = aLR {w} {x} {y ⊕ z}
    AWxyz = aLR {w ⊕ x} {y} {z}

    L0 = id {w} ⊕₁ Axyz
    L1 = AwXYz
    L2 = Awxy ⊕₁ id {z}
    L = L0 ⋆ (L1 ⋆ L2)
    R = AwxYZ ⋆ AWxyz

    jW : Hom[ w , ((w ⊕ x) ⊕ y) ⊕ z ]
    jW = ι₁ ⋆ (ι₁ ⋆ ι₁)
    jX : Hom[ x , ((w ⊕ x) ⊕ y) ⊕ z ]
    jX = ι₂ ⋆ (ι₁ ⋆ ι₁)
    jY : Hom[ y , ((w ⊕ x) ⊕ y) ⊕ z ]
    jY = ι₂ ⋆ ι₁
    jZ : Hom[ z , ((w ⊕ x) ⊕ y) ⊕ z ]
    jZ = ι₂

    lW : ι₁ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ L ≡ jW
    lW =
        push₁ (id {w}) Axyz (L1 ⋆ L2)
      ∙ ⋆IdL _
      ∙ aLR-post-x L2
      ∙ ⋆Assoc ι₁ ι₁ L2
      ∙ cong (ι₁ {x = w} {y = x ⊕ y} ⋆_) (⊕₁-ι₁ Awxy (id {z}))
      ∙ aLR-post-x ι₁
      ∙ ⋆Assoc ι₁ ι₁ ι₁

    rW : ι₁ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ R ≡ jW
    rW =
        aLR-post-x AWxyz
      ∙ ⋆Assoc ι₁ ι₁ AWxyz
      ∙ cong (ι₁ {x = w} {y = x} ⋆_) aLR-x

    lX : ι₁ {x = x} {y = y ⊕ z} ⋆
            (ι₂ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ L)
          ≡ jX
    lX =
        cong (ι₁ {x = x} {y = y ⊕ z} ⋆_)
          (push₂ (id {w}) Axyz (L1 ⋆ L2))
      ∙ aLR-post-x (ι₂ ⋆ (L1 ⋆ L2))
      ∙ ⋆Assoc (ι₁ {x = x} {y = y}) ι₁ (ι₂ ⋆ (L1 ⋆ L2))
      ∙ cong (ι₁ {x = x} {y = y} ⋆_) (aLR-post-y L2)
      ∙ sym (⋆Assoc ι₁ (ι₂ ⋆ ι₁) L2)
      ∙ cong (_⋆ L2) (sym (⋆Assoc ι₁ ι₂ ι₁))
      ∙ ⋆Assoc (ι₁ ⋆ ι₂) ι₁ L2
      ∙ cong ((ι₁ {x = x} {y = y} ⋆ ι₂ {x = w} {y = x ⊕ y}) ⋆_)
          (⊕₁-ι₁ Awxy (id {z}))
      ∙ ⋆Assoc (ι₁ {x = x} {y = y}) ι₂ (Awxy ⋆ ι₁)
      ∙ aLR-post-y ι₁
      ∙ ⋆Assoc ι₂ ι₁ ι₁

    rX : ι₁ {x = x} {y = y ⊕ z} ⋆
            (ι₂ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ R)
          ≡ jX
    rX =
        aLR-post-y AWxyz
      ∙ ⋆Assoc ι₂ ι₁ AWxyz
      ∙ cong (ι₂ {x = w} {y = x} ⋆_) aLR-x

    lY : ι₁ {x = y} {y = z} ⋆
            (ι₂ {x = x} {y = y ⊕ z} ⋆
              (ι₂ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ L))
          ≡ jY
    lY =
        cong (ι₁ {x = y} {y = z} ⋆_)
          (cong (ι₂ {x = x} {y = y ⊕ z} ⋆_)
            (push₂ (id {w}) Axyz (L1 ⋆ L2)))
      ∙ aLR-post-y (ι₂ ⋆ (L1 ⋆ L2))
      ∙ ⋆Assoc ι₂ ι₁ (ι₂ ⋆ (L1 ⋆ L2))
      ∙ cong (ι₂ {x = x} {y = y} ⋆_) (aLR-post-y L2)
      ∙ sym (⋆Assoc ι₂ (ι₂ ⋆ ι₁) L2)
      ∙ cong (_⋆ L2) (sym (⋆Assoc ι₂ ι₂ ι₁))
      ∙ ⋆Assoc (ι₂ ⋆ ι₂) ι₁ L2
      ∙ cong ((ι₂ {x = x} {y = y} ⋆ ι₂ {x = w} {y = x ⊕ y}) ⋆_)
          (⊕₁-ι₁ Awxy (id {z}))
      ∙ ⋆Assoc ι₂ ι₂ (Awxy ⋆ ι₁)
      ∙ aLR-post-z ι₁

    rY : ι₁ {x = y} {y = z} ⋆
            (ι₂ {x = x} {y = y ⊕ z} ⋆
              (ι₂ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ R))
          ≡ jY
    rY =
        cong (ι₁ {x = y} {y = z} ⋆_) (aLR-post-z AWxyz)
      ∙ aLR-y

    lZ : ι₂ {x = y} {y = z} ⋆
            (ι₂ {x = x} {y = y ⊕ z} ⋆
              (ι₂ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ L))
          ≡ jZ
    lZ =
        cong (ι₂ {x = y} {y = z} ⋆_)
          (cong (ι₂ {x = x} {y = y ⊕ z} ⋆_)
            (push₂ (id {w}) Axyz (L1 ⋆ L2)))
      ∙ aLR-post-z (ι₂ ⋆ (L1 ⋆ L2))
      ∙ aLR-post-z L2
      ∙ ⊕₁-ι₂ Awxy (id {z})
      ∙ ⋆IdL ι₂

    rZ : ι₂ {x = y} {y = z} ⋆
            (ι₂ {x = x} {y = y ⊕ z} ⋆
              (ι₂ {x = w} {y = x ⊕ (y ⊕ z)} ⋆ R))
          ≡ jZ
    rZ =
        cong (ι₂ {x = y} {y = z} ⋆_) (aLR-post-z AWxyz)
      ∙ aLR-z

  triangle⊕ : (x y : ob)
      → aLR {x} {𝟘} {y} ⋆ (ru {x} ⊕₁ id {y})
      ≡ id {x} ⊕₁ lu {y}
  triangle⊕ x y = ⊕-extR3 L R
    (lX ∙ sym rX) (init⊘ _ _) (lY ∙ sym rY)
    where
    L = aLR {x} {𝟘} {y} ⋆ (ru {x} ⊕₁ id {y})
    R = id {x} ⊕₁ lu {y}

    lX : ι₁ {x = x} {y = 𝟘 ⊕ y} ⋆ L
       ≡ ι₁ {x = x} {y = y}
    lX =
        aLR-post-x (ru ⊕₁ id)
      ∙ ⋆Assoc ι₁ ι₁ (ru ⊕₁ id)
      ∙ cong (ι₁ {x = x} {y = 𝟘} ⋆_) (⊕₁-ι₁ ru (id {y}))
      ∙ sym (⋆Assoc ι₁ ru ι₁)
      ∙ cong (_⋆ ι₁ {x = x} {y = y}) ru-sec
      ∙ ⋆IdL ι₁

    rX : ι₁ {x = x} {y = 𝟘 ⊕ y} ⋆ R
       ≡ ι₁ {x = x} {y = y}
    rX = ⊕₁-ι₁ (id {x}) lu ∙ ⋆IdL ι₁

    lY : ι₂ {x = 𝟘} {y = y} ⋆
            (ι₂ {x = x} {y = 𝟘 ⊕ y} ⋆ L)
       ≡ ι₂ {x = x} {y = y}
    lY =
        aLR-post-z (ru ⊕₁ id)
      ∙ ⊕₁-ι₂ ru (id {y})
      ∙ ⋆IdL ι₂

    rY : ι₂ {x = 𝟘} {y = y} ⋆
            (ι₂ {x = x} {y = 𝟘 ⊕ y} ⋆ R)
       ≡ ι₂ {x = x} {y = y}
    rY =
        cong (ι₂ {x = 𝟘} {y = y} ⋆_) (⊕₁-ι₂ (id {x}) lu)
      ∙ sym (⋆Assoc ι₂ lu ι₂)
      ∙ cong (_⋆ ι₂ {x = x} {y = y}) lu-sec
      ∙ ⋆IdL ι₂

  CocartM : MonoidalStr C
  CocartM .MonoidalStr.tenstr = CocartTensor
  CocartM .MonoidalStr.α .NatIso.trans .NatTrans.N-ob (x , y , z) =
    aLR {x} {y} {z}
  CocartM .MonoidalStr.α .NatIso.trans .NatTrans.N-hom (f , g , h) =
    aLR-nat f g h
  CocartM .MonoidalStr.α .NatIso.nIso (x , y , z) =
    isiso aRL aRL-aLR aLR-aRL
  CocartM .MonoidalStr.η .NatIso.trans .NatTrans.N-ob x = lu
  CocartM .MonoidalStr.η .NatIso.trans .NatTrans.N-hom f = lu-nat f
  CocartM .MonoidalStr.η .NatIso.nIso x =
    isiso ι₂ lu-sec lu-ret
  CocartM .MonoidalStr.ρ .NatIso.trans .NatTrans.N-ob x = ru
  CocartM .MonoidalStr.ρ .NatIso.trans .NatTrans.N-hom f = ru-nat f
  CocartM .MonoidalStr.ρ .NatIso.nIso x =
    isiso ι₁ ru-sec ru-ret
  CocartM .MonoidalStr.pentagon = pentagon⊕LR
  CocartM .MonoidalStr.triangle = triangle⊕

  ----------------------------------------------------------------------
  -- Cocartesian symmetry
  ----------------------------------------------------------------------

  swap-nat : {x x' y y' : ob}
             (f : Hom[ x , x' ]) (g : Hom[ y , y' ])
           → (f ⊕₁ g) ⋆ swap {x'} {y'}
           ≡ swap {x} {y} ⋆ (g ⊕₁ f)
  swap-nat f g = ⊕-ext _ _ (lX ∙ sym rX) (lY ∙ sym rY)
    where
    lX =
        push₁ f g swap
      ∙ cong (f ⋆_) swap-ι₁
    rX =
        swap-post₁ (g ⊕₁ f)
      ∙ ⊕₁-ι₂ g f
    lY =
        push₂ f g swap
      ∙ cong (g ⋆_) swap-ι₂
    rY =
        swap-post₂ (g ⊕₁ f)
      ∙ ⊕₁-ι₁ g f

  swap-invol : (x y : ob)
             → swap {x} {y} ⋆ swap {y} {x} ≡ id
  swap-invol x y = ⊕-ext _ _ cX cY
    where
    cX =
        swap-post₁ swap
      ∙ swap-ι₂
      ∙ sym (⋆IdR (ι₁ {x = x} {y = y}))
    cY =
        swap-post₂ swap
      ∙ swap-ι₁
      ∙ sym (⋆IdR (ι₂ {x = x} {y = y}))

  hexagon⊕ : (x y z : ob)
      → aRL {x} {y} {z}
          ⋆ (swap {x} {y ⊕ z} ⋆ aRL {y} {z} {x})
      ≡ (swap {x} {y} ⊕₁ id {z})
          ⋆ (aRL {y} {x} {z} ⋆ (id {y} ⊕₁ swap {x} {z}))
  hexagon⊕ x y z = ⊕-ext3 L R
    (lX ∙ sym rX) (lY ∙ sym rY) (lZ ∙ sym rZ)
    where
    Axyz = aRL {x} {y} {z}
    Ayzx = aRL {y} {z} {x}
    Ayxz = aRL {y} {x} {z}
    Sxyz = swap {x} {y ⊕ z}
    Sxy = swap {x} {y}
    Sxz = swap {x} {z}
    R0 = Sxy ⊕₁ id {z}
    R2 = id {y} ⊕₁ Sxz
    L = Axyz ⋆ (Sxyz ⋆ Ayzx)
    R = R0 ⋆ (Ayxz ⋆ R2)

    jX : Hom[ x , y ⊕ (z ⊕ x) ]
    jX = ι₂ ⋆ ι₂
    jY : Hom[ y , y ⊕ (z ⊕ x) ]
    jY = ι₁
    jZ : Hom[ z , y ⊕ (z ⊕ x) ]
    jZ = ι₁ ⋆ ι₂

    lX : ι₁ {x = x} {y = y} ⋆
            (ι₁ {x = x ⊕ y} {y = z} ⋆ L)
       ≡ jX
    lX =
        aRL-post-x (Sxyz ⋆ Ayzx)
      ∙ swap-post₁ Ayzx
      ∙ aRL-z

    rX : ι₁ {x = x} {y = y} ⋆
            (ι₁ {x = x ⊕ y} {y = z} ⋆ R)
       ≡ jX
    rX =
        cong (ι₁ {x = x} {y = y} ⋆_)
          (push₁ Sxy (id {z}) (Ayxz ⋆ R2))
      ∙ swap-post₁ (ι₁ ⋆ (Ayxz ⋆ R2))
      ∙ aRL-post-y R2
      ∙ ⋆Assoc ι₁ ι₂ R2
      ∙ cong (ι₁ {x = x} {y = z} ⋆_) (⊕₁-ι₂ (id {y}) Sxz)
      ∙ swap-post₁ ι₂

    lY : ι₂ {x = x} {y = y} ⋆
            (ι₁ {x = x ⊕ y} {y = z} ⋆ L)
       ≡ jY
    lY =
        aRL-post-y (Sxyz ⋆ Ayzx)
      ∙ ⋆Assoc ι₁ ι₂ (Sxyz ⋆ Ayzx)
      ∙ cong (ι₁ {x = y} {y = z} ⋆_) (swap-post₂ Ayzx)
      ∙ aRL-x

    rY : ι₂ {x = x} {y = y} ⋆
            (ι₁ {x = x ⊕ y} {y = z} ⋆ R)
       ≡ jY
    rY =
        cong (ι₂ {x = x} {y = y} ⋆_)
          (push₁ Sxy (id {z}) (Ayxz ⋆ R2))
      ∙ swap-post₂ (ι₁ ⋆ (Ayxz ⋆ R2))
      ∙ aRL-post-x R2
      ∙ ⊕₁-ι₁ (id {y}) Sxz
      ∙ ⋆IdL ι₁

    lZ : ι₂ {x = x ⊕ y} {y = z} ⋆ L ≡ jZ
    lZ =
        aRL-post-z (Sxyz ⋆ Ayzx)
      ∙ ⋆Assoc ι₂ ι₂ (Sxyz ⋆ Ayzx)
      ∙ cong (ι₂ {x = y} {y = z} ⋆_) (swap-post₂ Ayzx)
      ∙ aRL-y

    rZ : ι₂ {x = x ⊕ y} {y = z} ⋆ R ≡ jZ
    rZ =
        push₂ Sxy (id {z}) (Ayxz ⋆ R2)
      ∙ ⋆IdL _
      ∙ aRL-post-z R2
      ∙ ⋆Assoc ι₂ ι₂ R2
      ∙ cong (ι₂ {x = x} {y = z} ⋆_) (⊕₁-ι₂ (id {y}) Sxz)
      ∙ swap-post₂ ι₂

  CocartS : SymmetricStr C CocartM
  CocartS .SymmetricStr.B⟨_,_⟩ x y = swap {x} {y}
  CocartS .SymmetricStr.B-nat = swap-nat
  CocartS .SymmetricStr.B-invol = swap-invol
  CocartS .SymmetricStr.hexagon = hexagon⊕

  CocartSMC : SymmMonCategory ℓ ℓ'
  CocartSMC .SymmMonCategory.C = C
  CocartSMC .SymmMonCategory.M = CocartM
  CocartSMC .SymmMonCategory.S = CocartS

  ----------------------------------------------------------------------
  -- The identity strong monoidal functor on the cocartesian bundle
  ----------------------------------------------------------------------

  IdCocart : StrongMonoFunctor CocartSMC CocartSMC
  IdCocart .StrongMonoFunctor.F₀ x = x
  IdCocart .StrongMonoFunctor.F₁ f = f
  IdCocart .StrongMonoFunctor.F-id = refl
  IdCocart .StrongMonoFunctor.F-seq f g = refl
  IdCocart .StrongMonoFunctor.δ⟨_,_⟩ u v = id {u ⊕ v}
  IdCocart .StrongMonoFunctor.δ-iso u v = idCatIso .snd
  IdCocart .StrongMonoFunctor.γ = id {𝟘}
  IdCocart .StrongMonoFunctor.γ-iso = idCatIso .snd
  IdCocart .StrongMonoFunctor.δ-nat p q =
    ⋆IdR (p ⊕₁ q) ∙ sym (⋆IdL (p ⊕₁ q))
  IdCocart .StrongMonoFunctor.δ-assoc u v w =
      cong (aRL {u} {v} {w} ⋆_) (
          cong (_⋆ id {u ⊕ (v ⊕ w)}) (⊕₁-id {u} {v ⊕ w})
        ∙ ⋆IdL (id {u ⊕ (v ⊕ w)}))
    ∙ ⋆IdR (aRL {u} {v} {w})
    ∙ sym (
        cong (λ t → t ⋆ (id {((u ⊕ v) ⊕ w)} ⋆ aRL {u} {v} {w}))
          (⊕₁-id {u ⊕ v} {w})
      ∙ ⋆IdL (id {((u ⊕ v) ⊕ w)} ⋆ aRL {u} {v} {w})
      ∙ ⋆IdL (aRL {u} {v} {w}))
  IdCocart .StrongMonoFunctor.γ-left v =
      cong (λ t → t ⋆ (id {𝟘 ⊕ v} ⋆ lu {v})) (⊕₁-id {𝟘} {v})
    ∙ ⋆IdL (id {𝟘 ⊕ v} ⋆ lu {v})
    ∙ ⋆IdL (lu {v})
  IdCocart .StrongMonoFunctor.γ-right v =
      cong (λ t → t ⋆ (id {v ⊕ 𝟘} ⋆ ru {v})) (⊕₁-id {v} {𝟘})
    ∙ ⋆IdL (id {v ⊕ 𝟘} ⋆ ru {v})
    ∙ ⋆IdL (ru {v})

  module P = PolyOver CocartSMC CocartSMC IdCocart
  module R = AllocationCompletion D

  ----------------------------------------------------------------------
  -- Move the heap across the visible object by coproduct symmetry
  ----------------------------------------------------------------------

  toBnd : {A B : ob} → P.Repr A B → R.RBnd A B
  toBnd {A} (H , f) = H , swap {H} {A} ⋆ f

  fromBnd : {A B : ob} → R.RBnd A B → P.Repr A B
  fromBnd {A} (H , f) = H , swap {A} {H} ⋆ f

  toStep : {A B : ob} {x y : P.Repr A B}
         → P.PStep A B x y → R.RStep A B (toBnd x) (toBnd y)
  toStep {A} {x = H , f} {y = H' , f'} (h , e) = h , eq
    where
    eq : swap {H} {A} ⋆ f
       ≡ (h ⊕₁ id {A}) ⋆ (swap {H'} {A} ⋆ f')
    eq =
        cong (swap {H} {A} ⋆_) e
      ∙ sym (⋆Assoc swap (id {A} ⊕₁ h) f')
      ∙ cong (_⋆ f') (sym (swap-nat h (id {A})))
      ∙ ⋆Assoc (h ⊕₁ id {A}) swap f'

  fromStep : {A B : ob} {x y : R.RBnd A B}
           → R.RStep A B x y → P.PStep A B (fromBnd x) (fromBnd y)
  fromStep {A} {x = H , f} {y = H' , f'} (h , e) = h , eq
    where
    eq : swap {A} {H} ⋆ f
       ≡ (id {A} ⊕₁ h) ⋆ (swap {A} {H'} ⋆ f')
    eq =
        cong (swap {A} {H} ⋆_) e
      ∙ sym (⋆Assoc swap (h ⊕₁ id {A}) f')
      ∙ cong (_⋆ f') (sym (swap-nat (id {A}) h))
      ∙ ⋆Assoc (id {A} ⊕₁ h) swap f'

  toHom : (A B : ob) → P.PQuot A B → R.RQuot A B
  toHom A B = SQ.rec squash/ (λ x → [ toBnd x ])
    (λ x y zz → eq/ _ _
      (mapFence toBnd (λ {a} {b} st → toStep {x = a} {y = b} st) zz))

  fromHom : (A B : ob) → R.RQuot A B → P.PQuot A B
  fromHom A B = SQ.rec squash/ (λ x → [ fromBnd x ])
    (λ x y zz → eq/ _ _
      (mapFence fromBnd
        (λ {a} {b} st → fromStep {x = a} {y = b} st) zz))

  from-to : (A B : ob) (f : P.PQuot A B)
          → fromHom A B (toHom A B f) ≡ f
  from-to A B = SQ.elimProp (λ _ → squash/ _ _) go
    where
    go : (x : P.Repr A B) → fromHom A B (toHom A B [ x ]) ≡ [ x ]
    go (H , f) = cong [_] (cong (H ,_) core)
      where
      core : swap {A} {H} ⋆ (swap {H} {A} ⋆ f) ≡ f
      core =
          sym (⋆Assoc swap swap f)
        ∙ cong (_⋆ f) (swap-invol A H)
        ∙ ⋆IdL f

  to-from : (A B : ob) (f : R.RQuot A B)
          → toHom A B (fromHom A B f) ≡ f
  to-from A B = SQ.elimProp (λ _ → squash/ _ _) go
    where
    go : (x : R.RBnd A B) → toHom A B (fromHom A B [ x ]) ≡ [ x ]
    go (H , f) = cong [_] (cong (H ,_) core)
      where
      core : swap {H} {A} ⋆ (swap {A} {H} ⋆ f) ≡ f
      core =
          sym (⋆Assoc swap swap f)
        ∙ cong (_⋆ f) (swap-invol H A)
        ∙ ⋆IdL f

  homIsoAt : (A B : ob) → Iso (P.PQuot A B) (R.RQuot A B)
  homIsoAt A B =
    iso (toHom A B) (fromHom A B) (to-from A B) (from-to A B)

  ----------------------------------------------------------------------
  -- Forward functoriality: identity
  ----------------------------------------------------------------------

  swap-unit : (A : ob) → swap {𝟘} {A} ⋆ ru {A} ≡ lu {A}
  swap-unit A = ⊕-ext _ _ (init⊘ _ _) cA
    where
    cA =
        swap-post₂ (ru {A})
      ∙ ru-sec
      ∙ sym lu-sec

  to-id : (A : ob)
        → toHom A A [ P.idRepr A ] ≡ [ R.idRBnd A ]
  to-id A = cong [_] (cong (𝟘 ,_) core)
    where
    core :
      swap {𝟘} {A} ⋆
        ((id {A} ⊕₁ id {𝟘}) ⋆ ru {A})
      ≡ lu {A}
    core =
        cong (swap {𝟘} {A} ⋆_) (
            cong (_⋆ ru {A}) (⊕₁-id {A} {𝟘})
          ∙ ⋆IdL (ru {A}))
      ∙ swap-unit A

  ----------------------------------------------------------------------
  -- Forward functoriality: composition
  --
  -- The converted polynomial composite has heap H ⊕ K, while R[-]
  -- accumulates K ⊕ H.  One RStep with mediator swap{H}{K} bridges
  -- them; its core equation is the three-leaf H/K/A chase below.
  ----------------------------------------------------------------------

  to-seqCore : (A B Cc : ob)
               (x : P.Repr A B) (y : P.Repr B Cc)
             → toHom A Cc [ P.compPCore y x ]
             ≡ R.compRQuot (toHom A B [ x ]) (toHom B Cc [ y ])
  to-seqCore A B Cc (H , f) (K , g) =
      cong [_] (cong (H ⊕ K ,_) simplify)
    ∙ eq/ ((H ⊕ K) , W) ((K ⊕ H) , N)
        (zz-step (σ , sqEq))
    where
    T : Hom[ (A ⊕ H) ⊕ K , Cc ]
    T = (f ⊕₁ id {K}) ⋆ g

    W : Hom[ (H ⊕ K) ⊕ A , Cc ]
    W = swap {H ⊕ K} {A} ⋆ (aLR {A} {H} {K} ⋆ T)

    φf : Hom[ H ⊕ A , B ]
    φf = swap {H} {A} ⋆ f

    φg : Hom[ K ⊕ B , Cc ]
    φg = swap {K} {B} ⋆ g

    mm : Hom[ K ⊕ (H ⊕ A) , Cc ]
    mm = (id {K} ⊕₁ φf) ⋆ φg

    N : Hom[ (K ⊕ H) ⊕ A , Cc ]
    N = aRL {K} {H} {A} ⋆ mm

    σ : Hom[ H ⊕ K , K ⊕ H ]
    σ = swap {H} {K}

    simplify :
      swap {H ⊕ K} {A} ⋆
        ((id {A} ⊕₁ id {H ⊕ K}) ⋆
          (aLR {A} {H} {K} ⋆ T))
      ≡ W
    simplify =
      cong (swap {H ⊕ K} {A} ⋆_) (
          cong (_⋆ (aLR {A} {H} {K} ⋆ T))
            (⊕₁-id {A} {H ⊕ K})
        ∙ ⋆IdL (aLR {A} {H} {K} ⋆ T))

    eH : Hom[ H , Cc ]
    eH =
      ι₂ {x = A} {y = H} ⋆
        (f ⋆ (ι₁ {x = B} {y = K} ⋆ g))

    eK : Hom[ K , Cc ]
    eK = ι₂ {x = B} {y = K} ⋆ g

    eA : Hom[ A , Cc ]
    eA =
      ι₁ {x = A} {y = H} ⋆
        (f ⋆ (ι₁ {x = B} {y = K} ⋆ g))

    lH :
      ι₁ {x = H} {y = K} ⋆
        (ι₁ {x = H ⊕ K} {y = A} ⋆ W)
      ≡ eH
    lH =
        cong (ι₁ {x = H} {y = K} ⋆_)
          (swap-post₁ (aLR {A} {H} {K} ⋆ T))
      ∙ aLR-post-y T
      ∙ ⋆Assoc ι₂ ι₁ T
      ∙ cong (ι₂ {x = A} {y = H} ⋆_)
          (push₁ f (id {K}) g)

    lK :
      ι₂ {x = H} {y = K} ⋆
        (ι₁ {x = H ⊕ K} {y = A} ⋆ W)
      ≡ eK
    lK =
        cong (ι₂ {x = H} {y = K} ⋆_)
          (swap-post₁ (aLR {A} {H} {K} ⋆ T))
      ∙ aLR-post-z T
      ∙ push₂ f (id {K}) g
      ∙ ⋆IdL (ι₂ {x = B} {y = K} ⋆ g)

    lA :
      ι₂ {x = H ⊕ K} {y = A} ⋆ W
      ≡ eA
    lA =
        swap-post₂ (aLR {A} {H} {K} ⋆ T)
      ∙ aLR-post-x T
      ∙ ⋆Assoc ι₁ ι₁ T
      ∙ cong (ι₁ {x = A} {y = H} ⋆_)
          (push₁ f (id {K}) g)

    rH :
      ι₁ {x = H} {y = K} ⋆
        (ι₁ {x = H ⊕ K} {y = A} ⋆
          ((σ ⊕₁ id {A}) ⋆ N))
      ≡ eH
    rH =
        cong (ι₁ {x = H} {y = K} ⋆_)
          (push₁ σ (id {A}) N)
      ∙ swap-post₁ (ι₁ {x = K ⊕ H} {y = A} ⋆ N)
      ∙ aRL-post-y mm
      ∙ ⋆Assoc ι₁ ι₂ mm
      ∙ cong (ι₁ {x = H} {y = A} ⋆_)
          (push₂ (id {K}) φf φg)
      ∙ sym (⋆Assoc ι₁ φf (ι₂ ⋆ φg))
      ∙ cong (_⋆ (ι₂ {x = K} {y = B} ⋆ φg))
          (swap-post₁ f)
      ∙ ⋆Assoc ι₂ f (ι₂ ⋆ φg)
      ∙ cong (λ t → ι₂ {x = A} {y = H} ⋆ (f ⋆ t))
          (swap-post₂ g)

    rK :
      ι₂ {x = H} {y = K} ⋆
        (ι₁ {x = H ⊕ K} {y = A} ⋆
          ((σ ⊕₁ id {A}) ⋆ N))
      ≡ eK
    rK =
        cong (ι₂ {x = H} {y = K} ⋆_)
          (push₁ σ (id {A}) N)
      ∙ swap-post₂ (ι₁ {x = K ⊕ H} {y = A} ⋆ N)
      ∙ aRL-post-x mm
      ∙ push₁ (id {K}) φf φg
      ∙ ⋆IdL (ι₁ {x = K} {y = B} ⋆ φg)
      ∙ swap-post₁ g

    rA :
      ι₂ {x = H ⊕ K} {y = A} ⋆
        ((σ ⊕₁ id {A}) ⋆ N)
      ≡ eA
    rA =
        push₂ σ (id {A}) N
      ∙ ⋆IdL (ι₂ {x = K ⊕ H} {y = A} ⋆ N)
      ∙ aRL-post-z mm
      ∙ ⋆Assoc ι₂ ι₂ mm
      ∙ cong (ι₂ {x = H} {y = A} ⋆_)
          (push₂ (id {K}) φf φg)
      ∙ sym (⋆Assoc ι₂ φf (ι₂ ⋆ φg))
      ∙ cong (_⋆ (ι₂ {x = K} {y = B} ⋆ φg))
          (swap-post₂ f)
      ∙ ⋆Assoc ι₁ f (ι₂ ⋆ φg)
      ∙ cong (λ t → ι₁ {x = A} {y = H} ⋆ (f ⋆ t))
          (swap-post₂ g)

    sqEq : W ≡ (σ ⊕₁ id {A}) ⋆ N
    sqEq = ⊕-ext3 _ _
      (lH ∙ sym rH) (lK ∙ sym rK) (lA ∙ sym rA)

  to-seq : (A B Cc : ob)
           (f : P.PQuot A B) (g : P.PQuot B Cc)
         → toHom A Cc (P.compPQuot f g)
         ≡ R.compRQuot (toHom A B f) (toHom B Cc g)
  to-seq A B Cc =
    SQ.elimProp2 (λ _ _ → squash/ _ _) (to-seqCore A B Cc)

  ----------------------------------------------------------------------
  -- The recognition is an identity-on-objects strict category iso
  ----------------------------------------------------------------------

  Φ : Functor P.PolyCat R.RCat
  Φ .Functor.F-ob A = A
  Φ .Functor.F-hom {x} {y} = toHom x y
  Φ .Functor.F-id {x} = to-id x
  Φ .Functor.F-seq {x} {y} {z} f g = to-seq x y z f g

  PolyRecognition : CatIsoStrict P.PolyCat R.RCat
  PolyRecognition .CatIsoStrict.F = Φ
  PolyRecognition .CatIsoStrict.obEq = idIsEquiv ob
  PolyRecognition .CatIsoStrict.homEq =
    λ A B → isoToIsEquiv (homIsoAt A B)
