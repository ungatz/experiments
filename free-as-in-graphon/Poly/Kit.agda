{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Shared lemmas
--
-- Consequences of the DistSMC fields, used by the polynomial constructions
-- below: the copairing calculus for the coproduct, helpers for the initial
-- object and the coproduct unitors, the coproduct associator with its
-- restriction rules, tensor functoriality, and combinators for transporting
-- along zigzags.  No theorems live here.
------------------------------------------------------------------------

module Poly.Kit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.BinCoproduct

open import Poly.Base
open import Poly.Monoidal.Distributive

module Kit {ℓ ℓ' : Level} (D : DistSMC ℓ ℓ') where

  open DistSMC D

  ----------------------------------------------------------------------
  -- Coproduct kit (diagrammatic order)
  ----------------------------------------------------------------------

  β₁ : {x y z : ob} (f : Hom[ x , z ]) (g : Hom[ y , z ])
     → ι₁ ⋆ copair f g ≡ f
  β₁ {x} {y} f g = coprods x y .BinCoproduct.univProp f g .fst .snd .fst

  β₂ : {x y z : ob} (f : Hom[ x , z ]) (g : Hom[ y , z ])
     → ι₂ ⋆ copair f g ≡ g
  β₂ {x} {y} f g = coprods x y .BinCoproduct.univProp f g .fst .snd .snd

  copair-unique : {x y z : ob} (f : Hom[ x , z ]) (g : Hom[ y , z ])
                  (h : Hom[ x ⊕ y , z ])
                → ι₁ ⋆ h ≡ f → ι₂ ⋆ h ≡ g → copair f g ≡ h
  copair-unique {x} {y} f g h p q =
    cong fst (coprods x y .BinCoproduct.univProp f g .snd (h , p , q))

  copair-post : {x y z w : ob}
                (f : Hom[ x , z ]) (g : Hom[ y , z ]) (h : Hom[ z , w ])
              → copair f g ⋆ h ≡ copair (f ⋆ h) (g ⋆ h)
  copair-post f g h = sym (copair-unique (f ⋆ h) (g ⋆ h) (copair f g ⋆ h)
    (sym (⋆Assoc _ _ _) ∙ cong (_⋆ h) (β₁ f g))
    (sym (⋆Assoc _ _ _) ∙ cong (_⋆ h) (β₂ f g)))

  ⊕-ext : {x y z : ob} (f g : Hom[ x ⊕ y , z ])
        → ι₁ ⋆ f ≡ ι₁ ⋆ g → ι₂ ⋆ f ≡ ι₂ ⋆ g → f ≡ g
  ⊕-ext f g p q =
    sym (copair-unique (ι₁ ⋆ f) (ι₂ ⋆ f) f refl refl)
    ∙ cong₂ copair p q
    ∙ copair-unique (ι₁ ⋆ g) (ι₂ ⋆ g) g refl refl

  ⊕-ext3 : {x y z w : ob} (f g : Hom[ (x ⊕ y) ⊕ z , w ])
         → ι₁ ⋆ (ι₁ ⋆ f) ≡ ι₁ ⋆ (ι₁ ⋆ g)
         → ι₂ ⋆ (ι₁ ⋆ f) ≡ ι₂ ⋆ (ι₁ ⋆ g)
         → ι₂ ⋆ f ≡ ι₂ ⋆ g
         → f ≡ g
  ⊕-ext3 f g p q r =
    ⊕-ext f g (⊕-ext (ι₁ ⋆ f) (ι₁ ⋆ g) p q) r

  ⊕-ext4 : {x y z u w : ob} (f g : Hom[ ((x ⊕ y) ⊕ z) ⊕ u , w ])
         → ι₁ ⋆ (ι₁ ⋆ (ι₁ ⋆ f)) ≡ ι₁ ⋆ (ι₁ ⋆ (ι₁ ⋆ g))
         → ι₂ ⋆ (ι₁ ⋆ (ι₁ ⋆ f)) ≡ ι₂ ⋆ (ι₁ ⋆ (ι₁ ⋆ g))
         → ι₂ ⋆ (ι₁ ⋆ f) ≡ ι₂ ⋆ (ι₁ ⋆ g)
         → ι₂ ⋆ f ≡ ι₂ ⋆ g
         → f ≡ g
  ⊕-ext4 f g pL pK pH pA =
    ⊕-ext f g
      (⊕-ext (ι₁ ⋆ f) (ι₁ ⋆ g)
        (⊕-ext (ι₁ ⋆ (ι₁ ⋆ f)) (ι₁ ⋆ (ι₁ ⋆ g)) pL pK) pH) pA

  -- push an injection past a (⊕₁) and past a copair (restriction pushes)
  push₁ : {x x' y y' w : ob}
          (p : Hom[ x , x' ]) (q : Hom[ y , y' ]) (m : Hom[ x' ⊕ y' , w ])
        → ι₁ ⋆ ((p ⊕₁ q) ⋆ m) ≡ p ⋆ (ι₁ ⋆ m)
  push₁ p q m =
    sym (⋆Assoc ι₁ (p ⊕₁ q) m)
    ∙ cong (_⋆ m) (β₁ (p ⋆ ι₁) (q ⋆ ι₂))
    ∙ ⋆Assoc p ι₁ m

  push₂ : {x x' y y' w : ob}
          (p : Hom[ x , x' ]) (q : Hom[ y , y' ]) (m : Hom[ x' ⊕ y' , w ])
        → ι₂ ⋆ ((p ⊕₁ q) ⋆ m) ≡ q ⋆ (ι₂ ⋆ m)
  push₂ p q m =
    sym (⋆Assoc ι₂ (p ⊕₁ q) m)
    ∙ cong (_⋆ m) (β₂ (p ⋆ ι₁) (q ⋆ ι₂))
    ∙ ⋆Assoc q ι₂ m

  cp₁ : {x y z w : ob}
        (a : Hom[ x , z ]) (b : Hom[ y , z ]) (m : Hom[ z , w ])
      → ι₁ ⋆ (copair a b ⋆ m) ≡ a ⋆ m
  cp₁ a b m = sym (⋆Assoc ι₁ (copair a b) m) ∙ cong (_⋆ m) (β₁ a b)

  cp₂ : {x y z w : ob}
        (a : Hom[ x , z ]) (b : Hom[ y , z ]) (m : Hom[ z , w ])
      → ι₂ ⋆ (copair a b ⋆ m) ≡ b ⋆ m
  cp₂ a b m = sym (⋆Assoc ι₂ (copair a b) m) ∙ cong (_⋆ m) (β₂ a b)

  ⊕₁-ι₁ : {x x' y y' : ob} (f : Hom[ x , x' ]) (g : Hom[ y , y' ])
        → ι₁ ⋆ (f ⊕₁ g) ≡ f ⋆ ι₁
  ⊕₁-ι₁ f g = β₁ (f ⋆ ι₁) (g ⋆ ι₂)

  ⊕₁-ι₂ : {x x' y y' : ob} (f : Hom[ x , x' ]) (g : Hom[ y , y' ])
        → ι₂ ⋆ (f ⊕₁ g) ≡ g ⋆ ι₂
  ⊕₁-ι₂ f g = β₂ (f ⋆ ι₁) (g ⋆ ι₂)

  ⊕₁-copair : {x x' y y' z : ob}
              (f : Hom[ x , x' ]) (g : Hom[ y , y' ])
              (u : Hom[ x' , z ]) (v : Hom[ y' , z ])
            → (f ⊕₁ g) ⋆ copair u v ≡ copair (f ⋆ u) (g ⋆ v)
  ⊕₁-copair f g u v = sym (copair-unique (f ⋆ u) (g ⋆ v) _
    ( sym (⋆Assoc _ _ _)
    ∙ cong (_⋆ copair u v) (⊕₁-ι₁ f g)
    ∙ ⋆Assoc _ _ _
    ∙ cong (f ⋆_) (β₁ u v))
    ( sym (⋆Assoc _ _ _)
    ∙ cong (_⋆ copair u v) (⊕₁-ι₂ f g)
    ∙ ⋆Assoc _ _ _
    ∙ cong (g ⋆_) (β₂ u v)))

  ⊕₁-seq : {x x' x'' y y' y'' : ob}
           (f : Hom[ x , x' ]) (f' : Hom[ x' , x'' ])
           (g : Hom[ y , y' ]) (g' : Hom[ y' , y'' ])
         → (f ⊕₁ g) ⋆ (f' ⊕₁ g') ≡ (f ⋆ f') ⊕₁ (g ⋆ g')
  ⊕₁-seq f f' g g' =
    ⊕₁-copair f g (f' ⋆ ι₁) (g' ⋆ ι₂)
    ∙ cong₂ copair (sym (⋆Assoc f f' ι₁)) (sym (⋆Assoc g g' ι₂))

  ⊕₁-id : {x y : ob} → (id {x} ⊕₁ id {y}) ≡ id
  ⊕₁-id {x} {y} = copair-unique {x} {y} {x ⊕ y} (id ⋆ ι₁) (id ⋆ ι₂) id
    (⋆IdR ι₁ ∙ sym (⋆IdL ι₁)) (⋆IdR ι₂ ∙ sym (⋆IdL ι₂))

  -- id ⊕₁ (p ⋆ q) splits as (id ⊕₁ p) ⋆ (id ⊕₁ q)
  split-id⊕₁ : {a x x' x'' : ob} (p : Hom[ x , x' ]) (q : Hom[ x' , x'' ])
             → (id {a} ⊕₁ (p ⋆ q)) ≡ (id ⊕₁ p) ⋆ (id ⊕₁ q)
  split-id⊕₁ {a} p q =
    sym (⊕₁-seq (id {a}) (id {a}) p q ∙ cong (_⊕₁ (p ⋆ q)) (⋆IdL id))

  ----------------------------------------------------------------------
  -- Initial-object helpers and coproduct unitors
  ----------------------------------------------------------------------

  !→ : {a : ob} → Hom[ 𝟘 , a ]
  !→ {a} = initialD .snd a .fst

  init⊘ : {a : ob} (f g : Hom[ 𝟘 , a ]) → f ≡ g
  init⊘ {a} f g = isContr→isProp (initialD .snd a) f g

  -- coproduct unitors
  lu : {a : ob} → Hom[ 𝟘 ⊕ a , a ]
  lu = copair !→ id
  ru : {a : ob} → Hom[ a ⊕ 𝟘 , a ]
  ru = copair id !→

  ----------------------------------------------------------------------
  -- Coproduct associator (concrete copairing) and its restrictions
  ----------------------------------------------------------------------

  aRL : {x y z : ob} → Hom[ (x ⊕ y) ⊕ z , x ⊕ (y ⊕ z) ]
  aRL {x} {y} {z} = copair (copair ι₁ (ι₁ ⋆ ι₂)) (ι₂ ⋆ ι₂)

  aRL-x : {x y z : ob} → ι₁ ⋆ (ι₁ ⋆ aRL {x} {y} {z}) ≡ ι₁
  aRL-x = cong (ι₁ ⋆_) (β₁ (copair ι₁ (ι₁ ⋆ ι₂)) (ι₂ ⋆ ι₂)) ∙ β₁ ι₁ (ι₁ ⋆ ι₂)

  aRL-y : {x y z : ob} → ι₂ ⋆ (ι₁ ⋆ aRL {x} {y} {z}) ≡ ι₁ ⋆ ι₂
  aRL-y = cong (ι₂ ⋆_) (β₁ (copair ι₁ (ι₁ ⋆ ι₂)) (ι₂ ⋆ ι₂)) ∙ β₂ ι₁ (ι₁ ⋆ ι₂)

  aRL-z : {x y z : ob} → ι₂ ⋆ aRL {x} {y} {z} ≡ ι₂ ⋆ ι₂
  aRL-z = β₂ (copair ι₁ (ι₁ ⋆ ι₂)) (ι₂ ⋆ ι₂)

  -- restriction of aRL through a post-composition ⋆ M
  aRL-post-x : {x y z w : ob} (M : Hom[ x ⊕ (y ⊕ z) , w ])
             → ι₁ ⋆ (ι₁ ⋆ (aRL ⋆ M)) ≡ ι₁ ⋆ M
  aRL-post-x M =
      cong (ι₁ ⋆_) (sym (⋆Assoc ι₁ aRL M))
    ∙ sym (⋆Assoc ι₁ (ι₁ ⋆ aRL) M)
    ∙ cong (_⋆ M) aRL-x

  aRL-post-y : {x y z w : ob} (M : Hom[ x ⊕ (y ⊕ z) , w ])
             → ι₂ ⋆ (ι₁ ⋆ (aRL ⋆ M)) ≡ (ι₁ ⋆ ι₂) ⋆ M
  aRL-post-y M =
      cong (ι₂ ⋆_) (sym (⋆Assoc ι₁ aRL M))
    ∙ sym (⋆Assoc ι₂ (ι₁ ⋆ aRL) M)
    ∙ cong (_⋆ M) aRL-y

  aRL-post-z : {x y z w : ob} (M : Hom[ x ⊕ (y ⊕ z) , w ])
             → ι₂ ⋆ (aRL ⋆ M) ≡ (ι₂ ⋆ ι₂) ⋆ M
  aRL-post-z M = sym (⋆Assoc ι₂ aRL M) ∙ cong (_⋆ M) aRL-z

  ----------------------------------------------------------------------
  -- Tensor kit
  ----------------------------------------------------------------------

  ⊗-id : {x y : ob} → (id {x} ⊗ₕ id {y}) ≡ id
  ⊗-id = ─⊗─ .Functor.F-id

  ⊗-seq : {x x' x'' y y' y'' : ob}
          (f : Hom[ x , x' ]) (f' : Hom[ x' , x'' ])
          (g : Hom[ y , y' ]) (g' : Hom[ y' , y'' ])
        → (f ⊗ₕ g) ⋆ (f' ⊗ₕ g') ≡ (f ⋆ f') ⊗ₕ (g ⋆ g')
  ⊗-seq f f' g g' = sym (─⊗─ .Functor.F-seq (f , g) (f' , g'))

  id⊗s : {g x y z : ob} (u : Hom[ x , y ]) (v : Hom[ y , z ])
       → (id {g} ⊗ₕ u) ⋆ (id {g} ⊗ₕ v) ≡ id {g} ⊗ₕ (u ⋆ v)
  id⊗s {g} u v = ⊗-seq (id {g}) (id {g}) u v ∙ cong (_⊗ₕ (u ⋆ v)) (⋆IdL id)

  α-nat : {x x' y y' z z' : ob}
          (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
        → (f ⊗ₕ (g ⊗ₕ h)) ⋆ α⟨ x' , y' , z' ⟩
        ≡ α⟨ x , y , z ⟩ ⋆ ((f ⊗ₕ g) ⊗ₕ h)
  α-nat f g h = α .NatIso.trans .NatTrans.N-hom (f , g , h)

  η-nat : {a b : ob} (f : Hom[ a , b ])
        → (id ⊗ₕ f) ⋆ η⟨ b ⟩ ≡ η⟨ a ⟩ ⋆ f
  η-nat f = η .NatIso.trans .NatTrans.N-hom f

  α-sec : (x y z : ob) → α⁻¹⟨ x , y , z ⟩ ⋆ α⟨ x , y , z ⟩ ≡ id
  α-sec x y z = α .NatIso.nIso (x , y , z) .isIso.sec

  η-sec : (x : ob) → η⁻¹⟨ x ⟩ ⋆ η⟨ x ⟩ ≡ id
  η-sec x = η .NatIso.nIso x .isIso.sec

  ----------------------------------------------------------------------
  -- Zig-zag transport / recursion
  ----------------------------------------------------------------------

  mapFence : {ℓa ℓb ℓr ℓs : Level}
           {X : Type ℓa} {Y : Type ℓb}
           {R : X → X → Type ℓr} {S : Y → Y → Type ℓs}
           (φ : X → Y)
         → (∀ {x x'} → R x x' → S (φ x) (φ x'))
         → ∀ {x x'} → ZigZag R x x' → ZigZag S (φ x) (φ x')
  mapFence φ h zz-refl        = zz-refl
  mapFence φ h (zz-step st)   = zz-step (h st)
  mapFence φ h (zz-back st)   = zz-back (h st)
  mapFence φ h (zz-trans p q) = zz-trans (mapFence φ h p) (mapFence φ h q)

  foldFence : {ℓa ℓr ℓb : Level} {X : Type ℓa} {R : X → X → Type ℓr}
          {Y : Type ℓb} (φ : X → Y)
        → (∀ {x x'} → R x x' → φ x ≡ φ x')
        → ∀ {x x'} → ZigZag R x x' → φ x ≡ φ x'
  foldFence φ h zz-refl        = refl
  foldFence φ h (zz-step st)   = h st
  foldFence φ h (zz-back st)   = sym (h st)
  foldFence φ h (zz-trans p q) = foldFence φ h p ∙ foldFence φ h q
