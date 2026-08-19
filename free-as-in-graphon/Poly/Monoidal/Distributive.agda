{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- A distributive symmetric monoidal base
--
-- DistSMC packages a category with set-valued hom-sets, a monoidal structure,
-- a symmetry, chosen binary coproducts, an initial object, a distributor given
-- as component isomorphisms with naturality and the one coherence the
-- constructions below actually spend, and the annihilator saying that x (x) 0
-- is initial.
--
-- The tensor is not required to be cartesian.  No categorical product is
-- imported anywhere in this file, and the copairing laws are derived from the
-- coproduct's universal property rather than fielded.
--
-- The distributor is given componentwise rather than as a natural isomorphism
-- of composite functors.  The field set is the one the constructions need, and
-- it may grow if a later coherence turns out to be required.
------------------------------------------------------------------------

module Poly.Monoidal.Distributive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.Initial

open import Poly.Monoidal.Symmetric

record DistSMC (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    M : MonoidalStr C
    S : SymmetricStr C M

  open Category C public
  open MonoidalStr M public
  open SymmetricStr S public

  field
    coprods  : BinCoproducts C
    initialD : Initial C

  -- Coproduct notation.
  _⊕_ : ob → ob → ob
  x ⊕ y = coprods x y .BinCoproduct.binCoprodOb

  ι₁ : {x y : ob} → Hom[ x , x ⊕ y ]
  ι₁ {x} {y} = coprods x y .BinCoproduct.binCoprodInj₁

  ι₂ : {x y : ob} → Hom[ y , x ⊕ y ]
  ι₂ {x} {y} = coprods x y .BinCoproduct.binCoprodInj₂

  copair : {x y z : ob} → Hom[ x , z ] → Hom[ y , z ] → Hom[ x ⊕ y , z ]
  copair {x} {y} f g = coprods x y .BinCoproduct.univProp f g .fst .fst

  -- Functorial action of ⊕ (derived).
  _⊕₁_ : {x x' y y' : ob} → Hom[ x , x' ] → Hom[ y , y' ]
       → Hom[ x ⊕ y , x' ⊕ y' ]
  f ⊕₁ g = copair (f ⋆ ι₁) (g ⋆ ι₂)

  𝟘 : ob
  𝟘 = initialD .fst

  field
    -- The distributor, componentwise, with the one coherence the
    -- constructions below actually spend.
    δ⟨_,_,_⟩ : (x y z : ob) → CatIso C ((x ⊗ y) ⊕ (x ⊗ z)) (x ⊗ (y ⊕ z))
    δ-nat : {x x' y y' z z' : ob}
            (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
          → ((f ⊗ₕ g) ⊕₁ (f ⊗ₕ h)) ⋆ δ⟨ x' , y' , z' ⟩ .fst
          ≡ δ⟨ x , y , z ⟩ .fst ⋆ (f ⊗ₕ (g ⊕₁ h))
    δ-ι₁ : (x y z : ob)
         → ι₁ ⋆ δ⟨ x , y , z ⟩ .fst ≡ (id ⊗ₕ ι₁ {x = y} {y = z})
    annih : (x : ob) → isInitial C (x ⊗ 𝟘)
