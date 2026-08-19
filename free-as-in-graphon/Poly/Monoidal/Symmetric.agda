{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- The symmetric layer over a monoidal structure
--
-- The cubical library's MonoidalStr fields the associator and unitors as
-- natural isomorphisms with the pentagon and the triangle, and carries no
-- braided or symmetric notion.  This module adds one: a componentwise
-- braiding, its naturality, its involution, and one hexagon, stated in the
-- library's direction for the associator.
--
-- Only one hexagon is fielded.  The second is derivable and is added when a
-- consumer needs it.  The braiding is componentwise rather than a natural
-- isomorphism against a swap functor.
--
-- Source: Mac Lane, Categories for the Working Mathematician, 2nd ed., XI.1.
------------------------------------------------------------------------

module Poly.Monoidal.Symmetric where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base

module _ {ℓ ℓ' : Level} (C : Category ℓ ℓ') (M : MonoidalStr C) where

  open Category C
  open MonoidalStr M

  record SymmetricStr : Type (ℓ-max ℓ ℓ') where
    field
      B⟨_,_⟩ : (x y : ob) → Hom[ x ⊗ y , y ⊗ x ]
      B-nat  : {x x' y y' : ob} (f : Hom[ x , x' ]) (g : Hom[ y , y' ])
             → (f ⊗ₕ g) ⋆ B⟨ x' , y' ⟩ ≡ B⟨ x , y ⟩ ⋆ (g ⊗ₕ f)
      B-invol : (x y : ob) → B⟨ x , y ⟩ ⋆ B⟨ y , x ⟩ ≡ id
      -- The first hexagon, both sides (x⊗y)⊗z → y⊗(z⊗x).
      hexagon : (x y z : ob)
              → α⁻¹⟨ x , y , z ⟩ ⋆ B⟨ x , y ⊗ z ⟩ ⋆ α⁻¹⟨ y , z , x ⟩
              ≡ (B⟨ x , y ⟩ ⊗ₕ id) ⋆ α⁻¹⟨ y , x , z ⟩ ⋆ (id ⊗ₕ B⟨ x , z ⟩)

-- A bundled symmetric monoidal category.
record SymmMonCategory (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    C : Category ℓ ℓ'
    M : MonoidalStr C
    S : SymmetricStr C M
  open Category C public
  open MonoidalStr M public
  open SymmetricStr S public
