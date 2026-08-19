{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- The cocartesian polynomial category R[C]
--
-- The polynomial category over a base taken with its chosen coproduct as
-- tensor and its chosen initial object as unit.  It is built here over any
-- distributive symmetric monoidal base, but only the coproduct and the initial
-- object are used: the tensor, the symmetry and the distributor are never
-- touched.
--
-- Representatives, the step relation, the quotient, composition by heap
-- accumulation, and the two unit laws and associativity, ending in an honest
-- Category.  The coproduct pentagon is proved from scratch, since the library
-- states it for a monoidal structure rather than for a chosen coproduct.
------------------------------------------------------------------------

module Poly.Cocartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/)

open import Poly.Base
open import Poly.Monoidal.Distributive
open import Poly.Monoidal.SetInstance using (SetDistSMC)
open import Poly.Kit

module AllocationCompletion {ℓ ℓ' : Level} (D : DistSMC ℓ ℓ') where

  open DistSMC D
  open Kit D  -- the shared coproduct, initial-object and associator lemmas

  ----------------------------------------------------------------------
  -- Associator naturality (reusable engine for congruence + assoc)
  ----------------------------------------------------------------------

  private
    aRL-nat : {x x' y y' z z' : ob}
              (u : Hom[ x , x' ]) (v : Hom[ y , y' ]) (w : Hom[ z , z' ])
            → ((u ⊕₁ v) ⊕₁ w) ⋆ aRL ≡ aRL ⋆ (u ⊕₁ (v ⊕₁ w))
    aRL-nat {x} {x'} {y} {y'} {z} {z'} u v w = ⊕-ext3 _ _ cx cy cz
      where
      m : Hom[ x ⊕ (y ⊕ z) , x' ⊕ (y' ⊕ z') ]
      m = u ⊕₁ (v ⊕₁ w)
      -- LHS = ((u⊕₁v)⊕₁w) ⋆ aRL ;  RHS = aRL ⋆ m
      cxL : ι₁ ⋆ (ι₁ ⋆ (((u ⊕₁ v) ⊕₁ w) ⋆ aRL)) ≡ u ⋆ ι₁
      cxL = cong (ι₁ ⋆_) (push₁ (u ⊕₁ v) w aRL)
          ∙ push₁ u v (ι₁ ⋆ aRL)
          ∙ cong (u ⋆_) aRL-x
      cxR : ι₁ ⋆ (ι₁ ⋆ (aRL ⋆ m)) ≡ u ⋆ ι₁
      cxR = cong (ι₁ ⋆_) (cp₁ (copair ι₁ (ι₁ ⋆ ι₂)) (ι₂ ⋆ ι₂) m)
          ∙ cp₁ ι₁ (ι₁ ⋆ ι₂) m
          ∙ ⊕₁-ι₁ u (v ⊕₁ w)
      cx = cxL ∙ sym cxR

      cyL : ι₂ ⋆ (ι₁ ⋆ (((u ⊕₁ v) ⊕₁ w) ⋆ aRL)) ≡ v ⋆ (ι₁ ⋆ ι₂)
      cyL = cong (ι₂ ⋆_) (push₁ (u ⊕₁ v) w aRL)
          ∙ push₂ u v (ι₁ ⋆ aRL)
          ∙ cong (v ⋆_) aRL-y
      cyR : ι₂ ⋆ (ι₁ ⋆ (aRL ⋆ m)) ≡ v ⋆ (ι₁ ⋆ ι₂)
      cyR = cong (ι₂ ⋆_) (cp₁ (copair ι₁ (ι₁ ⋆ ι₂)) (ι₂ ⋆ ι₂) m)
          ∙ cp₂ ι₁ (ι₁ ⋆ ι₂) m
          ∙ ⋆Assoc ι₁ ι₂ m
          ∙ cong (ι₁ ⋆_) (⊕₁-ι₂ u (v ⊕₁ w))
          ∙ sym (⋆Assoc ι₁ (v ⊕₁ w) ι₂)
          ∙ cong (_⋆ ι₂) (⊕₁-ι₁ v w)
          ∙ ⋆Assoc v ι₁ ι₂
      cy = cyL ∙ sym cyR

      czL : ι₂ ⋆ (((u ⊕₁ v) ⊕₁ w) ⋆ aRL) ≡ w ⋆ (ι₂ ⋆ ι₂)
      czL = push₂ (u ⊕₁ v) w aRL
          ∙ cong (w ⋆_) aRL-z
      czR : ι₂ ⋆ (aRL ⋆ m) ≡ w ⋆ (ι₂ ⋆ ι₂)
      czR = cp₂ (copair ι₁ (ι₁ ⋆ ι₂)) (ι₂ ⋆ ι₂) m
          ∙ ⋆Assoc ι₂ ι₂ m
          ∙ cong (ι₂ ⋆_) (⊕₁-ι₂ u (v ⊕₁ w))
          ∙ sym (⋆Assoc ι₂ (v ⊕₁ w) ι₂)
          ∙ cong (_⋆ ι₂) (⊕₁-ι₂ v w)
          ∙ ⋆Assoc w ι₂ ι₂
      cz = czL ∙ sym czR

  ----------------------------------------------------------------------
  -- The coproduct pentagon (Mac Lane coherence for the associator)
  ----------------------------------------------------------------------

  private
    pentagon⊕ : {a b c d : ob}
              → (aRL {a ⊕ b} {c} {d} ⋆ aRL {a} {b} {c ⊕ d})
              ≡ ((aRL {a} {b} {c} ⊕₁ id {d})
                 ⋆ (aRL {a} {b ⊕ c} {d} ⋆ (id {a} ⊕₁ aRL {b} {c} {d})))
    pentagon⊕ {a} {b} {c} {d} = ⊕-ext4 _ _ pL pK pH pA
      where
      A2  = aRL {a} {b} {c ⊕ d}
      P   = aRL {a} {b} {c}
      Q3  = aRL {b} {c} {d}
      B3  = id {a} ⊕₁ Q3
      R23 = aRL {a} {b ⊕ c} {d} ⋆ B3
      -- leaf a
      pL : ι₁ ⋆ (ι₁ ⋆ (ι₁ ⋆ (aRL ⋆ A2)))
         ≡ ι₁ ⋆ (ι₁ ⋆ (ι₁ ⋆ ((P ⊕₁ id) ⋆ R23)))
      pL = ( cong (ι₁ ⋆_) (aRL-post-x A2) ∙ aRL-x )
         ∙ sym ( cong (λ t → ι₁ ⋆ (ι₁ ⋆ t)) (push₁ P id R23)
               ∙ aRL-post-x (ι₁ ⋆ R23)
               ∙ aRL-post-x B3
               ∙ ⊕₁-ι₁ id Q3
               ∙ ⋆IdL ι₁ )
      -- leaf b
      pK : ι₂ ⋆ (ι₁ ⋆ (ι₁ ⋆ (aRL ⋆ A2)))
         ≡ ι₂ ⋆ (ι₁ ⋆ (ι₁ ⋆ ((P ⊕₁ id) ⋆ R23)))
      pK = ( cong (ι₂ ⋆_) (aRL-post-x A2) ∙ aRL-y )
         ∙ sym ( cong (λ t → ι₂ ⋆ (ι₁ ⋆ t)) (push₁ P id R23)
               ∙ aRL-post-y (ι₁ ⋆ R23)
               ∙ ⋆Assoc ι₁ ι₂ (ι₁ ⋆ R23)
               ∙ cong (ι₁ ⋆_) ( aRL-post-y B3
                              ∙ ⋆Assoc ι₁ ι₂ B3
                              ∙ cong (ι₁ ⋆_) (⊕₁-ι₂ id Q3) )
               ∙ aRL-post-x ι₂ )
      -- leaf c
      pH : ι₂ ⋆ (ι₁ ⋆ (aRL ⋆ A2)) ≡ ι₂ ⋆ (ι₁ ⋆ ((P ⊕₁ id) ⋆ R23))
      pH = ( aRL-post-y A2 ∙ ⋆Assoc ι₁ ι₂ A2 ∙ cong (ι₁ ⋆_) aRL-z )
         ∙ sym ( cong (ι₂ ⋆_) (push₁ P id R23)
               ∙ aRL-post-z (ι₁ ⋆ R23)
               ∙ ⋆Assoc ι₂ ι₂ (ι₁ ⋆ R23)
               ∙ cong (ι₂ ⋆_) ( aRL-post-y B3
                              ∙ ⋆Assoc ι₁ ι₂ B3
                              ∙ cong (ι₁ ⋆_) (⊕₁-ι₂ id Q3) )
               ∙ aRL-post-y ι₂
               ∙ ⋆Assoc ι₁ ι₂ ι₂ )
      -- leaf d
      pA : ι₂ ⋆ (aRL ⋆ A2) ≡ ι₂ ⋆ ((P ⊕₁ id) ⋆ R23)
      pA = ( aRL-post-z A2 ∙ ⋆Assoc ι₂ ι₂ A2 ∙ cong (ι₂ ⋆_) aRL-z )
         ∙ sym ( push₂ P id R23
               ∙ ⋆IdL (ι₂ ⋆ R23)
               ∙ aRL-post-z B3
               ∙ ⋆Assoc ι₂ ι₂ B3
               ∙ cong (ι₂ ⋆_) (⊕₁-ι₂ id Q3)
               ∙ aRL-post-z ι₂
               ∙ ⋆Assoc ι₂ ι₂ ι₂ )

  ----------------------------------------------------------------------
  -- The allocation completion: carrier, step relation, quotient
  ----------------------------------------------------------------------

  -- R[V](A,B): a heap H and a core H ⊕ A → B.
  RBnd : (A B : ob) → Type (ℓ-max ℓ ℓ')
  RBnd A B = Σ[ H ∈ ob ] Hom[ H ⊕ A , B ]

  -- The heap mediator step: (H,f) ~ (H',f') via r : H → H'.
  RStep : (A B : ob) → RBnd A B → RBnd A B → Type ℓ'
  RStep A B (H , f) (H' , f') =
    Σ[ r ∈ Hom[ H , H' ] ] (f ≡ (r ⊕₁ id) ⋆ f')

  RQuot : (A B : ob) → Type (ℓ-max ℓ ℓ')
  RQuot A B = ZigZagQuotient (RStep A B)

  ----------------------------------------------------------------------
  -- Composition and identity (heap accumulation via the associator)
  ----------------------------------------------------------------------

  -- (K,g) after (H,f): heap K ⊕ H, core aRL ⋆ (id ⊕₁ f) ⋆ g.
  compRCore : {A B C : ob} → RBnd B C → RBnd A B → RBnd A C
  compRCore {A} (K , g) (H , f) =
    (K ⊕ H) , (aRL ⋆ ((id ⊕₁ f) ⋆ g))

  idRBnd : (A : ob) → RBnd A A
  idRBnd A = 𝟘 , lu

  ----------------------------------------------------------------------
  -- Congruence in each factor (uses associator naturality)
  ----------------------------------------------------------------------

  -- Vary the first factor (A → B).
  compRL-step : {A B C : ob} {x x' : RBnd A B} (y : RBnd B C)
              → RStep A B x x'
              → RStep A C (compRCore y x) (compRCore y x')
  compRL-step {A} {B} {C} {H , f} {H' , f'} (K , g) (r , e) =
    (id ⊕₁ r) , eq
    where
    eq : aRL ⋆ ((id ⊕₁ f) ⋆ g)
       ≡ ((id ⊕₁ r) ⊕₁ id) ⋆ (aRL ⋆ ((id ⊕₁ f') ⋆ g))
    eq =
        cong (λ t → aRL ⋆ ((id ⊕₁ t) ⋆ g)) e
      ∙ cong (λ t → aRL ⋆ (t ⋆ g))
          (sym (⊕₁-seq id id (r ⊕₁ id) f'
                ∙ cong (_⊕₁ ((r ⊕₁ id) ⋆ f')) (⋆IdL id)))
      ∙ cong (aRL ⋆_) (⋆Assoc (id ⊕₁ (r ⊕₁ id)) (id ⊕₁ f') g)
      ∙ sym (⋆Assoc aRL (id ⊕₁ (r ⊕₁ id)) ((id ⊕₁ f') ⋆ g))
      ∙ cong (_⋆ ((id ⊕₁ f') ⋆ g)) (sym (aRL-nat id r id))
      ∙ ⋆Assoc ((id ⊕₁ r) ⊕₁ id) aRL ((id ⊕₁ f') ⋆ g)

  -- Vary the second factor (B → C).
  compRR-step : {A B C : ob} {y y' : RBnd B C} (x : RBnd A B)
              → RStep B C y y'
              → RStep A C (compRCore y x) (compRCore y' x)
  compRR-step {A} {B} {C} {K , g} {K' , g'} (H , f) (r₂ , e₂) =
    (r₂ ⊕₁ id) , eq
    where
    interL : (id ⊕₁ f) ⋆ (r₂ ⊕₁ id) ≡ r₂ ⊕₁ f
    interL = ⊕₁-seq id r₂ f id ∙ cong₂ _⊕₁_ (⋆IdL r₂) (⋆IdR f)
    interR : (r₂ ⊕₁ id) ⋆ (id ⊕₁ f) ≡ r₂ ⊕₁ f
    interR = ⊕₁-seq r₂ id id f ∙ cong₂ _⊕₁_ (⋆IdR r₂) (⋆IdL f)
    eq : aRL ⋆ ((id ⊕₁ f) ⋆ g)
       ≡ ((r₂ ⊕₁ id) ⊕₁ id) ⋆ (aRL ⋆ ((id ⊕₁ f) ⋆ g'))
    eq =
        cong (λ t → aRL ⋆ ((id ⊕₁ f) ⋆ t)) e₂
      ∙ cong (aRL ⋆_) (sym (⋆Assoc (id ⊕₁ f) (r₂ ⊕₁ id) g'))
      ∙ cong (λ t → aRL ⋆ (t ⋆ g')) (interL ∙ sym interR)
      ∙ cong (aRL ⋆_) (⋆Assoc (r₂ ⊕₁ id) (id ⊕₁ f) g')
      ∙ sym (⋆Assoc aRL (r₂ ⊕₁ id) ((id ⊕₁ f) ⋆ g'))
      ∙ cong (_⋆ ((id ⊕₁ f) ⋆ g'))
          (cong (aRL ⋆_) (cong (r₂ ⊕₁_) (sym ⊕₁-id)) ∙ sym (aRL-nat r₂ id id))
      ∙ ⋆Assoc ((r₂ ⊕₁ id) ⊕₁ id) aRL ((id ⊕₁ f) ⋆ g')

  ----------------------------------------------------------------------
  -- Composition descends to the quotient
  ----------------------------------------------------------------------


  compRQuot : {A B C : ob} → RQuot A B → RQuot B C → RQuot A C
  compRQuot {A} {B} {C} = SQ.rec2 squash/ (λ x y → [ compRCore y x ])
    (λ x x' y zz → eq/ _ _
      (mapFence (compRCore y) (λ {a} {b} st → compRL-step y st) zz))
    (λ x y y' zz → eq/ _ _
      (mapFence (λ v → compRCore v x) (λ {a} {b} st → compRR-step x st) zz))

  ----------------------------------------------------------------------
  -- Unit law steps
  ----------------------------------------------------------------------

  -- id ⋆ x ~ x : compRCore x (idRBnd A) ~ x, with heap H ⊕ 𝟘 → H (ru).
  idlStepR : {A B : ob} (x : RBnd A B)
           → RStep A B (compRCore x (idRBnd A)) x
  idlStepR {A} {B} (H , f) = ru , (sym (⋆Assoc aRL (id ⊕₁ lu) f) ∙ cong (_⋆ f) U)
    where
    U : aRL ⋆ (id {H} ⊕₁ lu {A}) ≡ (ru {H} ⊕₁ id {A})
    U = ⊕-ext3 _ _ cH (init⊘ _ _) cA
      where
      cH : ι₁ ⋆ (ι₁ ⋆ (aRL ⋆ (id ⊕₁ lu))) ≡ ι₁ ⋆ (ι₁ ⋆ (ru ⊕₁ id))
      cH = ( aRL-post-x (id ⊕₁ lu) ∙ ⊕₁-ι₁ id lu ∙ ⋆IdL ι₁ )
         ∙ sym ( cong (ι₁ ⋆_) (⊕₁-ι₁ ru id)
               ∙ sym (⋆Assoc ι₁ ru ι₁)
               ∙ cong (_⋆ ι₁) (β₁ id !→)
               ∙ ⋆IdL ι₁ )
      cA : ι₂ ⋆ (aRL ⋆ (id ⊕₁ lu)) ≡ ι₂ ⋆ (ru ⊕₁ id)
      cA = ( aRL-post-z (id ⊕₁ lu)
           ∙ ⋆Assoc ι₂ ι₂ (id ⊕₁ lu)
           ∙ cong (ι₂ ⋆_) (⊕₁-ι₂ id lu)
           ∙ sym (⋆Assoc ι₂ lu ι₂)
           ∙ cong (_⋆ ι₂) (β₂ !→ id)
           ∙ ⋆IdL ι₂ )
         ∙ sym ( ⊕₁-ι₂ ru id ∙ ⋆IdL ι₂ )

  -- x ⋆ id ~ x : compRCore (idRBnd B) x ~ x, with heap 𝟘 ⊕ H → H (lu).
  idrStepR : {A B : ob} (x : RBnd A B)
           → RStep A B (compRCore (idRBnd B) x) x
  idrStepR {A} {B} (H , f) = lu , eq
    where
    Mf : Hom[ 𝟘 ⊕ (H ⊕ A) , B ]
    Mf = (id ⊕₁ f) ⋆ lu
    ι₂M : ι₂ ⋆ Mf ≡ f
    ι₂M = sym (⋆Assoc ι₂ (id ⊕₁ f) lu)
        ∙ cong (_⋆ lu) (⊕₁-ι₂ id f)
        ∙ ⋆Assoc f ι₂ lu
        ∙ cong (f ⋆_) (β₂ !→ id)
        ∙ ⋆IdR f
    cMid : ι₂ ⋆ (ι₁ ⋆ (aRL ⋆ Mf)) ≡ ι₂ ⋆ (ι₁ ⋆ ((lu ⊕₁ id) ⋆ f))
    cMid = ( aRL-post-y Mf
           ∙ ⋆Assoc ι₁ ι₂ Mf
           ∙ cong (ι₁ ⋆_) ι₂M )
         ∙ sym ( cong (ι₂ ⋆_) (push₁ lu id f)
               ∙ sym (⋆Assoc ι₂ lu (ι₁ ⋆ f))
               ∙ cong (_⋆ (ι₁ ⋆ f)) (β₂ !→ id)
               ∙ ⋆IdL (ι₁ ⋆ f) )
    cA : ι₂ ⋆ (aRL ⋆ Mf) ≡ ι₂ ⋆ ((lu ⊕₁ id) ⋆ f)
    cA = ( aRL-post-z Mf
         ∙ ⋆Assoc ι₂ ι₂ Mf
         ∙ cong (ι₂ ⋆_) ι₂M )
       ∙ sym ( push₂ lu id f ∙ ⋆IdL (ι₂ ⋆ f) )
    eq : aRL ⋆ Mf ≡ (lu ⊕₁ id) ⋆ f
    eq = ⊕-ext3 _ _ (init⊘ _ _) cMid cA

  ----------------------------------------------------------------------
  -- Associativity law step (reduces to naturality + the pentagon)
  ----------------------------------------------------------------------

  assocStepR : {A B C Dd : ob}
               (x : RBnd A B) (y : RBnd B C) (z : RBnd C Dd)
             → RStep A Dd (compRCore (compRCore z y) x)
                          (compRCore z (compRCore y x))
  assocStepR {A} {B} {C} {Dd} (H , f) (K , g) (L , h) = aRL {L} {K} {H} , eq
    where
    Tg : Hom[ L ⊕ (K ⊕ B) , Dd ]
    Tg = (id {L} ⊕₁ g) ⋆ h
    Tail : Hom[ L ⊕ (K ⊕ (H ⊕ A)) , Dd ]
    Tail = (id {L} ⊕₁ (id {K} ⊕₁ f)) ⋆ Tg

    -- commute f past the K,B associator
    commf : (id {L ⊕ K} ⊕₁ f) ⋆ aRL {L} {K} {B}
          ≡ aRL {L} {K} {H ⊕ A} ⋆ (id {L} ⊕₁ (id {K} ⊕₁ f))
    commf = cong (_⋆ aRL {L} {K} {B}) (cong (_⊕₁ f) (sym (⊕₁-id {L} {K})))
          ∙ aRL-nat (id {L}) (id {K}) f

    RHSeq : (aRL {L ⊕ K} {H} {A} ⋆ ((id {L ⊕ K} ⊕₁ f)
                ⋆ (aRL {L} {K} {B} ⋆ Tg)))
          ≡ (aRL {L ⊕ K} {H} {A} ⋆ aRL {L} {K} {H ⊕ A}) ⋆ Tail
    RHSeq =
        cong (aRL {L ⊕ K} {H} {A} ⋆_)
             (sym (⋆Assoc (id {L ⊕ K} ⊕₁ f) (aRL {L} {K} {B}) Tg))
      ∙ cong (λ t → aRL {L ⊕ K} {H} {A} ⋆ (t ⋆ Tg)) commf
      ∙ cong (aRL {L ⊕ K} {H} {A} ⋆_)
             (⋆Assoc (aRL {L} {K} {H ⊕ A}) (id {L} ⊕₁ (id {K} ⊕₁ f)) Tg)
      ∙ sym (⋆Assoc (aRL {L ⊕ K} {H} {A}) (aRL {L} {K} {H ⊕ A}) Tail)

    expandF : (id {L} ⊕₁ (aRL {K} {H} {A} ⋆ ((id {K} ⊕₁ f) ⋆ g))) ⋆ h
            ≡ (id {L} ⊕₁ aRL {K} {H} {A}) ⋆ Tail
    expandF =
        cong (_⋆ h) (split-id⊕₁ (aRL {K} {H} {A}) ((id {K} ⊕₁ f) ⋆ g))
      ∙ cong (λ t → ((id {L} ⊕₁ aRL {K} {H} {A}) ⋆ t) ⋆ h)
             (split-id⊕₁ (id {K} ⊕₁ f) g)
      ∙ ⋆Assoc (id {L} ⊕₁ aRL {K} {H} {A})
               ((id {L} ⊕₁ (id {K} ⊕₁ f)) ⋆ (id {L} ⊕₁ g)) h
      ∙ cong ((id {L} ⊕₁ aRL {K} {H} {A}) ⋆_)
             (⋆Assoc (id {L} ⊕₁ (id {K} ⊕₁ f)) (id {L} ⊕₁ g) h)

    LHSeq : (aRL {L} {K} {H} ⊕₁ id {A})
              ⋆ (aRL {L} {K ⊕ H} {A}
                 ⋆ ((id {L} ⊕₁ (aRL {K} {H} {A} ⋆ ((id {K} ⊕₁ f) ⋆ g))) ⋆ h))
          ≡ ((aRL {L} {K} {H} ⊕₁ id {A})
              ⋆ (aRL {L} {K ⊕ H} {A} ⋆ (id {L} ⊕₁ aRL {K} {H} {A}))) ⋆ Tail
    LHSeq =
        cong (λ t → (aRL {L} {K} {H} ⊕₁ id {A}) ⋆ (aRL {L} {K ⊕ H} {A} ⋆ t))
             expandF
      ∙ cong ((aRL {L} {K} {H} ⊕₁ id {A}) ⋆_)
             (sym (⋆Assoc (aRL {L} {K ⊕ H} {A})
                          (id {L} ⊕₁ aRL {K} {H} {A}) Tail))
      ∙ sym (⋆Assoc (aRL {L} {K} {H} ⊕₁ id {A})
                    (aRL {L} {K ⊕ H} {A} ⋆ (id {L} ⊕₁ aRL {K} {H} {A})) Tail)

    eq : (aRL {L ⊕ K} {H} {A} ⋆ ((id {L ⊕ K} ⊕₁ f)
             ⋆ (aRL {L} {K} {B} ⋆ Tg)))
       ≡ (aRL {L} {K} {H} ⊕₁ id {A})
           ⋆ (aRL {L} {K ⊕ H} {A}
              ⋆ ((id {L} ⊕₁ (aRL {K} {H} {A} ⋆ ((id {K} ⊕₁ f) ⋆ g))) ⋆ h))
    eq = RHSeq ∙ cong (_⋆ Tail) (pentagon⊕ {L} {K} {H} {A}) ∙ sym LHSeq

  ----------------------------------------------------------------------
  -- The allocation completion category  R[V]
  ----------------------------------------------------------------------

  RCat : Category ℓ (ℓ-max ℓ ℓ')
  RCat .Category.ob         = ob
  RCat .Category.Hom[_,_]   = RQuot
  RCat .Category.id {A}     = [ idRBnd A ]
  RCat .Category._⋆_        = compRQuot
  RCat .Category.⋆IdL       = SQ.elimProp (λ _ → squash/ _ _)
                                (λ x → eq/ _ _ (zz-step (idlStepR x)))
  RCat .Category.⋆IdR       = SQ.elimProp (λ _ → squash/ _ _)
                                (λ x → eq/ _ _ (zz-step (idrStepR x)))
  RCat .Category.⋆Assoc     = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
                                (λ x y z → eq/ _ _ (zz-back (assocStepR x y z)))
  RCat .Category.isSetHom   = squash/

------------------------------------------------------------------------
-- Non-vacuity: R[Set], the allocation completion of Set, is a genuine
-- category.  (SetDistSMC is the concrete distributive symmetric
-- monoidal base from Poly.Monoidal.SetInstance.)
------------------------------------------------------------------------

RCat-Set : (ℓ : Level) → Category (ℓ-suc ℓ) (ℓ-suc ℓ)
RCat-Set ℓ = AllocationCompletion.RCat (SetDistSMC ℓ)
