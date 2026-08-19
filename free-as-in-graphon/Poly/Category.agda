{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- The polynomial category C[x : jΣ]
--
-- Hermida and Tennent's construction adjoining a monoidal indeterminate,
-- built here in its general form: an arbitrary symmetric monoidal base C, an
-- index Σ, and a strong monoidal functor j.
--
--   objects        = objects of C
--   C[x:jΣ](x,y)   = (Σ w. C(x ⊗ jw , y)) / ~
--   a step (w,f) → (w',f') is an h : w → w' with f ≡ f' ∘ (x ⊗ jh)
--   composition accumulates heaps:
--     (w,f) ∘ (v,g) = (w ⊗ v , (id ⊗ δ⁻¹) ∘ α ∘ ((f ⊗ id) ∘ g))
--   identity       = (I , (id ⊗ γ⁻¹) ∘ ρ)
--
-- The three category laws hold on the quotient because each is a one-step
-- zigzag whose mediator is a structural isomorphism of the index.  Collapsing
-- those 2-cells is what makes composition strictly associative and unitary.
-- The unit laws strip the unit heap by the left and right unitors together
-- with the triangle; associativity is the index's associator, and the
-- obligation reduces to the distributor's associativity, the pentagon and
-- naturality.  The right unit law needs kellyρ below, derived from the
-- pentagon, the triangle and naturality alone, mirroring kellyλ.
--
-- What is built here is C[x : jΣ] as a category, together with the functor
-- adjoining the base into it.  What is not: the bicategory, of which only the
-- shadow on connected components appears; the symmetric monoidal structure
-- upstairs, which is Hermida and Tennent's Proposition 2.1 and is not
-- mechanized here; the characterisation by siftedness, which is cited rather
-- than mechanized; and the free distributive completion, which is not
-- mechanized anywhere.
--
-- Source: Hermida and Tennent, Monoidal indeterminates and categories of
-- possible worlds, ENTCS 2009, sections 2.1 to 2.4.
------------------------------------------------------------------------

module Poly.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/)

open import Poly.Base
open import Poly.Monoidal.Symmetric
open import Poly.Monoidal.Kelly

------------------------------------------------------------------------
-- Strong monoidal functors (none in cubical-0.9's Monoidal.Base)
------------------------------------------------------------------------

record StrongMonoFunctor {ℓΣ ℓΣ' ℓC ℓC'}
       (Σb : SymmMonCategory ℓΣ ℓΣ') (Cb : SymmMonCategory ℓC ℓC')
       : Type (ℓ-max (ℓ-max ℓΣ ℓΣ') (ℓ-max ℓC ℓC')) where
  module ΣM = SymmMonCategory Σb
  module CM = SymmMonCategory Cb
  field
    F₀ : ΣM.ob → CM.ob
    F₁ : {u v : ΣM.ob} → ΣM.Hom[ u , v ] → CM.Hom[ F₀ u , F₀ v ]
    F-id : {u : ΣM.ob} → F₁ (ΣM.id {u}) ≡ CM.id {F₀ u}
    F-seq : {u v w : ΣM.ob} (f : ΣM.Hom[ u , v ]) (g : ΣM.Hom[ v , w ])
          → F₁ (f ΣM.⋆ g) ≡ F₁ f CM.⋆ F₁ g

    δ⟨_,_⟩ : (u v : ΣM.ob) → CM.Hom[ F₀ u CM.⊗ F₀ v , F₀ (u ΣM.⊗ v) ]
    δ-iso : (u v : ΣM.ob) → isIso CM.C δ⟨ u , v ⟩
    γ : CM.Hom[ CM.unit , F₀ ΣM.unit ]
    γ-iso : isIso CM.C γ

    δ-nat : {u u' v v' : ΣM.ob} (p : ΣM.Hom[ u , u' ]) (q : ΣM.Hom[ v , v' ])
          → (F₁ p CM.⊗ₕ F₁ q) CM.⋆ δ⟨ u' , v' ⟩ ≡ δ⟨ u , v ⟩ CM.⋆ F₁ (p ΣM.⊗ₕ q)
    δ-assoc : (u v w : ΣM.ob)
            → CM.α⁻¹⟨ F₀ u , F₀ v , F₀ w ⟩ CM.⋆ (CM.id CM.⊗ₕ δ⟨ v , w ⟩)
                CM.⋆ δ⟨ u , v ΣM.⊗ w ⟩
            ≡ (δ⟨ u , v ⟩ CM.⊗ₕ CM.id) CM.⋆ δ⟨ u ΣM.⊗ v , w ⟩
                CM.⋆ F₁ (ΣM.α⁻¹⟨ u , v , w ⟩)
    γ-left : (v : ΣM.ob)
           → (γ CM.⊗ₕ CM.id) CM.⋆ δ⟨ ΣM.unit , v ⟩ CM.⋆ F₁ (ΣM.η⟨ v ⟩)
           ≡ CM.η⟨ F₀ v ⟩
    γ-right : (v : ΣM.ob)
            → (CM.id CM.⊗ₕ γ) CM.⋆ δ⟨ v , ΣM.unit ⟩ CM.⋆ F₁ (ΣM.ρ⟨ v ⟩)
            ≡ CM.ρ⟨ F₀ v ⟩

------------------------------------------------------------------------
-- The polynomial category
------------------------------------------------------------------------

module PolyOver {ℓΣ ℓΣ' ℓC ℓC'}
       (Σb : SymmMonCategory ℓΣ ℓΣ') (Cb : SymmMonCategory ℓC ℓC')
       (j : StrongMonoFunctor Σb Cb) where

  open StrongMonoFunctor j
  open KellyUnit CM.C CM.M using (η-cancel ; kellyλ ; kellyλ⁻)

  _⊗C_ : CM.ob → CM.ob → CM.ob
  x ⊗C y = x CM.⊗ y
  _⊗Σ_ : ΣM.ob → ΣM.ob → ΣM.ob
  u ⊗Σ v = u ΣM.⊗ v

  δ⁻¹⟨_,_⟩ : (u v : ΣM.ob) → CM.Hom[ F₀ (u ⊗Σ v) , F₀ u ⊗C F₀ v ]
  δ⁻¹⟨ u , v ⟩ = isIso.inv (δ-iso u v)

  δ-sec : (u v : ΣM.ob) → δ⁻¹⟨ u , v ⟩ CM.⋆ δ⟨ u , v ⟩ ≡ CM.id
  δ-sec u v = isIso.sec (δ-iso u v)

  δ-ret : (u v : ΣM.ob) → δ⟨ u , v ⟩ CM.⋆ δ⁻¹⟨ u , v ⟩ ≡ CM.id
  δ-ret u v = isIso.ret (δ-iso u v)

  γ⁻¹ : CM.Hom[ F₀ ΣM.unit , CM.unit ]
  γ⁻¹ = isIso.inv γ-iso

  γ-sec : γ⁻¹ CM.⋆ γ ≡ CM.id
  γ-sec = isIso.sec γ-iso

  γ-ret : γ CM.⋆ γ⁻¹ ≡ CM.id
  γ-ret = isIso.ret γ-iso

  ----------------------------------------------------------------------
  -- tensor-functoriality helpers (the Kit one-liners, re-derived over CM)
  ----------------------------------------------------------------------

  ⊗C-id : {x y : CM.ob} → (CM.id {x} CM.⊗ₕ CM.id {y}) ≡ CM.id
  ⊗C-id = CM.─⊗─ .Functor.F-id

  ⊗C-seq : {x x' x'' y y' y'' : CM.ob}
           (f : CM.Hom[ x , x' ]) (f' : CM.Hom[ x' , x'' ])
           (g : CM.Hom[ y , y' ]) (g' : CM.Hom[ y' , y'' ])
         → (f CM.⊗ₕ g) CM.⋆ (f' CM.⊗ₕ g') ≡ (f CM.⋆ f') CM.⊗ₕ (g CM.⋆ g')
  ⊗C-seq f f' g g' = sym (CM.─⊗─ .Functor.F-seq (f , g) (f' , g'))

  id⊗Cs : {g x y z : CM.ob} (u : CM.Hom[ x , y ]) (v : CM.Hom[ y , z ])
        → (CM.id {g} CM.⊗ₕ u) CM.⋆ (CM.id {g} CM.⊗ₕ v) ≡ CM.id {g} CM.⊗ₕ (u CM.⋆ v)
  id⊗Cs {g} u v = ⊗C-seq (CM.id {g}) (CM.id {g}) u v ∙ cong (CM._⊗ₕ (u CM.⋆ v)) (CM.⋆IdL CM.id)

  id⊗Cs3 : {g w x y z : CM.ob}
          → (u : CM.Hom[ w , x ]) (v : CM.Hom[ x , y ])
          → (t : CM.Hom[ y , z ])
          → (CM.id {g} CM.⊗ₕ u) CM.⋆
              ((CM.id {g} CM.⊗ₕ v) CM.⋆ (CM.id {g} CM.⊗ₕ t))
          ≡ CM.id {g} CM.⊗ₕ (u CM.⋆ (v CM.⋆ t))
  id⊗Cs3 {g} u v t =
      cong ((CM.id {g} CM.⊗ₕ u) CM.⋆_) (id⊗Cs v t)
    ∙ id⊗Cs u (v CM.⋆ t)

  split⊗id : {x y z t : CM.ob}
           → (u : CM.Hom[ x , y ]) (v : CM.Hom[ y , z ])
           → (u CM.⋆ v) CM.⊗ₕ CM.id {t}
           ≡ (u CM.⊗ₕ CM.id {t}) CM.⋆ (v CM.⊗ₕ CM.id {t})
  split⊗id {t = t} u v =
    sym (⊗C-seq u v (CM.id {t}) (CM.id {t})
      ∙ cong ((u CM.⋆ v) CM.⊗ₕ_) (CM.⋆IdL (CM.id {t})))

  αC-nat : {x x' y y' z z' : CM.ob}
           (f : CM.Hom[ x , x' ]) (g : CM.Hom[ y , y' ]) (h : CM.Hom[ z , z' ])
         → (f CM.⊗ₕ (g CM.⊗ₕ h)) CM.⋆ CM.α⟨ x' , y' , z' ⟩
         ≡ CM.α⟨ x , y , z ⟩ CM.⋆ ((f CM.⊗ₕ g) CM.⊗ₕ h)
  αC-nat f g h = CM.α .NatIso.trans .NatTrans.N-hom (f , g , h)

  ρC-nat : {x y : CM.ob} (f : CM.Hom[ x , y ])
         → (f CM.⊗ₕ CM.id {CM.unit}) CM.⋆ CM.ρ⟨ y ⟩ ≡ CM.ρ⟨ x ⟩ CM.⋆ f
  ρC-nat f = CM.ρ .NatIso.trans .NatTrans.N-hom f

  α-secC : (x y z : CM.ob) → CM.α⁻¹⟨ x , y , z ⟩ CM.⋆ CM.α⟨ x , y , z ⟩ ≡ CM.id
  α-secC x y z = CM.α .NatIso.nIso (x , y , z) .isIso.sec

  α-retC : (x y z : CM.ob) → CM.α⟨ x , y , z ⟩ CM.⋆ CM.α⁻¹⟨ x , y , z ⟩ ≡ CM.id
  α-retC x y z = CM.α .NatIso.nIso (x , y , z) .isIso.ret

  -- deltaInv-nat, the inverse form of delta-nat consumed by the congruence chases
  δ⁻¹-nat : {u u' v v' : ΣM.ob} (p : ΣM.Hom[ u , u' ]) (q : ΣM.Hom[ v , v' ])
          → δ⁻¹⟨ u , v ⟩ CM.⋆ (F₁ p CM.⊗ₕ F₁ q) ≡ F₁ (p ΣM.⊗ₕ q) CM.⋆ δ⁻¹⟨ u' , v' ⟩
  δ⁻¹-nat {u} {u'} {v} {v'} p q =
      sym (CM.⋆IdR _)
    ∙ cong ((δ⁻¹⟨ u , v ⟩ CM.⋆ (F₁ p CM.⊗ₕ F₁ q)) CM.⋆_) (sym (δ-ret u' v'))
    ∙ sym (CM.⋆Assoc (δ⁻¹⟨ u , v ⟩ CM.⋆ (F₁ p CM.⊗ₕ F₁ q)) δ⟨ u' , v' ⟩ δ⁻¹⟨ u' , v' ⟩)
    ∙ cong (CM._⋆ δ⁻¹⟨ u' , v' ⟩) (
        CM.⋆Assoc δ⁻¹⟨ u , v ⟩ (F₁ p CM.⊗ₕ F₁ q) δ⟨ u' , v' ⟩
      ∙ cong (δ⁻¹⟨ u , v ⟩ CM.⋆_) (δ-nat p q)
      ∙ sym (CM.⋆Assoc δ⁻¹⟨ u , v ⟩ δ⟨ u , v ⟩ (F₁ (p ΣM.⊗ₕ q)))
      ∙ cong (CM._⋆ F₁ (p ΣM.⊗ₕ q)) (δ-sec u v)
      ∙ CM.⋆IdL (F₁ (p ΣM.⊗ₕ q)))

  -- cancel an iso on the right: f . z == g . z  ==>  f == g
  cancel-post : {a b c : CM.ob} {f g : CM.Hom[ a , b ]} {z : CM.Hom[ b , c ]}
              → isIso CM.C z → f CM.⋆ z ≡ g CM.⋆ z → f ≡ g
  cancel-post {f = f} {g} {z} zi p =
      sym (CM.⋆IdR f)
    ∙ cong (f CM.⋆_) (sym (isIso.ret zi))
    ∙ sym (CM.⋆Assoc f z (isIso.inv zi))
    ∙ cong (CM._⋆ isIso.inv zi) p
    ∙ CM.⋆Assoc g z (isIso.inv zi)
    ∙ cong (g CM.⋆_) (isIso.ret zi)
    ∙ CM.⋆IdR g

  -- cancel an iso on the left: z . f == z . g  ==>  f == g
  cancel-pre : {a b c : CM.ob} {z : CM.Hom[ a , b ]} {f g : CM.Hom[ b , c ]}
             → isIso CM.C z → z CM.⋆ f ≡ z CM.⋆ g → f ≡ g
  cancel-pre {z = z} {f = f} {g = g} zi p =
      sym (CM.⋆IdL f)
    ∙ cong (CM._⋆ f) (sym (isIso.sec zi))
    ∙ CM.⋆Assoc (isIso.inv zi) z f
    ∙ cong (isIso.inv zi CM.⋆_) p
    ∙ sym (CM.⋆Assoc (isIso.inv zi) z g)
    ∙ cong (CM._⋆ g) (isIso.sec zi)
    ∙ CM.⋆IdL g

  -- delta . F1 etaSigma == (gammaInv ox id) . etaC, gamma-left rearranged
  δF₁ηΣ-eq : (w : ΣM.ob)
           → δ⟨ ΣM.unit , w ⟩ CM.⋆ F₁ (ΣM.η⟨ w ⟩)
           ≡ (γ⁻¹ CM.⊗ₕ CM.id) CM.⋆ CM.η⟨ F₀ w ⟩
  δF₁ηΣ-eq w =
      sym (CM.⋆IdL _)
    ∙ cong (CM._⋆ (δ⟨ ΣM.unit , w ⟩ CM.⋆ F₁ (ΣM.η⟨ w ⟩))) (sym γ⊗-sec)
    ∙ CM.⋆Assoc (γ⁻¹ CM.⊗ₕ CM.id) (γ CM.⊗ₕ CM.id) (δ⟨ ΣM.unit , w ⟩ CM.⋆ F₁ (ΣM.η⟨ w ⟩))
    ∙ cong ((γ⁻¹ CM.⊗ₕ CM.id) CM.⋆_) (γ-left w)
    where
    γ⊗-sec : (γ⁻¹ CM.⊗ₕ CM.id) CM.⋆ (γ CM.⊗ₕ CM.id) ≡ CM.id
    γ⊗-sec = ⊗C-seq _ _ _ _ ∙ cong₂ CM._⊗ₕ_ γ-sec (CM.⋆IdL _) ∙ ⊗C-id

  -- delta . F1 rhoSigma == (id ox gammaInv) . rhoC, gamma-right rearranged
  δF₁ρΣ-eq : (w : ΣM.ob)
           → δ⟨ w , ΣM.unit ⟩ CM.⋆ F₁ (ΣM.ρ⟨ w ⟩)
           ≡ (CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ F₀ w ⟩
  δF₁ρΣ-eq w =
      sym (CM.⋆IdL _)
    ∙ cong (CM._⋆ (δ⟨ w , ΣM.unit ⟩ CM.⋆ F₁ (ΣM.ρ⟨ w ⟩))) (sym id⊗γ-sec)
    ∙ CM.⋆Assoc (CM.id CM.⊗ₕ γ⁻¹) (CM.id CM.⊗ₕ γ) (δ⟨ w , ΣM.unit ⟩ CM.⋆ F₁ (ΣM.ρ⟨ w ⟩))
    ∙ cong ((CM.id CM.⊗ₕ γ⁻¹) CM.⋆_) (γ-right w)
    where
    id⊗γ-sec : (CM.id CM.⊗ₕ γ⁻¹) CM.⋆ (CM.id CM.⊗ₕ γ) ≡ CM.id
    id⊗γ-sec = ⊗C-seq _ _ _ _ ∙ cong₂ CM._⊗ₕ_ (CM.⋆IdL _) γ-sec ∙ ⊗C-id

  -- F1 etaSigma = deltaInv . ((gammaInv ox id) . etaC)
  F₁ηΣ-eq : (w : ΣM.ob)
          → F₁ (ΣM.η⟨ w ⟩) ≡ δ⁻¹⟨ ΣM.unit , w ⟩ CM.⋆ ((γ⁻¹ CM.⊗ₕ CM.id) CM.⋆ CM.η⟨ F₀ w ⟩)
  F₁ηΣ-eq w =
      sym (CM.⋆IdL _)
    ∙ cong (CM._⋆ F₁ (ΣM.η⟨ w ⟩)) (sym (δ-sec _ _))
    ∙ CM.⋆Assoc δ⁻¹⟨ ΣM.unit , w ⟩ δ⟨ ΣM.unit , w ⟩ (F₁ (ΣM.η⟨ w ⟩))
    ∙ cong (δ⁻¹⟨ ΣM.unit , w ⟩ CM.⋆_) (δF₁ηΣ-eq w)

  -- F1 rhoSigma = deltaInv . ((id ox gammaInv) . rhoC)
  F₁ρΣ-eq : (w : ΣM.ob)
          → F₁ (ΣM.ρ⟨ w ⟩) ≡ δ⁻¹⟨ w , ΣM.unit ⟩ CM.⋆ ((CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ F₀ w ⟩)
  F₁ρΣ-eq w =
      sym (CM.⋆IdL _)
    ∙ cong (CM._⋆ F₁ (ΣM.ρ⟨ w ⟩)) (sym (δ-sec _ _))
    ∙ CM.⋆Assoc δ⁻¹⟨ w , ΣM.unit ⟩ δ⟨ w , ΣM.unit ⟩ (F₁ (ΣM.ρ⟨ w ⟩))
    ∙ cong (δ⁻¹⟨ w , ΣM.unit ⟩ CM.⋆_) (δF₁ρΣ-eq w)

  ----------------------------------------------------------------------
  -- kellyρ: the right-unit Kelly coherence (mirror of kellyλ,
  -- upstream candidate).  alpha<x,y,1> . rho<x ox y> == id ox rho<y>,
  -- from the pentagon, the triangle, and naturality alone.
  ----------------------------------------------------------------------

  ρ-cancel : {a b : CM.ob} (f g : CM.Hom[ a , b ])
           → (f CM.⊗ₕ CM.id {CM.unit}) ≡ (g CM.⊗ₕ CM.id {CM.unit}) → f ≡ g
  ρ-cancel {a} {b} f g p =
      sym (CM.⋆IdL f)
    ∙ cong (CM._⋆ f) (sym (CM.ρ .NatIso.nIso a .isIso.sec))
    ∙ CM.⋆Assoc CM.ρ⁻¹⟨ a ⟩ CM.ρ⟨ a ⟩ f
    ∙ cong (CM.ρ⁻¹⟨ a ⟩ CM.⋆_)
        (sym (ρC-nat f) ∙ cong (CM._⋆ CM.ρ⟨ b ⟩) p ∙ ρC-nat g)
    ∙ sym (CM.⋆Assoc CM.ρ⁻¹⟨ a ⟩ CM.ρ⟨ a ⟩ g)
    ∙ cong (CM._⋆ g) (CM.ρ .NatIso.nIso a .isIso.sec)
    ∙ CM.⋆IdL g

  kellyρ : (x y : CM.ob)
         → CM.α⟨ x , y , CM.unit ⟩ CM.⋆ CM.ρ⟨ x ⊗C y ⟩ ≡ CM.id {x} CM.⊗ₕ CM.ρ⟨ y ⟩
  kellyρ x y = ρ-cancel _ _ chain
    where
    a1 = CM.α⟨ x , y , CM.unit ⟩
    aX = CM.α⟨ x , y CM.⊗ CM.unit , CM.unit ⟩
    aX⁻¹ = CM.α⁻¹⟨ x , y CM.⊗ CM.unit , CM.unit ⟩
    aQ = CM.α⟨ x , y , CM.unit CM.⊗ CM.unit ⟩
    aR = CM.α⟨ x CM.⊗ y , CM.unit , CM.unit ⟩
    idα = CM.id {x} CM.⊗ₕ CM.α⟨ y , CM.unit , CM.unit ⟩
    idα-inv = CM.id {x} CM.⊗ₕ CM.α⁻¹⟨ y , CM.unit , CM.unit ⟩
    ρXY = CM.ρ⟨ x CM.⊗ y ⟩

    idα-sec' : idα-inv CM.⋆ idα ≡ CM.id
    idα-sec' = id⊗Cs _ _ ∙ cong (CM.id CM.⊗ₕ_) (α-secC _ _ _) ∙ ⊗C-id

    -- the pentagon at (x, y, unit, unit), solved for (a1 ox id)
    pentSolve : (a1 CM.⊗ₕ CM.id) ≡ aX⁻¹ CM.⋆ (idα-inv CM.⋆ (aQ CM.⋆ aR))
    pentSolve = sym expand
      where
      expand : aX⁻¹ CM.⋆ (idα-inv CM.⋆ (aQ CM.⋆ aR)) ≡ (a1 CM.⊗ₕ CM.id)
      expand =
          cong (λ t → aX⁻¹ CM.⋆ (idα-inv CM.⋆ t)) (sym (CM.pentagon x y CM.unit CM.unit))
        ∙ cong (aX⁻¹ CM.⋆_) (sym (CM.⋆Assoc idα-inv idα (aX CM.⋆ (a1 CM.⊗ₕ CM.id))))
        ∙ cong (aX⁻¹ CM.⋆_) (sym (CM.⋆Assoc (idα-inv CM.⋆ idα) aX (a1 CM.⊗ₕ CM.id)))
        ∙ sym (CM.⋆Assoc aX⁻¹ ((idα-inv CM.⋆ idα) CM.⋆ aX) (a1 CM.⊗ₕ CM.id))
        ∙ cong (CM._⋆ (a1 CM.⊗ₕ CM.id)) (
            cong (aX⁻¹ CM.⋆_) (cong (CM._⋆ aX) idα-sec' ∙ CM.⋆IdL aX)
          ∙ α-secC _ _ _)
        ∙ CM.⋆IdL (a1 CM.⊗ₕ CM.id)

    stepN : aQ CM.⋆ ((CM.id {x CM.⊗ y}) CM.⊗ₕ CM.η⟨ CM.unit ⟩)
          ≡ (CM.id {x} CM.⊗ₕ (CM.id {y} CM.⊗ₕ CM.η⟨ CM.unit ⟩)) CM.⋆ a1
    stepN =
        cong (aQ CM.⋆_) (cong (CM._⊗ₕ CM.η⟨ CM.unit ⟩) (sym ⊗C-id))
      ∙ sym (αC-nat CM.id CM.id CM.η⟨ CM.unit ⟩)

    stepA : (idα-inv CM.⋆ (aQ CM.⋆ aR)) CM.⋆ (ρXY CM.⊗ₕ CM.id)
          ≡ idα-inv CM.⋆ ((CM.id {x} CM.⊗ₕ (CM.id {y} CM.⊗ₕ CM.η⟨ CM.unit ⟩)) CM.⋆ a1)
    stepA =
        CM.⋆Assoc idα-inv (aQ CM.⋆ aR) (ρXY CM.⊗ₕ CM.id)
      ∙ cong (idα-inv CM.⋆_) (
          CM.⋆Assoc aQ aR (ρXY CM.⊗ₕ CM.id)
        ∙ cong (aQ CM.⋆_) (CM.triangle (x CM.⊗ y) CM.unit)
        ∙ stepN)

    stepB : idα-inv CM.⋆ ((CM.id {x} CM.⊗ₕ (CM.id {y} CM.⊗ₕ CM.η⟨ CM.unit ⟩)) CM.⋆ a1)
          ≡ idα-inv CM.⋆ (idα CM.⋆ ((CM.id {x} CM.⊗ₕ (CM.ρ⟨ y ⟩ CM.⊗ₕ CM.id)) CM.⋆ a1))
    stepB = cong (idα-inv CM.⋆_) (
        cong (CM._⋆ a1) (
            cong (CM.id CM.⊗ₕ_) (sym (CM.triangle y CM.unit))
          ∙ sym (id⊗Cs CM.α⟨ y , CM.unit , CM.unit ⟩ (CM.ρ⟨ y ⟩ CM.⊗ₕ CM.id)))
      ∙ CM.⋆Assoc idα (CM.id CM.⊗ₕ (CM.ρ⟨ y ⟩ CM.⊗ₕ CM.id)) a1)

    stepC : aX⁻¹ CM.⋆ ((CM.id {x} CM.⊗ₕ (CM.ρ⟨ y ⟩ CM.⊗ₕ CM.id)) CM.⋆ a1)
          ≡ aX⁻¹ CM.⋆ (aX CM.⋆ ((CM.id {x} CM.⊗ₕ CM.ρ⟨ y ⟩) CM.⊗ₕ CM.id))
    stepC = cong (aX⁻¹ CM.⋆_) (αC-nat CM.id CM.ρ⟨ y ⟩ CM.id)

    chain : (a1 CM.⋆ ρXY) CM.⊗ₕ CM.id
          ≡ (CM.id {x} CM.⊗ₕ CM.ρ⟨ y ⟩) CM.⊗ₕ CM.id
    chain =
        cong ((a1 CM.⋆ ρXY) CM.⊗ₕ_) (sym (CM.⋆IdL CM.id))
      ∙ sym (⊗C-seq a1 ρXY CM.id CM.id)
      ∙ cong (CM._⋆ (ρXY CM.⊗ₕ CM.id)) pentSolve
      ∙ CM.⋆Assoc aX⁻¹ (idα-inv CM.⋆ (aQ CM.⋆ aR)) (ρXY CM.⊗ₕ CM.id)
      ∙ cong (aX⁻¹ CM.⋆_) stepA
      ∙ cong (aX⁻¹ CM.⋆_) stepB
      ∙ cong (aX⁻¹ CM.⋆_) (sym (CM.⋆Assoc idα-inv idα
          ((CM.id CM.⊗ₕ (CM.ρ⟨ y ⟩ CM.⊗ₕ CM.id)) CM.⋆ a1)))
      ∙ cong (aX⁻¹ CM.⋆_) (cong (CM._⋆ ((CM.id CM.⊗ₕ (CM.ρ⟨ y ⟩ CM.⊗ₕ CM.id)) CM.⋆ a1))
          idα-sec' ∙ CM.⋆IdL _)
      ∙ stepC
      ∙ sym (CM.⋆Assoc aX⁻¹ aX ((CM.id CM.⊗ₕ CM.ρ⟨ y ⟩) CM.⊗ₕ CM.id))
      ∙ cong (CM._⋆ ((CM.id CM.⊗ₕ CM.ρ⟨ y ⟩) CM.⊗ₕ CM.id)) (α-secC _ _ _)
      ∙ CM.⋆IdL _

  ----------------------------------------------------------------------
  -- Representatives, the step relation, the quotient
  ----------------------------------------------------------------------

  Repr : (A B : CM.ob) → Type (ℓ-max ℓΣ ℓC')
  Repr A B = Σ[ w ∈ ΣM.ob ] CM.Hom[ A ⊗C F₀ w , B ]

  PStep : (A B : CM.ob) → Repr A B → Repr A B → Type (ℓ-max ℓΣ' ℓC')
  PStep A B (w , f) (w' , f') =
    Σ[ h ∈ ΣM.Hom[ w , w' ] ] (f ≡ (CM.id CM.⊗ₕ F₁ h) CM.⋆ f')

  PQuot : (A B : CM.ob) → Type (ℓ-max (ℓ-max ℓΣ ℓC') (ℓ-max ℓΣ' ℓC'))
  PQuot A B = ZigZagQuotient (PStep A B)

  compPCore : {A B C : CM.ob} → Repr B C → Repr A B → Repr A C
  compPCore {A} (v , g) (w , f) =
    (w ⊗Σ v) ,
    ((CM.id CM.⊗ₕ δ⁻¹⟨ w , v ⟩) CM.⋆ CM.α⟨ A , F₀ w , F₀ v ⟩ CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ g))

  idRepr : (A : CM.ob) → Repr A A
  idRepr A = (ΣM.unit , (CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ A ⟩)

  ----------------------------------------------------------------------
  -- Congruence in each factor
  ----------------------------------------------------------------------

  -- Vary the first factor (A -> B): mediator h ox id.
  compPL-step : {A B C : CM.ob} {x x' : Repr A B} (y : Repr B C)
              → PStep A B x x'
              → PStep A C (compPCore y x) (compPCore y x')
  compPL-step {A} {B} {C} {w , f} {w' , f'} (v , g) (h , e) =
    (h ΣM.⊗ₕ ΣM.id) , eq
    where
    eq : (CM.id CM.⊗ₕ δ⁻¹⟨ w , v ⟩) CM.⋆ CM.α⟨ A , F₀ w , F₀ v ⟩ CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ g)
       ≡ (CM.id CM.⊗ₕ F₁ (h ΣM.⊗ₕ ΣM.id))
           CM.⋆ ((CM.id CM.⊗ₕ δ⁻¹⟨ w' , v ⟩) CM.⋆ CM.α⟨ A , F₀ w' , F₀ v ⟩ CM.⋆ ((f' CM.⊗ₕ CM.id) CM.⋆ g))
    eq =
        cong (λ t → P1 CM.⋆ (α CM.⋆ ((t CM.⊗ₕ CM.id) CM.⋆ g))) e
      ∙ cong (λ t → P1 CM.⋆ (α CM.⋆ (t CM.⋆ g))) (
            cong (((CM.id CM.⊗ₕ F₁ h) CM.⋆ f') CM.⊗ₕ_) (sym (CM.⋆IdL CM.id))
          ∙ sym (⊗C-seq (CM.id CM.⊗ₕ F₁ h) f' CM.id CM.id))
      -- P1 ⋆ (α ⋆ ((X ⋆ (f'⊗ₕid)) ⋆ g))
      ∙ cong (P1 CM.⋆_) (cong (α CM.⋆_) (CM.⋆Assoc X (f' CM.⊗ₕ CM.id) g))
      -- P1 ⋆ (α ⋆ (X ⋆ T))
      ∙ cong (P1 CM.⋆_) (sym (CM.⋆Assoc α X T))
      -- P1 ⋆ ((α ⋆ X) ⋆ T)
      ∙ cong (P1 CM.⋆_) (cong (CM._⋆ T) (sym (αC-nat CM.id (F₁ h) CM.id)))
      -- P1 ⋆ ((Q ⋆ α') ⋆ T)
      ∙ cong (P1 CM.⋆_) (CM.⋆Assoc Q α' T)
      -- P1 ⋆ (Q ⋆ (α' ⋆ T))
      ∙ sym (CM.⋆Assoc P1 Q (α' CM.⋆ T))
      -- ((P1 ⋆ Q) ⋆ (α' ⋆ T))
      ∙ cong (CM._⋆ (α' CM.⋆ T)) (
            cong (λ t → (CM.id CM.⊗ₕ δ⁻¹⟨ w , v ⟩) CM.⋆ (CM.id CM.⊗ₕ (F₁ h CM.⊗ₕ t))) (sym F-id)
          ∙ id⊗Cs δ⁻¹⟨ w , v ⟩ (F₁ h CM.⊗ₕ F₁ ΣM.id)
          ∙ cong (CM.id CM.⊗ₕ_) (δ⁻¹-nat h ΣM.id)
          ∙ sym (id⊗Cs (F₁ (h ΣM.⊗ₕ ΣM.id)) δ⁻¹⟨ w' , v ⟩))
      -- ((P' ⋆ Q') ⋆ (α' ⋆ T))
      ∙ CM.⋆Assoc (CM.id CM.⊗ₕ F₁ (h ΣM.⊗ₕ ΣM.id)) (CM.id CM.⊗ₕ δ⁻¹⟨ w' , v ⟩) (α' CM.⋆ T)
      where
      P1 = CM.id CM.⊗ₕ δ⁻¹⟨ w , v ⟩
      Q = CM.id CM.⊗ₕ (F₁ h CM.⊗ₕ CM.id)
      α = CM.α⟨ A , F₀ w , F₀ v ⟩
      α' = CM.α⟨ A , F₀ w' , F₀ v ⟩
      X = (CM.id CM.⊗ₕ F₁ h) CM.⊗ₕ CM.id
      T = (f' CM.⊗ₕ CM.id) CM.⋆ g

  -- Vary the second factor (B -> C): mediator id ox h.
  compPR-step : {A B C : CM.ob} {y y' : Repr B C} (x : Repr A B)
              → PStep B C y y'
              → PStep A C (compPCore y x) (compPCore y' x)
  compPR-step {A} {B} {C} {v , g} {v' , g'} (w , f) (h₂ , e₂) =
    (ΣM.id ΣM.⊗ₕ h₂) , eq
    where
    -- (f ⊗ₕ id) ⋆ (id ⊗ₕ F₁h₂) ≡ (id ⊗ₕ F₁h₂) ⋆ (f ⊗ₕ id), both = f ⊗ₕ F₁h₂
    interL : (f CM.⊗ₕ CM.id {F₀ v}) CM.⋆ (CM.id {B} CM.⊗ₕ F₁ h₂)
           ≡ (CM.id {A CM.⊗ F₀ w} CM.⊗ₕ F₁ h₂) CM.⋆ (f CM.⊗ₕ CM.id {F₀ v'})
    interL =
        ⊗C-seq f (CM.id {B}) (CM.id {F₀ v}) (F₁ h₂)
      ∙ cong₂ CM._⊗ₕ_ (CM.⋆IdR f) (CM.⋆IdL (F₁ h₂))
      ∙ sym (cong₂ CM._⊗ₕ_ (CM.⋆IdL f) (CM.⋆IdR (F₁ h₂)))
      ∙ sym (⊗C-seq (CM.id {A CM.⊗ F₀ w}) f (F₁ h₂) (CM.id {F₀ v'}))
    eq : (CM.id CM.⊗ₕ δ⁻¹⟨ w , v ⟩) CM.⋆ CM.α⟨ A , F₀ w , F₀ v ⟩ CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ g)
       ≡ (CM.id CM.⊗ₕ F₁ (ΣM.id ΣM.⊗ₕ h₂))
           CM.⋆ ((CM.id CM.⊗ₕ δ⁻¹⟨ w , v' ⟩) CM.⋆ CM.α⟨ A , F₀ w , F₀ v' ⟩ CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ g'))
    eq =
        cong (λ t → P1 CM.⋆ (α CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ t))) e₂
      -- P1 ⋆ (α ⋆ ((f⊗id) ⋆ ((id⊗F₁h₂) ⋆ g')))
      ∙ cong (P1 CM.⋆_) (cong (α CM.⋆_) (
            sym (CM.⋆Assoc (f CM.⊗ₕ CM.id) (CM.id CM.⊗ₕ F₁ h₂) g')
          ∙ cong (CM._⋆ g') interL
          ∙ CM.⋆Assoc (CM.id CM.⊗ₕ F₁ h₂) (f CM.⊗ₕ CM.id) g'))
      -- P1 ⋆ (α ⋆ ((id⊗F₁h₂) ⋆ T))
      ∙ cong (P1 CM.⋆_) (
          sym (CM.⋆Assoc α (CM.id {A CM.⊗ F₀ w} CM.⊗ₕ F₁ h₂) T)
        ∙ cong (CM._⋆ T) (
            cong (α CM.⋆_) (cong (CM._⊗ₕ F₁ h₂) (sym ⊗C-id))
          ∙ sym (αC-nat CM.id CM.id (F₁ h₂)))
        ∙ CM.⋆Assoc (CM.id CM.⊗ₕ (CM.id CM.⊗ₕ F₁ h₂)) α' T)
      -- P1 ⋆ (Q ⋆ (α' ⋆ T))
      ∙ sym (CM.⋆Assoc P1 Q (α' CM.⋆ T))
      -- ((P1 ⋆ Q) ⋆ (α' ⋆ T))
      ∙ cong (CM._⋆ (α' CM.⋆ T)) (
            cong (λ t → (CM.id CM.⊗ₕ δ⁻¹⟨ w , v ⟩) CM.⋆ (CM.id CM.⊗ₕ (t CM.⊗ₕ F₁ h₂))) (sym F-id)
          ∙ id⊗Cs δ⁻¹⟨ w , v ⟩ (F₁ ΣM.id CM.⊗ₕ F₁ h₂)
          ∙ cong (CM.id CM.⊗ₕ_) (δ⁻¹-nat ΣM.id h₂)
          ∙ sym (id⊗Cs (F₁ (ΣM.id ΣM.⊗ₕ h₂)) δ⁻¹⟨ w , v' ⟩))
      -- ((P' ⋆ Q') ⋆ (α' ⋆ T))
      ∙ CM.⋆Assoc (CM.id CM.⊗ₕ F₁ (ΣM.id ΣM.⊗ₕ h₂)) (CM.id CM.⊗ₕ δ⁻¹⟨ w , v' ⟩) (α' CM.⋆ T)
      where
      P1 = CM.id CM.⊗ₕ δ⁻¹⟨ w , v ⟩
      Q = CM.id CM.⊗ₕ (CM.id CM.⊗ₕ F₁ h₂)
      α = CM.α⟨ A , F₀ w , F₀ v ⟩
      α' = CM.α⟨ A , F₀ w , F₀ v' ⟩
      T = (f CM.⊗ₕ CM.id) CM.⋆ g'

  ----------------------------------------------------------------------
  -- Composition descends to the quotient
  ----------------------------------------------------------------------

  mapFenceP : {ℓa ℓb ℓr ℓs : Level}
            {X : Type ℓa} {Y : Type ℓb}
            {R : X → X → Type ℓr} {S : Y → Y → Type ℓs}
            (f : X → Y)
          → (∀ {x x'} → R x x' → S (f x) (f x'))
          → ∀ {x x'} → ZigZag R x x' → ZigZag S (f x) (f x')
  mapFenceP f h zz-refl        = zz-refl
  mapFenceP f h (zz-step st)   = zz-step (h st)
  mapFenceP f h (zz-back st)   = zz-back (h st)
  mapFenceP f h (zz-trans p q) =
    zz-trans (mapFenceP f h p) (mapFenceP f h q)

  compPQuot : {A B C : CM.ob} → PQuot A B → PQuot B C → PQuot A C
  compPQuot {A} {B} {C} = SQ.rec2 squash/ (λ x y → [ compPCore y x ])
    (λ x x' y zz → eq/ _ _
      (mapFenceP (compPCore y) (λ {a} {b} st → compPL-step y st) zz))
    (λ x y y' zz → eq/ _ _
      (mapFenceP (λ v → compPCore v x)
        (λ {a} {b} st → compPR-step x st) zz))

  ----------------------------------------------------------------------
  -- Unit law steps
  ----------------------------------------------------------------------

  -- id . x ~ x : mediator etaSigma<w>.
  idlStepP : {A B : CM.ob} (x : Repr A B)
           → PStep A B (compPCore x (idRepr A)) x
  idlStepP {A} {B} (w , f) = ΣM.η⟨ w ⟩ , eq
    where
    P = CM.id {A} CM.⊗ₕ δ⁻¹⟨ ΣM.unit , w ⟩
    α = CM.α⟨ A , F₀ ΣM.unit , F₀ w ⟩
    R = ((CM.id {A} CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ A ⟩)
          CM.⊗ₕ CM.id {F₀ w}
    Q = CM.id {A} CM.⊗ₕ
          ((γ⁻¹ CM.⊗ₕ CM.id {F₀ w}) CM.⋆ CM.η⟨ F₀ w ⟩)

    core-eq : α CM.⋆ R ≡ Q
    rhs-to-lhs : (CM.id CM.⊗ₕ F₁ (ΣM.η⟨ w ⟩)) CM.⋆ f
               ≡ P CM.⋆ α CM.⋆ (R CM.⋆ f)
    eq : (CM.id CM.⊗ₕ δ⁻¹⟨ ΣM.unit , w ⟩) CM.⋆ CM.α⟨ A , F₀ ΣM.unit , F₀ w ⟩
           CM.⋆ ((((CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ A ⟩) CM.⊗ₕ CM.id) CM.⋆ f)
       ≡ (CM.id CM.⊗ₕ F₁ (ΣM.η⟨ w ⟩)) CM.⋆ f
    eq = sym rhs-to-lhs

    rhs-to-lhs =
        cong (λ t → (CM.id {A} CM.⊗ₕ t) CM.⋆ f) (F₁ηΣ-eq w)
      ∙ cong (CM._⋆ f) (sym (id⊗Cs _ _))
      ∙ CM.⋆Assoc P Q f
      ∙ cong (P CM.⋆_) (cong (CM._⋆ f) (sym core-eq))
      ∙ cong (P CM.⋆_) (CM.⋆Assoc α R f)

    core-eq =
          cong (α CM.⋆_) (
              cong ((((CM.id {A} CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ A ⟩) CM.⊗ₕ_))
                (sym (CM.⋆IdR (CM.id {F₀ w})))
            ∙ sym (⊗C-seq (CM.id {A} CM.⊗ₕ γ⁻¹) CM.ρ⟨ A ⟩
                    (CM.id {F₀ w}) (CM.id {F₀ w})))
        ∙ sym (CM.⋆Assoc α
            ((CM.id {A} CM.⊗ₕ γ⁻¹) CM.⊗ₕ CM.id {F₀ w})
            (CM.ρ⟨ A ⟩ CM.⊗ₕ CM.id {F₀ w}))
        ∙ cong (CM._⋆ (CM.ρ⟨ A ⟩ CM.⊗ₕ CM.id {F₀ w}))
            (sym (αC-nat (CM.id {A}) γ⁻¹ (CM.id {F₀ w})))
        ∙ CM.⋆Assoc
            (CM.id {A} CM.⊗ₕ (γ⁻¹ CM.⊗ₕ CM.id {F₀ w}))
            CM.α⟨ A , CM.unit , F₀ w ⟩
            (CM.ρ⟨ A ⟩ CM.⊗ₕ CM.id {F₀ w})
        ∙ cong ((CM.id {A} CM.⊗ₕ (γ⁻¹ CM.⊗ₕ CM.id {F₀ w})) CM.⋆_)
            (CM.triangle A (F₀ w))
        ∙ id⊗Cs _ _

  -- x . id ~ x : mediator rhoSigma<w>.
  idrStepP : {A B : CM.ob} (x : Repr A B)
           → PStep A B (compPCore (idRepr B) x) x
  idrStepP {A} {B} (w , f) = ΣM.ρ⟨ w ⟩ , eq
    where
    P = CM.id {A} CM.⊗ₕ δ⁻¹⟨ w , ΣM.unit ⟩
    α₀ = CM.α⟨ A , F₀ w , F₀ ΣM.unit ⟩
    αI = CM.α⟨ A , F₀ w , CM.unit ⟩
    X = CM.id {A CM.⊗ F₀ w} CM.⊗ₕ γ⁻¹
    Q₀ = CM.id {A} CM.⊗ₕ (CM.id {F₀ w} CM.⊗ₕ γ⁻¹)
    S = (CM.id {B} CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ B ⟩
    L = α₀ CM.⋆ ((f CM.⊗ₕ CM.id {F₀ ΣM.unit}) CM.⋆ S)
    Q = CM.id {A} CM.⊗ₕ
          ((CM.id {F₀ w} CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ F₀ w ⟩)

    inter : (f CM.⊗ₕ CM.id {F₀ ΣM.unit})
              CM.⋆ (CM.id {B} CM.⊗ₕ γ⁻¹)
          ≡ X CM.⋆ (f CM.⊗ₕ CM.id {CM.unit})
    core-eq : L ≡ Q CM.⋆ f
    rhs-to-lhs : (CM.id {A} CM.⊗ₕ F₁ (ΣM.ρ⟨ w ⟩)) CM.⋆ f
               ≡ P CM.⋆ L
    eq : (CM.id CM.⊗ₕ δ⁻¹⟨ w , ΣM.unit ⟩) CM.⋆ CM.α⟨ A , F₀ w , F₀ ΣM.unit ⟩
           CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ ((CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ B ⟩))
       ≡ (CM.id CM.⊗ₕ F₁ (ΣM.ρ⟨ w ⟩)) CM.⋆ f
    eq = sym rhs-to-lhs

    rhs-to-lhs =
        cong (λ t → (CM.id {A} CM.⊗ₕ t) CM.⋆ f) (F₁ρΣ-eq w)
      ∙ cong (CM._⋆ f) (sym (id⊗Cs _ _))
      ∙ CM.⋆Assoc P Q f
      ∙ cong (P CM.⋆_) (sym core-eq)

    inter =
        ⊗C-seq f (CM.id {B}) (CM.id {F₀ ΣM.unit}) γ⁻¹
      ∙ cong₂ CM._⊗ₕ_ (CM.⋆IdR f) (CM.⋆IdL γ⁻¹)
      ∙ sym (cong₂ CM._⊗ₕ_ (CM.⋆IdL f) (CM.⋆IdR γ⁻¹))
      ∙ sym (⊗C-seq (CM.id {A CM.⊗ F₀ w}) f γ⁻¹
              (CM.id {CM.unit}))

    core-eq =
        cong (α₀ CM.⋆_) (
            sym (CM.⋆Assoc (f CM.⊗ₕ CM.id {F₀ ΣM.unit})
                  (CM.id {B} CM.⊗ₕ γ⁻¹) CM.ρ⟨ B ⟩)
          ∙ cong (CM._⋆ CM.ρ⟨ B ⟩) inter
          ∙ CM.⋆Assoc X (f CM.⊗ₕ CM.id {CM.unit}) CM.ρ⟨ B ⟩
          ∙ cong (X CM.⋆_) (ρC-nat f))
      ∙ sym (CM.⋆Assoc α₀ X (CM.ρ⟨ A CM.⊗ F₀ w ⟩ CM.⋆ f))
      ∙ cong (CM._⋆ (CM.ρ⟨ A CM.⊗ F₀ w ⟩ CM.⋆ f)) (
          cong (α₀ CM.⋆_)
            (cong (CM._⊗ₕ γ⁻¹) (sym ⊗C-id))
        ∙ sym (αC-nat (CM.id {A}) (CM.id {F₀ w}) γ⁻¹))
      ∙ CM.⋆Assoc Q₀ αI (CM.ρ⟨ A CM.⊗ F₀ w ⟩ CM.⋆ f)
      ∙ cong (Q₀ CM.⋆_) (
          sym (CM.⋆Assoc αI CM.ρ⟨ A CM.⊗ F₀ w ⟩ f)
        ∙ cong (CM._⋆ f) (kellyρ A (F₀ w)))
      ∙ sym (CM.⋆Assoc Q₀
          (CM.id {A} CM.⊗ₕ CM.ρ⟨ F₀ w ⟩) f)
      ∙ cong (CM._⋆ f) (id⊗Cs _ _)

  ----------------------------------------------------------------------
  -- Associativity law step (delta-assocInv + pentagon + naturality)
  ----------------------------------------------------------------------

  -- the inverse form of delta-assoc (derived via cancel-post twice)
  δA : (w₁ w₂ w₃ : ΣM.ob)
     → δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩ CM.⋆ (CM.id CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩) CM.⋆ CM.α⟨ F₀ w₁ , F₀ w₂ , F₀ w₃ ⟩
     ≡ F₁ (ΣM.α⟨ w₁ , w₂ , w₃ ⟩) CM.⋆ δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩ CM.⋆ (δ⁻¹⟨ w₁ , w₂ ⟩ CM.⊗ₕ CM.id)
  δA w₁ w₂ w₃ =
    cancel-post z₁-iso (cancel-post (δ-iso (w₁ ⊗Σ w₂) w₃) goal)
    where
    αΣ = ΣM.α⟨ w₁ , w₂ , w₃ ⟩
    αΣ⁻¹ = ΣM.α⁻¹⟨ w₁ , w₂ , w₃ ⟩
    Fα = F₁ αΣ
    Fα⁻¹ = F₁ αΣ⁻¹

    z₁ = δ⟨ w₁ , w₂ ⟩ CM.⊗ₕ CM.id {F₀ w₃}
    z₁⁻¹ = δ⁻¹⟨ w₁ , w₂ ⟩ CM.⊗ₕ CM.id {F₀ w₃}
    z₂ = δ⟨ w₁ ⊗Σ w₂ , w₃ ⟩
    z₂⁻¹ = δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩

    d₂₃ = CM.id {F₀ w₁} CM.⊗ₕ δ⟨ w₂ , w₃ ⟩
    d₂₃⁻¹ = CM.id {F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩
    d₁₂₃ = δ⟨ w₁ , w₂ ⊗Σ w₃ ⟩
    d₁₂₃⁻¹ = δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩
    αC = CM.α⟨ F₀ w₁ , F₀ w₂ , F₀ w₃ ⟩
    αC⁻¹ = CM.α⁻¹⟨ F₀ w₁ , F₀ w₂ , F₀ w₃ ⟩

    forward = αC⁻¹ CM.⋆ (d₂₃ CM.⋆ d₁₂₃)
    leftInv = d₁₂₃⁻¹ CM.⋆ (d₂₃⁻¹ CM.⋆ αC)
    rightInv = Fα CM.⋆ (z₂⁻¹ CM.⋆ z₁⁻¹)
    leftPost = (leftInv CM.⋆ z₁) CM.⋆ z₂
    rightPost = (rightInv CM.⋆ z₁) CM.⋆ z₂

    z₁-iso : isIso CM.C z₁
    z₁-iso = record
      { inv = z₁⁻¹
      ; sec =
          ⊗C-seq δ⁻¹⟨ w₁ , w₂ ⟩ δ⟨ w₁ , w₂ ⟩
            (CM.id {F₀ w₃}) (CM.id {F₀ w₃})
        ∙ cong₂ CM._⊗ₕ_ (δ-sec w₁ w₂) (CM.⋆IdL (CM.id {F₀ w₃}))
        ∙ ⊗C-id
      ; ret =
          ⊗C-seq δ⟨ w₁ , w₂ ⟩ δ⁻¹⟨ w₁ , w₂ ⟩
            (CM.id {F₀ w₃}) (CM.id {F₀ w₃})
        ∙ cong₂ CM._⊗ₕ_ (δ-ret w₁ w₂) (CM.⋆IdL (CM.id {F₀ w₃}))
        ∙ ⊗C-id }

    αΣ-ret : αΣ ΣM.⋆ αΣ⁻¹ ≡ ΣM.id
    αΣ-ret = ΣM.α .NatIso.nIso (w₁ , w₂ , w₃) .isIso.ret

    αΣ-sec : αΣ⁻¹ ΣM.⋆ αΣ ≡ ΣM.id
    αΣ-sec = ΣM.α .NatIso.nIso (w₁ , w₂ , w₃) .isIso.sec

    Fα⁻¹-iso : isIso CM.C Fα⁻¹
    Fα⁻¹-iso = record
      { inv = Fα
      ; sec =
          sym (F-seq αΣ αΣ⁻¹)
        ∙ cong F₁ αΣ-ret
        ∙ F-id
      ; ret =
          sym (F-seq αΣ⁻¹ αΣ)
        ∙ cong F₁ αΣ-sec
        ∙ F-id }

    d₂₃-sec : d₂₃⁻¹ CM.⋆ d₂₃ ≡ CM.id
    d₂₃-sec =
        id⊗Cs _ _
      ∙ cong (CM.id {F₀ w₁} CM.⊗ₕ_) (δ-sec w₂ w₃)
      ∙ ⊗C-id

    α-cancel : αC CM.⋆ (αC⁻¹ CM.⋆ (d₂₃ CM.⋆ d₁₂₃))
             ≡ d₂₃ CM.⋆ d₁₂₃
    α-cancel =
        sym (CM.⋆Assoc αC αC⁻¹ (d₂₃ CM.⋆ d₁₂₃))
      ∙ cong (CM._⋆ (d₂₃ CM.⋆ d₁₂₃)) (α-retC _ _ _)
      ∙ CM.⋆IdL _

    leftInv-forward : leftInv CM.⋆ forward ≡ CM.id
    leftInv-forward =
        CM.⋆Assoc d₁₂₃⁻¹ (d₂₃⁻¹ CM.⋆ αC) forward
      ∙ cong (d₁₂₃⁻¹ CM.⋆_)
          (CM.⋆Assoc d₂₃⁻¹ αC forward)
      ∙ cong (d₁₂₃⁻¹ CM.⋆_) (cong (d₂₃⁻¹ CM.⋆_) α-cancel)
      ∙ cong (d₁₂₃⁻¹ CM.⋆_)
          (sym (CM.⋆Assoc d₂₃⁻¹ d₂₃ d₁₂₃))
      ∙ cong (d₁₂₃⁻¹ CM.⋆_)
          (cong (CM._⋆ d₁₂₃) d₂₃-sec ∙ CM.⋆IdL d₁₂₃)
      ∙ δ-sec w₁ (w₂ ⊗Σ w₃)

    left-post-Fα⁻¹ : leftPost CM.⋆ Fα⁻¹ ≡ CM.id
    left-post-Fα⁻¹ =
        CM.⋆Assoc (leftInv CM.⋆ z₁) z₂ Fα⁻¹
      ∙ CM.⋆Assoc leftInv z₁ (z₂ CM.⋆ Fα⁻¹)
      ∙ cong (leftInv CM.⋆_) (sym (δ-assoc w₁ w₂ w₃))
      ∙ leftInv-forward

    left-to-Fα : leftPost ≡ Fα
    left-to-Fα = cancel-post Fα⁻¹-iso
      (left-post-Fα⁻¹ ∙ sym (isIso.sec Fα⁻¹-iso))

    right-z₁-cancel : rightInv CM.⋆ z₁
                    ≡ Fα CM.⋆ z₂⁻¹
    right-z₁-cancel =
        CM.⋆Assoc Fα (z₂⁻¹ CM.⋆ z₁⁻¹) z₁
      ∙ cong (Fα CM.⋆_) (
          CM.⋆Assoc z₂⁻¹ z₁⁻¹ z₁
        ∙ cong (z₂⁻¹ CM.⋆_) (isIso.sec z₁-iso)
        ∙ CM.⋆IdR z₂⁻¹)

    right-to-Fα : rightPost ≡ Fα
    right-to-Fα =
        cong (CM._⋆ z₂) right-z₁-cancel
      ∙ CM.⋆Assoc Fα z₂⁻¹ z₂
      ∙ cong (Fα CM.⋆_) (δ-sec (w₁ ⊗Σ w₂) w₃)
      ∙ CM.⋆IdR Fα

    goal : leftPost ≡ rightPost
    goal = left-to-Fα ∙ sym right-to-Fα

  assocStepP : {A B C D : CM.ob} (x : Repr A B) (y : Repr B C) (z : Repr C D)
             → PStep A D (compPCore (compPCore z y) x)
                         (compPCore z (compPCore y x))
  assocStepP {A} {B} {C} {D} (w₁ , f) (w₂ , g) (w₃ , h) = ΣM.α⟨ w₁ , w₂ , w₃ ⟩ , eq
    where
    Tl = (((f CM.⊗ₕ CM.id {F₀ w₂}) CM.⊗ₕ CM.id {F₀ w₃})
            CM.⋆ (g CM.⊗ₕ CM.id {F₀ w₃})) CM.⋆ h

    α₁ = CM.α⟨ A , F₀ w₁ , F₀ (w₂ ⊗Σ w₃) ⟩
    α₂ = CM.α⟨ A , F₀ w₁ , F₀ w₂ CM.⊗ F₀ w₃ ⟩
    α₃ = CM.α⟨ A CM.⊗ F₀ w₁ , F₀ w₂ , F₀ w₃ ⟩
    α₄ = CM.α⟨ A , F₀ (w₁ ⊗Σ w₂) , F₀ w₃ ⟩
    α₅ = CM.α⟨ A , F₀ w₁ , F₀ w₂ ⟩
    α₆ = CM.α⟨ A , F₀ w₁ CM.⊗ F₀ w₂ , F₀ w₃ ⟩
    αB = CM.α⟨ B , F₀ w₂ , F₀ w₃ ⟩

    stepL1 :
      (f CM.⊗ₕ CM.id {F₀ (w₂ ⊗Σ w₃)}) CM.⋆
        ((CM.id {B} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩) CM.⋆
          (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h)))
      ≡ (CM.id {A CM.⊗ F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩) CM.⋆
          ((f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) CM.⋆
            (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h)))
    stepL1 =
        sym (CM.⋆Assoc
          (f CM.⊗ₕ CM.id {F₀ (w₂ ⊗Σ w₃)})
          (CM.id {B} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)
          (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h)))
      ∙ cong (CM._⋆ (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h))) (
          ⊗C-seq f (CM.id {B}) (CM.id {F₀ (w₂ ⊗Σ w₃)})
            δ⁻¹⟨ w₂ , w₃ ⟩
        ∙ cong₂ CM._⊗ₕ_ (CM.⋆IdR f) (CM.⋆IdL _)
        ∙ sym (cong₂ CM._⊗ₕ_ (CM.⋆IdL f) (CM.⋆IdR _))
        ∙ sym (⊗C-seq (CM.id {A CM.⊗ F₀ w₁}) f
                δ⁻¹⟨ w₂ , w₃ ⟩
                (CM.id {F₀ w₂ CM.⊗ F₀ w₃})))
      ∙ CM.⋆Assoc
          (CM.id {A CM.⊗ F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)
          (f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃})
          (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h))

    stepL2 :
      α₁ CM.⋆
        ((CM.id {A CM.⊗ F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩) CM.⋆
          ((f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) CM.⋆
            (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h))))
      ≡ (CM.id {A} CM.⊗ₕ
          (CM.id {F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)) CM.⋆
          (α₂ CM.⋆
            ((f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) CM.⋆
              (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h))))
    stepL2 =
        sym (CM.⋆Assoc α₁
          (CM.id {A CM.⊗ F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)
          ((f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) CM.⋆
            (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h))))
      ∙ cong (CM._⋆
          ((f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) CM.⋆
            (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h)))) (
          cong (α₁ CM.⋆_)
            (cong (CM._⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩) (sym ⊗C-id))
        ∙ sym (αC-nat (CM.id {A}) (CM.id {F₀ w₁})
                δ⁻¹⟨ w₂ , w₃ ⟩))
      ∙ CM.⋆Assoc
          (CM.id {A} CM.⊗ₕ
            (CM.id {F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩))
          α₂
          ((f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) CM.⋆
            (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h)))

    stepL3 :
      (f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) CM.⋆
        (αB CM.⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h))
      ≡ α₃ CM.⋆ Tl
    stepL3 =
        sym (CM.⋆Assoc
          (f CM.⊗ₕ CM.id {F₀ w₂ CM.⊗ F₀ w₃}) αB
          ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h))
      ∙ cong (CM._⋆ ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h)) (
          cong (CM._⋆ αB)
            (cong (f CM.⊗ₕ_) (sym ⊗C-id))
        ∙ αC-nat f (CM.id {F₀ w₂}) (CM.id {F₀ w₃}))
      ∙ CM.⋆Assoc α₃
          ((f CM.⊗ₕ CM.id {F₀ w₂}) CM.⊗ₕ CM.id {F₀ w₃})
          ((g CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h)
      ∙ cong (α₃ CM.⋆_)
          (sym (CM.⋆Assoc
            ((f CM.⊗ₕ CM.id {F₀ w₂}) CM.⊗ₕ CM.id {F₀ w₃})
            (g CM.⊗ₕ CM.id {F₀ w₃}) h))

    P₁₂ = CM.id {A} CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⟩
    K₁₂ = (f CM.⊗ₕ CM.id {F₀ w₂}) CM.⋆ g
    P₁₂₃ = P₁₂ CM.⊗ₕ CM.id {F₀ w₃}
    α₅₃ = α₅ CM.⊗ₕ CM.id {F₀ w₃}
    F₃ = (f CM.⊗ₕ CM.id {F₀ w₂}) CM.⊗ₕ CM.id {F₀ w₃}
    g₃ = g CM.⊗ₕ CM.id {F₀ w₃}

    tensorCore :
      (P₁₂ CM.⋆ (α₅ CM.⋆ K₁₂)) CM.⊗ₕ CM.id {F₀ w₃}
      ≡ P₁₂₃ CM.⋆ (α₅₃ CM.⋆ (F₃ CM.⋆ g₃))
    tensorCore =
        split⊗id P₁₂ (α₅ CM.⋆ K₁₂)
      ∙ cong (P₁₂₃ CM.⋆_) (split⊗id α₅ K₁₂)
      ∙ cong (P₁₂₃ CM.⋆_)
          (cong (α₅₃ CM.⋆_)
            (split⊗id (f CM.⊗ₕ CM.id {F₀ w₂}) g))

    stepR1 :
      ((P₁₂ CM.⋆ (α₅ CM.⋆ K₁₂)) CM.⊗ₕ CM.id {F₀ w₃}) CM.⋆ h
      ≡ P₁₂₃ CM.⋆ (α₅₃ CM.⋆ Tl)
    stepR1 =
        cong (CM._⋆ h) tensorCore
      ∙ CM.⋆Assoc P₁₂₃ (α₅₃ CM.⋆ (F₃ CM.⋆ g₃)) h
      ∙ cong (P₁₂₃ CM.⋆_)
          (CM.⋆Assoc α₅₃ (F₃ CM.⋆ g₃) h)

    X₄ = P₁₂ CM.⊗ₕ CM.id {F₀ w₃}
    Q₄ = CM.id {A} CM.⊗ₕ
      (δ⁻¹⟨ w₁ , w₂ ⟩ CM.⊗ₕ CM.id {F₀ w₃})

    stepR2 : α₄ CM.⋆ (X₄ CM.⋆ (α₅₃ CM.⋆ Tl))
           ≡ Q₄ CM.⋆ (α₆ CM.⋆ (α₅₃ CM.⋆ Tl))
    stepR2 =
        sym (CM.⋆Assoc α₄ X₄ (α₅₃ CM.⋆ Tl))
      ∙ cong (CM._⋆ (α₅₃ CM.⋆ Tl))
          (sym (αC-nat (CM.id {A}) δ⁻¹⟨ w₁ , w₂ ⟩
                  (CM.id {F₀ w₃})))
      ∙ CM.⋆Assoc Q₄ α₆ (α₅₃ CM.⋆ Tl)

    T₆ = α₆ CM.⋆ (α₅₃ CM.⋆ Tl)
    aδ = CM.id {A} CM.⊗ₕ F₁ (ΣM.α⟨ w₁ , w₂ , w₃ ⟩)
    bδ = CM.id {A} CM.⊗ₕ δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩
    cδ = CM.id {A} CM.⊗ₕ
      (δ⁻¹⟨ w₁ , w₂ ⟩ CM.⊗ₕ CM.id {F₀ w₃})
    dδ = CM.id {A} CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩
    eδ = CM.id {A} CM.⊗ₕ
      (CM.id {F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)
    qδ = CM.id {A} CM.⊗ₕ
      CM.α⟨ F₀ w₁ , F₀ w₂ , F₀ w₃ ⟩
    leftδ = aδ CM.⋆ (bδ CM.⋆ cδ)
    rightδ = dδ CM.⋆ (eδ CM.⋆ qδ)

    δ-lift : leftδ ≡ rightδ
    δ-lift =
        id⊗Cs3 {g = A}
          (F₁ (ΣM.α⟨ w₁ , w₂ , w₃ ⟩))
          δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩
          (δ⁻¹⟨ w₁ , w₂ ⟩ CM.⊗ₕ CM.id {F₀ w₃})
      ∙ cong (CM.id {A} CM.⊗ₕ_) (sym (δA w₁ w₂ w₃))
      ∙ sym (id⊗Cs3 {g = A}
          δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩
          (CM.id {F₀ w₁} CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)
          CM.α⟨ F₀ w₁ , F₀ w₂ , F₀ w₃ ⟩)

    stepR3 : aδ CM.⋆ (bδ CM.⋆ (cδ CM.⋆ T₆))
           ≡ dδ CM.⋆ (eδ CM.⋆ (qδ CM.⋆ T₆))
    stepR3 =
        cong (aδ CM.⋆_) (sym (CM.⋆Assoc bδ cδ T₆))
      ∙ sym (CM.⋆Assoc aδ (bδ CM.⋆ cδ) T₆)
      ∙ cong (CM._⋆ T₆) δ-lift
      ∙ CM.⋆Assoc dδ (eδ CM.⋆ qδ) T₆
      ∙ cong (dδ CM.⋆_) (CM.⋆Assoc eδ qδ T₆)

    stepR4 : qδ CM.⋆ (α₆ CM.⋆ (α₅₃ CM.⋆ Tl))
           ≡ α₂ CM.⋆ (α₃ CM.⋆ Tl)
    stepR4 =
        cong (qδ CM.⋆_) (sym (CM.⋆Assoc α₆ α₅₃ Tl))
      ∙ sym (CM.⋆Assoc qδ (α₆ CM.⋆ α₅₃) Tl)
      ∙ cong (CM._⋆ Tl) (CM.pentagon A (F₀ w₁) (F₀ w₂) (F₀ w₃))
      ∙ CM.⋆Assoc α₂ α₃ Tl

    N = (CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩)
          CM.⋆ ((CM.id CM.⊗ₕ (CM.id CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩))
          CM.⋆ (α₂ CM.⋆ (α₃ CM.⋆ Tl)))

    normL : (CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩) CM.⋆ α₁
              CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ ((CM.id CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩) CM.⋆ αB CM.⋆ ((g CM.⊗ₕ CM.id) CM.⋆ h)))
          ≡ N
    normL =
        cong (λ t → (CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩) CM.⋆ (α₁ CM.⋆ t)) stepL1
      ∙ cong ((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩) CM.⋆_) stepL2
      ∙ cong ((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩) CM.⋆_) (
          cong ((CM.id CM.⊗ₕ (CM.id CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)) CM.⋆_) (
            cong (α₂ CM.⋆_) stepL3))

    normR : (CM.id CM.⊗ₕ F₁ (ΣM.α⟨ w₁ , w₂ , w₃ ⟩))
              CM.⋆ ((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩) CM.⋆ α₄
                CM.⋆ ((((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⟩) CM.⋆ α₅ CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ g)) CM.⊗ₕ CM.id) CM.⋆ h))
          ≡ N
    normR =
        cong ((CM.id CM.⊗ₕ F₁ (ΣM.α⟨ w₁ , w₂ , w₃ ⟩)) CM.⋆_) (
          cong (λ t → (CM.id CM.⊗ₕ δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩) CM.⋆ (α₄ CM.⋆ t)) stepR1)
      ∙ cong ((CM.id CM.⊗ₕ F₁ (ΣM.α⟨ w₁ , w₂ , w₃ ⟩)) CM.⋆_) (
          cong ((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩) CM.⋆_) stepR2)
      ∙ stepR3
      ∙ cong ((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩) CM.⋆_) (
          cong ((CM.id CM.⊗ₕ (CM.id CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩)) CM.⋆_) stepR4)

    eq : (CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⊗Σ w₃ ⟩) CM.⋆ α₁
           CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ ((CM.id CM.⊗ₕ δ⁻¹⟨ w₂ , w₃ ⟩) CM.⋆ αB CM.⋆ ((g CM.⊗ₕ CM.id) CM.⋆ h)))
       ≡ (CM.id CM.⊗ₕ F₁ (ΣM.α⟨ w₁ , w₂ , w₃ ⟩))
           CM.⋆ ((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ ⊗Σ w₂ , w₃ ⟩) CM.⋆ α₄
             CM.⋆ ((((CM.id CM.⊗ₕ δ⁻¹⟨ w₁ , w₂ ⟩) CM.⋆ α₅ CM.⋆ ((f CM.⊗ₕ CM.id) CM.⋆ g)) CM.⊗ₕ CM.id) CM.⋆ h))
    eq = normL ∙ sym normR

  ----------------------------------------------------------------------
  -- The polynomial category C[x : jSigma]
  ----------------------------------------------------------------------

  PolyCat : Category _ _
  PolyCat .Category.ob = CM.ob
  PolyCat .Category.Hom[_,_] = PQuot
  PolyCat .Category.id {A} = [ idRepr A ]
  PolyCat .Category._⋆_ = compPQuot
  PolyCat .Category.⋆IdL = SQ.elimProp (λ _ → squash/ _ _)
                              (λ x → eq/ _ _ (zz-step (idlStepP x)))
  PolyCat .Category.⋆IdR = SQ.elimProp (λ _ → squash/ _ _)
                              (λ x → eq/ _ _ (zz-step (idrStepP x)))
  PolyCat .Category.⋆Assoc = SQ.elimProp3 (λ _ _ _ → squash/ _ _)
                              (λ x y z → eq/ _ _ (zz-back (assocStepP x y z)))
  PolyCat .Category.isSetHom = squash/

  ----------------------------------------------------------------------
  -- The adjoining functor R_Sigma : C -> C[x : jSigma]
  ----------------------------------------------------------------------

  rawRep : {x y : CM.ob} → CM.Hom[ x , y ] → Repr x y
  rawRep {x} f = (ΣM.unit , (CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ x ⟩ CM.⋆ f)

  rawRep-comp-step : {x y z : CM.ob} (f : CM.Hom[ x , y ]) (g : CM.Hom[ y , z ])
                   → PStep x z (compPCore (rawRep g) (rawRep f)) (rawRep (f CM.⋆ g))
  rawRep-comp-step {x} {y} {z} f g = ΣM.η⟨ ΣM.unit ⟩ , eq
    where
    α₁' = CM.α⟨ x , F₀ ΣM.unit , F₀ ΣM.unit ⟩
    α₂' = CM.α⟨ y , CM.unit , F₀ ΣM.unit ⟩
    Ff = (CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ x ⟩ CM.⋆ f
    Fg = (CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ y ⟩ CM.⋆ g
    raw-core = (CM.id CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ x ⟩ CM.⋆ (f CM.⋆ g)

    -- Ff = (f ox gammaInv) . rho<y>
    Ff-eq : Ff ≡ (f CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ y ⟩
    Ff-eq =
        cong ((CM.id {x} CM.⊗ₕ γ⁻¹) CM.⋆_) (sym (ρC-nat f))
      ∙ sym (CM.⋆Assoc (CM.id {x} CM.⊗ₕ γ⁻¹)
          (f CM.⊗ₕ CM.id {CM.unit}) CM.ρ⟨ y ⟩)
      ∙ cong (CM._⋆ CM.ρ⟨ y ⟩) (
          ⊗C-seq (CM.id {x}) f γ⁻¹ (CM.id {CM.unit})
        ∙ cong₂ CM._⊗ₕ_ (CM.⋆IdL f) (CM.⋆IdR γ⁻¹))
    Fg-eq : Fg ≡ (g CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ z ⟩
    Fg-eq =
        cong ((CM.id {y} CM.⊗ₕ γ⁻¹) CM.⋆_) (sym (ρC-nat g))
      ∙ sym (CM.⋆Assoc (CM.id {y} CM.⊗ₕ γ⁻¹)
          (g CM.⊗ₕ CM.id {CM.unit}) CM.ρ⟨ z ⟩)
      ∙ cong (CM._⋆ CM.ρ⟨ z ⟩) (
          ⊗C-seq (CM.id {y}) g γ⁻¹ (CM.id {CM.unit})
        ∙ cong₂ CM._⊗ₕ_ (CM.⋆IdL g) (CM.⋆IdR γ⁻¹))
    h-eq : raw-core ≡ ((f CM.⋆ g) CM.⊗ₕ γ⁻¹) CM.⋆ CM.ρ⟨ z ⟩
    h-eq =
        cong ((CM.id {x} CM.⊗ₕ γ⁻¹) CM.⋆_)
          (sym (ρC-nat (f CM.⋆ g)))
      ∙ sym (CM.⋆Assoc (CM.id {x} CM.⊗ₕ γ⁻¹)
          ((f CM.⋆ g) CM.⊗ₕ CM.id {CM.unit}) CM.ρ⟨ z ⟩)
      ∙ cong (CM._⋆ CM.ρ⟨ z ⟩) (
          ⊗C-seq (CM.id {x}) (f CM.⋆ g) γ⁻¹
            (CM.id {CM.unit})
        ∙ cong₂ CM._⊗ₕ_ (CM.⋆IdL (f CM.⋆ g)) (CM.⋆IdR γ⁻¹))

    -- The only non-structural part of functoriality is the two-wire
    -- calculation below.  First expose the two tensor factors; alpha
    -- naturality moves f and gammaInv to the front, the triangle removes
    -- rho<y>, and tensor functoriality combines the remaining arrows.
    a = γ⁻¹ CM.⊗ₕ CM.id {F₀ ΣM.unit}
    s = CM.η⟨ F₀ ΣM.unit ⟩ CM.⋆ γ⁻¹
    p = f CM.⊗ₕ γ⁻¹
    q = CM.ρ⟨ y ⟩
    P = p CM.⊗ₕ CM.id {F₀ ΣM.unit}
    Q = q CM.⊗ₕ CM.id {F₀ ΣM.unit}
    t = g CM.⊗ₕ γ⁻¹
    T = t CM.⋆ CM.ρ⟨ z ⟩
    H = f CM.⊗ₕ a

    middle : (CM.id {y} CM.⊗ₕ CM.η⟨ F₀ ΣM.unit ⟩) CM.⋆ t
           ≡ g CM.⊗ₕ s
    middle =
        ⊗C-seq (CM.id {y}) g (CM.η⟨ F₀ ΣM.unit ⟩) γ⁻¹
      ∙ cong (CM._⊗ₕ s) (CM.⋆IdL g)

    lhs-eq : α₁' CM.⋆ ((Ff CM.⊗ₕ CM.id) CM.⋆ Fg)
           ≡ ((f CM.⋆ g) CM.⊗ₕ (a CM.⋆ s)) CM.⋆ CM.ρ⟨ z ⟩
    lhs-eq =
        cong (λ u → α₁' CM.⋆ ((u CM.⊗ₕ CM.id {F₀ ΣM.unit}) CM.⋆ Fg)) Ff-eq
      ∙ cong (λ u → α₁' CM.⋆ (((p CM.⋆ q) CM.⊗ₕ CM.id {F₀ ΣM.unit}) CM.⋆ u)) Fg-eq
      ∙ cong (λ u → α₁' CM.⋆ (u CM.⋆ T)) (split⊗id p q)
      ∙ cong (α₁' CM.⋆_) (CM.⋆Assoc P Q T)
      ∙ sym (CM.⋆Assoc α₁' P (Q CM.⋆ T))
      ∙ cong (CM._⋆ (Q CM.⋆ T))
          (sym (αC-nat f γ⁻¹ (CM.id {F₀ ΣM.unit})))
      ∙ CM.⋆Assoc H α₂' (Q CM.⋆ T)
      ∙ cong (H CM.⋆_) (
          sym (CM.⋆Assoc α₂' Q T)
        ∙ cong (CM._⋆ T) (CM.triangle y (F₀ ΣM.unit))
        ∙ sym (CM.⋆Assoc
            (CM.id {y} CM.⊗ₕ CM.η⟨ F₀ ΣM.unit ⟩)
            t (CM.ρ⟨ z ⟩))
        ∙ cong (CM._⋆ CM.ρ⟨ z ⟩) middle)
      ∙ sym (CM.⋆Assoc H (g CM.⊗ₕ s) (CM.ρ⟨ z ⟩))
      ∙ cong (CM._⋆ CM.ρ⟨ z ⟩) (⊗C-seq f g a s)

    -- The other side is just right-unitor naturality (already packaged
    -- as h-eq), followed by tensor functoriality and associativity.
    u = a CM.⋆ CM.η⟨ F₀ ΣM.unit ⟩

    rhs-eq : (CM.id {x} CM.⊗ₕ u) CM.⋆ raw-core
           ≡ ((f CM.⋆ g) CM.⊗ₕ (a CM.⋆ s)) CM.⋆ CM.ρ⟨ z ⟩
    rhs-eq =
        cong ((CM.id {x} CM.⊗ₕ u) CM.⋆_) h-eq
      ∙ sym (CM.⋆Assoc
          (CM.id {x} CM.⊗ₕ u)
          ((f CM.⋆ g) CM.⊗ₕ γ⁻¹)
          (CM.ρ⟨ z ⟩))
      ∙ cong (CM._⋆ CM.ρ⟨ z ⟩) (
          ⊗C-seq (CM.id {x}) (f CM.⋆ g) u γ⁻¹
        ∙ cong₂ CM._⊗ₕ_
            (CM.⋆IdL (f CM.⋆ g))
            (CM.⋆Assoc a (CM.η⟨ F₀ ΣM.unit ⟩) γ⁻¹))

    core-eq : α₁' CM.⋆ ((Ff CM.⊗ₕ CM.id) CM.⋆ Fg)
            ≡ (CM.id CM.⊗ₕ ((γ⁻¹ CM.⊗ₕ CM.id) CM.⋆ CM.η⟨ F₀ ΣM.unit ⟩)) CM.⋆ raw-core
    core-eq = lhs-eq ∙ sym rhs-eq

    rhs-to-lhs :
      (CM.id CM.⊗ₕ F₁ (ΣM.η⟨ ΣM.unit ⟩)) CM.⋆ raw-core
      ≡ (CM.id CM.⊗ₕ δ⁻¹⟨ ΣM.unit , ΣM.unit ⟩) CM.⋆
          α₁' CM.⋆ ((Ff CM.⊗ₕ CM.id) CM.⋆ Fg)
    eq : (CM.id CM.⊗ₕ δ⁻¹⟨ ΣM.unit , ΣM.unit ⟩) CM.⋆ α₁' CM.⋆ ((Ff CM.⊗ₕ CM.id) CM.⋆ Fg)
       ≡ (CM.id CM.⊗ₕ F₁ (ΣM.η⟨ ΣM.unit ⟩)) CM.⋆ raw-core
    eq = sym rhs-to-lhs

    rhs-to-lhs =
        cong (λ v → (CM.id {x} CM.⊗ₕ v) CM.⋆ raw-core)
          (F₁ηΣ-eq ΣM.unit)
      ∙ cong (CM._⋆ raw-core) (sym (id⊗Cs _ _))
      ∙ CM.⋆Assoc
          (CM.id {x} CM.⊗ₕ δ⁻¹⟨ ΣM.unit , ΣM.unit ⟩)
          (CM.id {x} CM.⊗ₕ u)
          raw-core
      ∙ cong ((CM.id {x} CM.⊗ₕ δ⁻¹⟨ ΣM.unit , ΣM.unit ⟩) CM.⋆_)
          (sym core-eq)

  ----------------------------------------------------------------------
  -- R_Sigma
  ----------------------------------------------------------------------

  RΣ : Functor CM.C PolyCat
  RΣ .Functor.F-ob x = x
  RΣ .Functor.F-hom f = [ rawRep f ]
  RΣ .Functor.F-id {x} =
    cong [_] (cong (ΣM.unit ,_)
      (cong (((CM.id {x} CM.⊗ₕ γ⁻¹)) CM.⋆_) (CM.⋆IdR (CM.ρ⟨ x ⟩))))
  RΣ .Functor.F-seq f g = eq/ _ _ (zz-back (rawRep-comp-step f g))
