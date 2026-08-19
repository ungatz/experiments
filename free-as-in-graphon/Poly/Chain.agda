{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- A three-element chain, and why the construction is not degenerate
--
-- The chain bottom < middle < top, with the meet as tensor, the top as unit,
-- the join as coproduct and the bottom as initial object, is a distributive
-- symmetric monoidal base whose canonical distributor is invertible.  The
-- natural numbers under the reverse order, with addition as the monoidal
-- structure, give a directed index.
--
-- So the coproducts and the initial object of the previous module exist here.
-- The point of the instance is the other two facts: the adjoining functor is
-- not full, and there is no morphism from the top to the bottom.  Without
-- them nothing rules out the construction being degenerate.
------------------------------------------------------------------------

module Poly.Chain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; max)
open import Cubical.Data.Nat.Properties
  using (+-assoc ; +-comm ; +-zero)
open import Cubical.Data.Nat.Order
  using (_≤_ ; isProp≤ ; ≤-refl ; ≤-trans ; ≤-+-≤
       ; left-≤-max ; right-≤-max ; ¬-<-zero)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.Initial
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ using ([_] ; squash/)

open import Poly.Monoidal.Symmetric
open import Poly.Monoidal.Distributive
open import Poly.Category
open import Poly.Directed

------------------------------------------------------------------------
-- The thin three-element chain
------------------------------------------------------------------------

data Chain₃ : Type where
  bottom middle top : Chain₃

infix 4 _≤₃_

_≤₃_ : Chain₃ → Chain₃ → Type
bottom ≤₃ _ = Unit
middle ≤₃ bottom = ⊥
middle ≤₃ middle = Unit
middle ≤₃ top = Unit
top ≤₃ bottom = ⊥
top ≤₃ middle = ⊥
top ≤₃ top = Unit

≤₃-prop : {x y : Chain₃} → isProp (x ≤₃ y)
≤₃-prop {bottom} p q = refl
≤₃-prop {middle} {bottom} ()
≤₃-prop {middle} {middle} p q = refl
≤₃-prop {middle} {top} p q = refl
≤₃-prop {top} {bottom} ()
≤₃-prop {top} {middle} ()
≤₃-prop {top} {top} p q = refl

≤₃-refl : (x : Chain₃) → x ≤₃ x
≤₃-refl bottom = tt
≤₃-refl middle = tt
≤₃-refl top = tt

≤₃-trans : {x y z : Chain₃} → x ≤₃ y → y ≤₃ z → x ≤₃ z
≤₃-trans {bottom} f g = tt
≤₃-trans {middle} {bottom} ()
≤₃-trans {middle} {middle} f g = g
≤₃-trans {middle} {top} {bottom} f ()
≤₃-trans {middle} {top} {middle} f ()
≤₃-trans {middle} {top} {top} f g = tt
≤₃-trans {top} {bottom} ()
≤₃-trans {top} {middle} ()
≤₃-trans {top} {top} {bottom} f ()
≤₃-trans {top} {top} {middle} f ()
≤₃-trans {top} {top} {top} f g = tt

ChainCat : Category ℓ-zero ℓ-zero
ChainCat .Category.ob = Chain₃
ChainCat .Category.Hom[_,_] = _≤₃_
ChainCat .Category.id {x} = ≤₃-refl x
ChainCat .Category._⋆_ = ≤₃-trans
ChainCat .Category.⋆IdL _ = ≤₃-prop _ _
ChainCat .Category.⋆IdR _ = ≤₃-prop _ _
ChainCat .Category.⋆Assoc _ _ _ = ≤₃-prop _ _
ChainCat .Category.isSetHom = isProp→isSet ≤₃-prop

infixl 7 _∧₃_
infixl 6 _∨₃_

_∧₃_ : Chain₃ → Chain₃ → Chain₃
bottom ∧₃ _ = bottom
middle ∧₃ bottom = bottom
middle ∧₃ middle = middle
middle ∧₃ top = middle
top ∧₃ y = y

_∨₃_ : Chain₃ → Chain₃ → Chain₃
bottom ∨₃ y = y
middle ∨₃ bottom = middle
middle ∨₃ middle = middle
middle ∨₃ top = top
top ∨₃ _ = top

meet-mono :
    {a a' b b' : Chain₃}
  → a ≤₃ a' → b ≤₃ b' → (a ∧₃ b) ≤₃ (a' ∧₃ b')
meet-mono {a = bottom} f g = tt
meet-mono {a = middle} {a' = bottom} ()
meet-mono {a = middle} {a' = middle} {b = bottom} f g = tt
meet-mono {a = middle} {a' = middle} {b = middle} {b' = bottom} f ()
meet-mono {a = middle} {a' = middle} {b = middle} {b' = middle} f g = tt
meet-mono {a = middle} {a' = middle} {b = middle} {b' = top} f g = tt
meet-mono {a = middle} {a' = middle} {b = top} {b' = bottom} f ()
meet-mono {a = middle} {a' = middle} {b = top} {b' = middle} f ()
meet-mono {a = middle} {a' = middle} {b = top} {b' = top} f g = tt
meet-mono {a = middle} {a' = top} {b = bottom} f g = tt
meet-mono {a = middle} {a' = top} {b = middle} {b' = bottom} f ()
meet-mono {a = middle} {a' = top} {b = middle} {b' = middle} f g = tt
meet-mono {a = middle} {a' = top} {b = middle} {b' = top} f g = tt
meet-mono {a = middle} {a' = top} {b = top} {b' = bottom} f ()
meet-mono {a = middle} {a' = top} {b = top} {b' = middle} f ()
meet-mono {a = middle} {a' = top} {b = top} {b' = top} f g = tt
meet-mono {a = top} {a' = bottom} ()
meet-mono {a = top} {a' = middle} ()
meet-mono {a = top} {a' = top} f g = g

meet-assoc :
  (x y z : Chain₃) → x ∧₃ (y ∧₃ z) ≡ (x ∧₃ y) ∧₃ z
meet-assoc bottom y z = refl
meet-assoc middle bottom z = refl
meet-assoc middle middle bottom = refl
meet-assoc middle middle middle = refl
meet-assoc middle middle top = refl
meet-assoc middle top z = refl
meet-assoc top y z = refl

meet-comm : (x y : Chain₃) → x ∧₃ y ≡ y ∧₃ x
meet-comm bottom bottom = refl
meet-comm bottom middle = refl
meet-comm bottom top = refl
meet-comm middle bottom = refl
meet-comm middle middle = refl
meet-comm middle top = refl
meet-comm top bottom = refl
meet-comm top middle = refl
meet-comm top top = refl

meet-idL : (x : Chain₃) → top ∧₃ x ≡ x
meet-idL x = refl

meet-idR : (x : Chain₃) → x ∧₃ top ≡ x
meet-idR bottom = refl
meet-idR middle = refl
meet-idR top = refl

path≤₃ : {x y : Chain₃} → x ≡ y → x ≤₃ y
path≤₃ {x} p = subst (x ≤₃_) p (≤₃-refl x)

MeetTensor : Functor (ChainCat ×C ChainCat) ChainCat
MeetTensor .Functor.F-ob (x , y) = x ∧₃ y
MeetTensor .Functor.F-hom (f , g) = meet-mono f g
MeetTensor .Functor.F-id = ≤₃-prop _ _
MeetTensor .Functor.F-seq _ _ = ≤₃-prop _ _

ChainM : MonoidalStr ChainCat
ChainM .MonoidalStr.tenstr .TensorStr.─⊗─ = MeetTensor
ChainM .MonoidalStr.tenstr .TensorStr.unit = top
ChainM .MonoidalStr.α = record
  { trans = record
      { N-ob = λ (x , y , z) → path≤₃ (meet-assoc x y z)
      ; N-hom = λ _ → ≤₃-prop _ _ }
  ; nIso = λ (x , y , z) →
      isiso (path≤₃ (sym (meet-assoc x y z)))
        (≤₃-prop _ _) (≤₃-prop _ _) }
ChainM .MonoidalStr.η = record
  { trans = record
      { N-ob = λ x → path≤₃ (meet-idL x)
      ; N-hom = λ _ → ≤₃-prop _ _ }
  ; nIso = λ x →
      isiso (path≤₃ (sym (meet-idL x)))
        (≤₃-prop _ _) (≤₃-prop _ _) }
ChainM .MonoidalStr.ρ = record
  { trans = record
      { N-ob = λ x → path≤₃ (meet-idR x)
      ; N-hom = λ _ → ≤₃-prop _ _ }
  ; nIso = λ x →
      isiso (path≤₃ (sym (meet-idR x)))
        (≤₃-prop _ _) (≤₃-prop _ _) }
ChainM .MonoidalStr.pentagon _ _ _ _ = ≤₃-prop _ _
ChainM .MonoidalStr.triangle _ _ = ≤₃-prop _ _

ChainS : SymmetricStr ChainCat ChainM
ChainS .SymmetricStr.B⟨_,_⟩ x y = path≤₃ (meet-comm x y)
ChainS .SymmetricStr.B-nat _ _ = ≤₃-prop _ _
ChainS .SymmetricStr.B-invol _ _ = ≤₃-prop _ _
ChainS .SymmetricStr.hexagon _ _ _ = ≤₃-prop _ _

join-inl : (x y : Chain₃) → x ≤₃ (x ∨₃ y)
join-inl bottom y = tt
join-inl middle bottom = tt
join-inl middle middle = tt
join-inl middle top = tt
join-inl top y = tt

join-inr : (x y : Chain₃) → y ≤₃ (x ∨₃ y)
join-inr bottom y = ≤₃-refl y
join-inr middle bottom = tt
join-inr middle middle = tt
join-inr middle top = tt
join-inr top bottom = tt
join-inr top middle = tt
join-inr top top = tt

join-univ :
    {x y z : Chain₃}
  → x ≤₃ z → y ≤₃ z → (x ∨₃ y) ≤₃ z
join-univ {x = bottom} f g = g
join-univ {x = middle} {y = bottom} f g = f
join-univ {x = middle} {y = middle} f g = f
join-univ {x = middle} {y = top} f g = g
join-univ {x = top} f g = f

ChainCoproducts : BinCoproducts ChainCat
ChainCoproducts x y .BinCoproduct.binCoprodOb = x ∨₃ y
ChainCoproducts x y .BinCoproduct.binCoprodInj₁ = join-inl x y
ChainCoproducts x y .BinCoproduct.binCoprodInj₂ = join-inr x y
ChainCoproducts x y .BinCoproduct.univProp f g =
  (join-univ f g , ≤₃-prop _ _ , ≤₃-prop _ _) , uniq
  where
  uniq :
      (t : Σ[ h ∈ _ ] _)
    → (join-univ f g , ≤₃-prop _ _ , ≤₃-prop _ _) ≡ t
  uniq (h , p , q) =
    Σ≡Prop
      (λ _ → isProp×
        (ChainCat .Category.isSetHom _ _)
        (ChainCat .Category.isSetHom _ _))
      (≤₃-prop _ _)

ChainInitial : Initial ChainCat
ChainInitial .fst = bottom
ChainInitial .snd y .fst = tt
ChainInitial .snd y .snd f = ≤₃-prop {bottom} {y} tt f

right-distrib :
    (x y z : Chain₃)
  → (x ∧₃ y) ∨₃ (x ∧₃ z) ≡ x ∧₃ (y ∨₃ z)
right-distrib bottom y z = refl
right-distrib middle bottom bottom = refl
right-distrib middle bottom middle = refl
right-distrib middle bottom top = refl
right-distrib middle middle bottom = refl
right-distrib middle middle middle = refl
right-distrib middle middle top = refl
right-distrib middle top bottom = refl
right-distrib middle top middle = refl
right-distrib middle top top = refl
right-distrib top y z = refl

left-distrib :
    (x y z : Chain₃)
  → (x ∧₃ z) ∨₃ (y ∧₃ z) ≡ (x ∨₃ y) ∧₃ z
left-distrib x y z =
    cong₂ _∨₃_ (meet-comm x z) (meet-comm y z)
  ∙ right-distrib z x y
  ∙ meet-comm z (x ∨₃ y)

meet-bottom : (x : Chain₃) → x ∧₃ bottom ≡ bottom
meet-bottom x = meet-comm x bottom

ChainDist : DistSMC ℓ-zero ℓ-zero
ChainDist .DistSMC.C = ChainCat
ChainDist .DistSMC.M = ChainM
ChainDist .DistSMC.S = ChainS
ChainDist .DistSMC.coprods = ChainCoproducts
ChainDist .DistSMC.initialD = ChainInitial
ChainDist .DistSMC.δ⟨_,_,_⟩ x y z =
  path≤₃ (right-distrib x y z) ,
  isiso (path≤₃ (sym (right-distrib x y z)))
    (≤₃-prop _ _) (≤₃-prop _ _)
ChainDist .DistSMC.δ-nat _ _ _ = ≤₃-prop _ _
ChainDist .DistSMC.δ-ι₁ _ _ _ = ≤₃-prop _ _
ChainDist .DistSMC.annih x y =
  ≤₃-trans (path≤₃ (meet-bottom x)) tt ,
  λ f → ≤₃-prop _ f

ChainCanonical : CanonicalDistributorIso ChainDist
ChainCanonical .CanonicalDistributorIso.dmL-iso x y z =
  isiso (path≤₃ (sym (left-distrib x y z)))
    (≤₃-prop _ _) (≤₃-prop _ _)

------------------------------------------------------------------------
-- The directed index (Nat, >=, +, 0)
------------------------------------------------------------------------

NatRevCat : Category ℓ-zero ℓ-zero
NatRevCat .Category.ob = ℕ
NatRevCat .Category.Hom[_,_] m n = n ≤ m
NatRevCat .Category.id = ≤-refl
NatRevCat .Category._⋆_ f g = ≤-trans g f
NatRevCat .Category.⋆IdL _ = isProp≤ _ _
NatRevCat .Category.⋆IdR _ = isProp≤ _ _
NatRevCat .Category.⋆Assoc _ _ _ = isProp≤ _ _
NatRevCat .Category.isSetHom = isProp→isSet isProp≤

natPathHom :
  {m n : ℕ} → m ≡ n → Category.Hom[_,_] NatRevCat m n
natPathHom p = 0 , sym p

NatTensor : Functor (NatRevCat ×C NatRevCat) NatRevCat
NatTensor .Functor.F-ob (m , n) = m + n
NatTensor .Functor.F-hom (f , g) = ≤-+-≤ f g
NatTensor .Functor.F-id = isProp≤ _ _
NatTensor .Functor.F-seq _ _ = isProp≤ _ _

NatM : MonoidalStr NatRevCat
NatM .MonoidalStr.tenstr .TensorStr.─⊗─ = NatTensor
NatM .MonoidalStr.tenstr .TensorStr.unit = 0
NatM .MonoidalStr.α = record
  { trans = record
      { N-ob = λ (m , n , k) → natPathHom (+-assoc m n k)
      ; N-hom = λ _ → isProp≤ _ _ }
  ; nIso = λ (m , n , k) →
      isiso (natPathHom (sym (+-assoc m n k)))
        (isProp≤ _ _) (isProp≤ _ _) }
NatM .MonoidalStr.η = record
  { trans = record
      { N-ob = λ n → natPathHom refl
      ; N-hom = λ _ → isProp≤ _ _ }
  ; nIso = λ n →
      isiso (natPathHom refl)
        (isProp≤ _ _) (isProp≤ _ _) }
NatM .MonoidalStr.ρ = record
  { trans = record
      { N-ob = λ n → natPathHom (+-zero n)
      ; N-hom = λ _ → isProp≤ _ _ }
  ; nIso = λ n →
      isiso (natPathHom (sym (+-zero n)))
        (isProp≤ _ _) (isProp≤ _ _) }
NatM .MonoidalStr.pentagon _ _ _ _ = isProp≤ _ _
NatM .MonoidalStr.triangle _ _ = isProp≤ _ _

NatS : SymmetricStr NatRevCat NatM
NatS .SymmetricStr.B⟨_,_⟩ m n = natPathHom (+-comm m n)
NatS .SymmetricStr.B-nat _ _ = isProp≤ _ _
NatS .SymmetricStr.B-invol _ _ = isProp≤ _ _
NatS .SymmetricStr.hexagon _ _ _ = isProp≤ _ _

NatIndex : SymmMonCategory ℓ-zero ℓ-zero
NatIndex .SymmMonCategory.C = NatRevCat
NatIndex .SymmMonCategory.M = NatM
NatIndex .SymmMonCategory.S = NatS

NatDirected : DirectedIndex NatIndex
NatDirected .DirectedIndex.hom-prop = isProp≤
NatDirected .DirectedIndex.inhabitant = 0
NatDirected .DirectedIndex.meet = max
NatDirected .DirectedIndex.meet-l _ _ = left-≤-max
NatDirected .DirectedIndex.meet-r _ _ = right-≤-max

------------------------------------------------------------------------
-- The strong monoidal functor j(0)=top, j(n+1)=middle
------------------------------------------------------------------------

j₀ : ℕ → Chain₃
j₀ zero = top
j₀ (suc n) = middle

j₁ :
    {m n : ℕ}
  → Category.Hom[_,_] NatRevCat m n
  → Category.Hom[_,_] ChainCat (j₀ m) (j₀ n)
j₁ {zero} {zero} h = tt
j₁ {zero} {suc n} h = Empty.rec (¬-<-zero h)
j₁ {suc m} {zero} h = tt
j₁ {suc m} {suc n} h = tt

jδ :
    (m n : ℕ)
  → (j₀ m ∧₃ j₀ n) ≤₃ j₀ (m + n)
jδ zero zero = tt
jδ zero (suc n) = tt
jδ (suc m) zero = tt
jδ (suc m) (suc n) = tt

jδ⁻¹ :
    (m n : ℕ)
  → j₀ (m + n) ≤₃ (j₀ m ∧₃ j₀ n)
jδ⁻¹ zero zero = tt
jδ⁻¹ zero (suc n) = tt
jδ⁻¹ (suc m) zero = tt
jδ⁻¹ (suc m) (suc n) = tt

top-id : top ≤₃ top
top-id = tt

ChainJ : StrongMonoFunctor NatIndex (BaseSMC ChainDist)
ChainJ .StrongMonoFunctor.F₀ = j₀
ChainJ .StrongMonoFunctor.F₁ = j₁
ChainJ .StrongMonoFunctor.F-id = ≤₃-prop _ _
ChainJ .StrongMonoFunctor.F-seq _ _ = ≤₃-prop _ _
ChainJ .StrongMonoFunctor.δ⟨_,_⟩ = jδ
ChainJ .StrongMonoFunctor.δ-iso m n =
  isiso (jδ⁻¹ m n) (≤₃-prop _ _) (≤₃-prop _ _)
ChainJ .StrongMonoFunctor.γ = tt
ChainJ .StrongMonoFunctor.γ-iso =
  isiso top-id
    (≤₃-prop {top} {top} _ _)
    (≤₃-prop {top} {top} _ _)
ChainJ .StrongMonoFunctor.δ-nat _ _ = ≤₃-prop _ _
ChainJ .StrongMonoFunctor.δ-assoc _ _ _ = ≤₃-prop _ _
ChainJ .StrongMonoFunctor.γ-left _ = ≤₃-prop _ _
ChainJ .StrongMonoFunctor.γ-right _ = ≤₃-prop _ _

------------------------------------------------------------------------
-- The instantiated directed theorem
------------------------------------------------------------------------

module P = PolyOver NatIndex (BaseSMC ChainDist) ChainJ
module DirectedChain =
  DirectedPolynomial ChainDist NatIndex ChainJ NatDirected ChainCanonical

chainPolyCoproducts : BinCoproducts P.PolyCat
chainPolyCoproducts = DirectedChain.polyCoproducts

chainPolyInitial : Initial P.PolyCat
chainPolyInitial = DirectedChain.polyInitial

chainImageDistributor :
    (A B X : Chain₃)
  → CatIso P.PolyCat
      ((A ∧₃ X) ∨₃ (B ∧₃ X))
      ((A ∨₃ B) ∧₃ X)
chainImageDistributor = DirectedChain.imageDistributor

------------------------------------------------------------------------
-- Direct non-degeneracy witnesses
------------------------------------------------------------------------

heap-one-arrow : P.PQuot top middle
heap-one-arrow = [ (suc zero , tt) ]

no-base-top-middle :
  ¬ Category.Hom[_,_] ChainCat top middle
no-base-top-middle x = x

RΣ-not-full : ¬ Functor.isFull P.RΣ
RΣ-not-full full =
  PT.rec Empty.isProp⊥
    (λ (f , _) → no-base-top-middle f)
    (full top middle heap-one-arrow)

top-bottom-core-empty :
    (w : ℕ)
  → Category.Hom[_,_] ChainCat (top ∧₃ j₀ w) bottom
  → ⊥
top-bottom-core-empty zero f = f
top-bottom-core-empty (suc w) f = f

top-bottom-rep-empty : P.Repr top bottom → ⊥
top-bottom-rep-empty (w , f) = top-bottom-core-empty w f

top-bottom-empty : P.PQuot top bottom → ⊥
top-bottom-empty =
  SQ.rec (isProp→isSet Empty.isProp⊥)
    top-bottom-rep-empty
    (λ x _ _ → Empty.rec (top-bottom-rep-empty x))

poly-not-indiscrete :
  ¬ ((A B : Chain₃) → P.PQuot A B)
poly-not-indiscrete all = top-bottom-empty (all top bottom)
