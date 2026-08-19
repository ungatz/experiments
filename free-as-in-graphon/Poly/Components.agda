{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- The quotient as connected components
--
-- For fixed endpoints the representatives and the steps between them form a
-- category, because steps compose.  The quotient is its set of connected
-- components.  That is a restatement rather than new mathematics, but it is
-- worth making once, because several separate-looking facts become instances
-- of three properties provable in the abstract.
--
--   Invariants.  Anything constant along a single step is constant along a
--   zigzag, hence a function on the quotient, hence a separator.
--
--   Weak cones.  If any two steps into a common object admit a common source,
--   every zigzag collapses to a span of length two.  No commutation is asked
--   for, since connectivity is all the quotient sees.  The hypothesis is a
--   fragment of cofilteredness, and a strictly weaker one: cofilteredness asks
--   for a cone over every pair rather than only over pairs already joined by a
--   cospan, and equalises parallel arrows as well.  Neither extra demand buys
--   anything visible here.
--
--   A canonical root.  If every object receives a step from a canonically
--   chosen one and the choice is invariant, the root is a complete invariant:
--   zigzags are spans with a canonical apex, and two objects are identified
--   exactly when their roots agree.
--
-- and, as a corollary, a dichotomy: a step relation with a canonical root and
-- a separating invariant is impossible unless the invariant is constant.  A
-- collapse theorem and a separation theorem are then not two accidents about
-- two bases.  They are the two ways one category can fail to be the other.
--
-- Everything here is at the level of an abstract step relation on an abstract
-- carrier.  No base, no monoidal structure and no polynomial category appears.
------------------------------------------------------------------------

module Poly.Components where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/)

open import Poly.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

----------------------------------------------------------------------
-- Spans: fences of length two, both legs out of a common apex
----------------------------------------------------------------------

Span : {Rep : Type ℓ} (Step : Rep → Rep → Type ℓ') → Rep → Rep → Type (ℓ-max ℓ ℓ')
Span {Rep = Rep} Step x y = Σ[ z ∈ Rep ] (Step z x × Step z y)

span→fence : {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'} {x y : Rep}
           → Span Step x y → ZigZag Step x y
span→fence (z , (l , r)) = zz-trans (zz-back l) (zz-step r)

----------------------------------------------------------------------
-- Invariants are functions on π₀
----------------------------------------------------------------------

-- Constant along one step implies constant along any fence.  Stated
-- without hypotheses on the target, since no truncation is used.
invariant-fence :
  {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'} {X : Type ℓ''}
  (inv : Rep → X)
  (inv-step : {x y : Rep} → Step x y → inv x ≡ inv y)
  → {x y : Rep} → ZigZag Step x y → inv x ≡ inv y
invariant-fence inv inv-step zz-refl        = refl
invariant-fence inv inv-step (zz-step s)    = inv-step s
invariant-fence inv inv-step (zz-back s)    = sym (inv-step s)
invariant-fence inv inv-step (zz-trans p q) =
  invariant-fence inv inv-step p ∙ invariant-fence inv inv-step q

module Invariant {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'} {X : Type ℓ''}
                 (isSetX : isSet X)
                 (inv : Rep → X)
                 (inv-step : {x y : Rep} → Step x y → inv x ≡ inv y) where

  onQuotient : ZigZagQuotient Step → X
  onQuotient = SQ.rec isSetX inv
    (λ x y zz → invariant-fence inv inv-step zz)

  -- distinct values separate classes: this is the shape of every
  -- non-identification argument in the development
  separates : {x y : Rep}
            → ¬ (inv x ≡ inv y)
            → ¬ (Path (ZigZagQuotient Step) [ x ] [ y ])
  separates ne p = ne (cong onQuotient p)

----------------------------------------------------------------------
-- Weak cones collapse every fence to a span
----------------------------------------------------------------------

module WeakCones {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'}
  (idStep : (x : Rep) → Step x x)
  (compStep : {x y z : Rep} → Step x y → Step y z → Step x z)
  (cone : {a b c : Rep} → Step a b → Step c b
        → Σ[ d ∈ Rep ] (Step d a × Step d c))
  where

  -- Induction on the fence.  The transitive case is the only content:
  -- two spans meeting at a common endpoint are merged by taking a
  -- common source of their inner legs, then composing outwards.
  collapse : {x y : Rep} → ZigZag Step x y → Span Step x y
  collapse {x} {y} zz-refl     = x , (idStep x , idStep x)
  collapse {x} {y} (zz-step s) = x , (idStep x , s)
  collapse {x} {y} (zz-back s) = y , (s , idStep y)
  collapse {x} {y} (zz-trans p q) = merge (collapse p) (collapse q)
    where
    merge : {m : Rep} → Span Step x m → Span Step m y → Span Step x y
    merge (d₁ , (l₁ , r₁)) (d₂ , (l₂ , r₂)) =
      let (e , (e₁ , e₂)) = cone r₁ l₂
      in e , (compStep e₁ l₁ , compStep e₂ r₂)

  -- so nothing longer than a span is ever needed
  fence≃span : {x y : Rep} → ZigZag Step x y → ZigZag Step x y
  fence≃span zz = span→fence (collapse zz)

----------------------------------------------------------------------
-- A canonical root: fences are spans with a canonical apex, and the
-- root is a complete invariant
----------------------------------------------------------------------

-- The root is not an element of the carrier but a VALUE in a set: the
-- carrier of representatives need not be a set (objects of a category
-- are not), while the datum that names a class always is.
module CanonicalRoot {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'}
  {X : Type ℓ''} (isSetX : isSet X)
  (val      : Rep → X)                                   -- the naming datum
  (rep      : X → Rep)                                   -- its canonical carrier
  (rep→     : (r : Rep) → Step (rep (val r)) r)          -- which reaches r
  (val-step : {x y : Rep} → Step x y → val x ≡ val y)    -- and is invariant
  where

  valOnQuotient : ZigZagQuotient Step → X
  valOnQuotient = Invariant.onQuotient isSetX val val-step

  -- every fence is a span of length two, with the apex NAMED
  fence→span : {x y : Rep} → ZigZag Step x y → Span Step x y
  fence→span {x} {y} zz =
    rep (val x) , (rep→ x , subst (λ t → Step (rep t) y) (sym valEq) (rep→ y))
    where
    valEq : val x ≡ val y
    valEq = invariant-fence val val-step zz

  -- and the datum decides identification, in both directions
  complete : {x y : Rep}
           → Path (ZigZagQuotient Step) [ x ] [ y ] → val x ≡ val y
  complete p = cong valOnQuotient p

  sound : {x y : Rep}
        → val x ≡ val y → Path (ZigZagQuotient Step) [ x ] [ y ]
  sound {x} {y} q =
      sym (eq/ _ _ (zz-step (rep→ x)))
    ∙ cong (λ t → [ rep t ]) q
    ∙ eq/ _ _ (zz-step (rep→ y))

----------------------------------------------------------------------
-- The dichotomy, sharpened: a canonical root leaves no room for a
-- separating invariant
----------------------------------------------------------------------

module Dichotomy {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'}
  {X Y : Type ℓ''} (isSetX : isSet X)
  (val : Rep → X) (rep : X → Rep)
  (rep→ : (r : Rep) → Step (rep (val r)) r)
  (val-step : {x y : Rep} → Step x y → val x ≡ val y)
  (inv : Rep → Y)
  (inv-step : {x y : Rep} → Step x y → inv x ≡ inv y)
  where

  open CanonicalRoot isSetX val rep rep→ val-step using (sound)

  -- Nothing a canonical root has identified can be separated by any
  -- invariant.  So on a carrier where the root exists, every invariant
  -- factors through the root's fibres: the paper's two halves exclude
  -- one another wherever the quotient is nontrivial.
  no-separation : {x y : Rep} → val x ≡ val y → inv x ≡ inv y
  no-separation {x} {y} q =
    invariant-fence inv inv-step
      (zz-trans (zz-back (rep→ x))
                (zz-trans (subst (λ t → ZigZag Step (rep (val x)) (rep t)) q zz-refl)
                          (zz-step (rep→ y))))

----------------------------------------------------------------------
-- Instantiation 1: the cardinality model separates, by an invariant
--
-- The cardinality separation below is exactly Invariant.separates
-- at the residual, with no reference to that module's specifics.
----------------------------------------------------------------------

module _ where
  open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots ; injSuc ; isSetℕ)

  -- residual carriers with a base-drawn change between them
  private
    CardStep : ℕ → ℕ → Type
    CardStep m n = m ≡ n

  card-separates : (n : ℕ)
                 → ¬ (Path (ZigZagQuotient CardStep) [ n ] [ suc n ])
  private
    n≢suc : (n : ℕ) → ¬ (n ≡ suc n)
    n≢suc zero    q = znots q
    n≢suc (suc n) q = n≢suc n (injSuc q)

  card-separates n =
    Invariant.separates {Step = CardStep} isSetℕ (λ m → m) (λ p → p)
      {x = n} {y = suc n} (n≢suc n)

----------------------------------------------------------------------
-- Instantiation 2: the collapse, derived from the framework alone
--
-- A collapse theorem, that the adjoining functor into the cocartesian
-- polynomial category is an isomorphism, is usually proved by a chase in the
-- base.  The chase is not the content: all that gets used is that the
-- empty-heap representative is a canonical root.
-- Below, an abstract carrier with a root has its quotient computed, and
-- fences bounded at two, with no base in sight.  Feeding fullness of the adjoining
-- functor and its retracting step into this module reproduces that theorem.
----------------------------------------------------------------------

module RootedQuotient {Rep : Type ℓ} {Step : Rep → Rep → Type ℓ'}
  {X : Type ℓ''} (isSetX : isSet X)
  (val : Rep → X) (rep : X → Rep)
  (rep→ : (r : Rep) → Step (rep (val r)) r)
  (val-step : {x y : Rep} → Step x y → val x ≡ val y)
  where

  open CanonicalRoot isSetX val rep rep→ val-step public

  -- identification in the quotient IS equality of the naming datum
  decides : {x y : Rep}
          → (Path (ZigZagQuotient Step) [ x ] [ y ] → val x ≡ val y)
          × (val x ≡ val y → Path (ZigZagQuotient Step) [ x ] [ y ])
  decides = complete , sound

  -- and every fence is a span of length two
  bounded : {x y : Rep} → ZigZag Step x y → Span Step x y
  bounded = fence→span
