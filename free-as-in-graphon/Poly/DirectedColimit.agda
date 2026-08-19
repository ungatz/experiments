{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Directed colimits of core families, and the product comparison
--
-- A directed preorder of heaps with a meet on every pair, a family of core
-- sets pulling back along it, the quotient of the total space, and the
-- comparison
--
--   colim (F × G)  →  colim F × colim G
--
-- which is shown surjective, and injective by an alignment argument.  Also
-- here: the natural numbers under the reverse order as an instance, and the
-- observation that it has no least heap.
--
-- What is mechanized is the comparison being a bijection.  The step from there
-- to distributivity of the polynomial category is not carried out here, and no
-- monoidal structure, distributor or category appears in this file.  In
-- particular, having no least heap does not by itself show that a chosen core
-- family fails to collapse.
------------------------------------------------------------------------

module Poly.DirectedColimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Properties using (max)
open import Cubical.Data.Nat.Order
  using (_≤_ ; isProp≤ ; ≤-trans ; left-≤-max ; right-≤-max ; ¬m<m)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/)

open import Poly.Base

private
  variable
    ℓ ℓ' ℓc : Level

----------------------------------------------------------------------
-- A directed mediator preorder, and a core family over it
----------------------------------------------------------------------

record DirectedGraph (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Heap     : Type ℓ
    Med      : Heap → Heap → Type ℓ'
    -- at most one mediator between two heaps: no coherence arises
    Med-prop : {a b : Heap} → isProp (Med a b)
    Med-trans : {a b c : Heap} → Med a b → Med b c → Med a c
    -- every two heaps have a COMMON SOURCE.  No LEAST heap is asked for.
    meet     : Heap → Heap → Heap
    meet-l   : (a b : Heap) → Med (meet a b) a
    meet-r   : (a b : Heap) → Med (meet a b) b

record DirectedFamily {ℓ ℓ' : Level} (Γ : DirectedGraph ℓ ℓ') (ℓc : Level)
       : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') ℓc)) where
  open DirectedGraph Γ
  field
    Core      : Heap → Type ℓc
    isSetCore : {H : Heap} → isSet (Core H)
    pull      : {a b : Heap} → Med a b → Core b → Core a
    -- functorial.  Since Med is prop-valued the composite is unique, so
    -- this is a coherence rather than a choice.
    pull-∘    : {a b c : Heap} (r : Med a b) (s : Med b c) (t : Med a c)
                (f : Core c)
              → pull r (pull s f) ≡ pull t f

----------------------------------------------------------------------
-- The quotient, built directly: a directed graph need not have a least
-- heap, so `Permitted` (which fields one) is not the right home.
----------------------------------------------------------------------

module Over {ℓ ℓ' ℓc : Level}
            (Γ : DirectedGraph ℓ ℓ') (F : DirectedFamily Γ ℓc) where

  open DirectedGraph Γ public
  open DirectedFamily F public

  Rep : Type (ℓ-max ℓ ℓc)
  Rep = Σ[ H ∈ Heap ] Core H

  Step : Rep → Rep → Type (ℓ-max ℓ' ℓc)
  Step (a , f) (b , g) = Σ[ r ∈ Med a b ] (f ≡ pull r g)

  Quot : Type (ℓ-max (ℓ-max ℓ ℓ') ℓc)
  Quot = ZigZagQuotient Step

  -- pulling back along the unique mediator, whichever proof one has
  pull-irr : {a b : Heap} (r s : Med a b) (f : Core b) → pull r f ≡ pull s f
  pull-irr r s f = cong (λ t → pull t f) (Med-prop r s)

  ------------------------------------------------------------------
  -- THE ENGINE.  A fence flattens to a single common source.
  ------------------------------------------------------------------

  Joined : Rep → Rep → Type (ℓ-max (ℓ-max ℓ ℓ') ℓc)
  Joined (a , f) (b , g) =
    Σ[ c ∈ Heap ] Σ[ ra ∈ Med c a ] Σ[ rb ∈ Med c b ]
      (pull ra f ≡ pull rb g)

  straighten : {x y : Rep} → ZigZag Step x y → Joined x y
  straighten {a , f} {.(a , f)} zz-refl =
    meet a a , meet-l a a , meet-r a a , pull-irr (meet-l a a) (meet-r a a) f
  straighten {a , f} {b , g} (zz-step (r , eq)) =
      meet a b , meet-l a b , meet-r a b
    , ( cong (pull (meet-l a b)) eq
      ∙ pull-∘ (meet-l a b) r (meet-r a b) g )
  straighten {a , f} {b , g} (zz-back (r , eq)) =
      meet a b , meet-l a b , meet-r a b
    , ( sym ( cong (pull (meet-r a b)) eq
            ∙ pull-∘ (meet-r a b) r (meet-l a b) f ) )
  straighten {a , f} {b , g} (zz-trans {y = m , h} p q) =
    let (c₁ , r₁a , r₁m , e₁) = straighten p
        (c₂ , r₂m , r₂b , e₂) = straighten q
        c  = meet c₁ c₂
        la = Med-trans (meet-l c₁ c₂) r₁a
        lb = Med-trans (meet-r c₁ c₂) r₂b
        m₁ = Med-trans (meet-l c₁ c₂) r₁m
        m₂ = Med-trans (meet-r c₁ c₂) r₂m
    in c , la , lb ,
       ( sym (pull-∘ (meet-l c₁ c₂) r₁a la f)
       ∙ cong (pull (meet-l c₁ c₂)) e₁
       ∙ pull-∘ (meet-l c₁ c₂) r₁m m₁ h
       ∙ pull-irr m₁ m₂ h
       ∙ sym (pull-∘ (meet-r c₁ c₂) r₂m m₂ h)
       ∙ cong (pull (meet-r c₁ c₂)) e₂
       ∙ pull-∘ (meet-r c₁ c₂) r₂b lb g )

----------------------------------------------------------------------
-- The product comparison is a bijection
----------------------------------------------------------------------

module Comparison {ℓ ℓ' ℓc : Level}
                  (Γ : DirectedGraph ℓ ℓ')
                  (F G : DirectedFamily Γ ℓc) where

  open DirectedGraph Γ
  private
    module f = Over Γ F
    module g = Over Γ G

  -- the pointwise product family
  pairF : DirectedFamily Γ ℓc
  pairF .DirectedFamily.Core H = F .DirectedFamily.Core H × G .DirectedFamily.Core H
  pairF .DirectedFamily.isSetCore =
    isSet× (F .DirectedFamily.isSetCore) (G .DirectedFamily.isSetCore)
  pairF .DirectedFamily.pull r (u , v) =
    F .DirectedFamily.pull r u , G .DirectedFamily.pull r v
  pairF .DirectedFamily.pull-∘ r s t (u , v) i =
    F .DirectedFamily.pull-∘ r s t u i , G .DirectedFamily.pull-∘ r s t v i

  private module p = Over Γ pairF

  compare : p.Quot → f.Quot × g.Quot
  compare = SQ.rec (isSet× squash/ squash/) onRep (λ _ _ → onFence)
    where
    onRep : p.Rep → f.Quot × g.Quot
    onRep (H , (u , v)) = [ (H , u) ] , [ (H , v) ]

    onStep : {x y : p.Rep} → p.Step x y → onRep x ≡ onRep y
    onStep {H , (u , v)} {H' , (u' , v')} (r , eq) =
      cong₂ _,_ (eq/ _ _ (zz-step (r , cong fst eq)))
                (eq/ _ _ (zz-step (r , cong snd eq)))

    onFence : {x y : p.Rep} → ZigZag p.Step x y → onRep x ≡ onRep y
    onFence zz-refl        = refl
    onFence (zz-step t)    = onStep t
    onFence (zz-back t)    = sym (onStep t)
    onFence (zz-trans a b) = onFence a ∙ onFence b

  ------------------------------------------------------------------
  -- SURJECTIVE.  Two classes over different heaps are pulled back to a
  -- common source and read there together.  A common source is exactly
  -- what `meet` supplies, and no least heap is involved.
  ------------------------------------------------------------------

  compare-surj :
      (a b : Heap)
      (u : F .DirectedFamily.Core a) (v : G .DirectedFamily.Core b)
    → compare [ ( meet a b
                , ( F .DirectedFamily.pull (meet-l a b) u
                  , G .DirectedFamily.pull (meet-r a b) v ) ) ]
    ≡ ([ (a , u) ] , [ (b , v) ])
  compare-surj a b u v =
    cong₂ _,_
      (eq/ _ _ (zz-step (meet-l a b , refl)))
      (eq/ _ _ (zz-step (meet-r a b , refl)))

  ------------------------------------------------------------------
  -- INJECTIVE, in the form that is actually provable here.  Two fences,
  -- one in each component, ALIGN into a single fence of pairs.  This is
  -- the step that fails in general -- Fence.ReachabilityGap is exactly
  -- its failure -- and directedness is what supplies it.
  --
  -- Stated on classes rather than through effectiveness of the
  -- quotient: the zigzag relation is not proposition-valued, so
  -- `SQ.effective` does not apply, and nothing below pretends it does.
  ------------------------------------------------------------------

  align :
      {a b : Heap}
      {u : F .DirectedFamily.Core a} {u' : F .DirectedFamily.Core b}
      {v : G .DirectedFamily.Core a} {v' : G .DirectedFamily.Core b}
    → ZigZag f.Step (a , u) (b , u')
    → ZigZag g.Step (a , v) (b , v')
    → Path p.Quot [ (a , (u , v)) ] [ (b , (u' , v')) ]
  align {a} {b} {u} {u'} {v} {v'} pf pg =
      sym (eq/ _ _ (zz-step (la , refl)))
    ∙ cong box midEq
    ∙ eq/ _ _ (zz-step (lb , refl))
    where
    Jf = f.straighten pf
    Jg = g.straighten pg

    c₁ = fst Jf
    r₁a = fst (snd Jf)
    r₁b = fst (snd (snd Jf))
    e₁  = snd (snd (snd Jf))

    c₂ = fst Jg
    r₂a = fst (snd Jg)
    r₂b = fst (snd (snd Jg))
    e₂  = snd (snd (snd Jg))

    c : Heap
    c = meet c₁ c₂

    la : Med c a
    la = Med-trans (meet-l c₁ c₂) r₁a

    lb : Med c b
    lb = Med-trans (meet-r c₁ c₂) r₂b

    -- the F component travels through c₁ ...
    eF : F .DirectedFamily.pull la u ≡ F .DirectedFamily.pull lb u'
    eF = sym (F .DirectedFamily.pull-∘ (meet-l c₁ c₂) r₁a la u)
       ∙ cong (F .DirectedFamily.pull (meet-l c₁ c₂)) e₁
       ∙ F .DirectedFamily.pull-∘ (meet-l c₁ c₂) r₁b
           (Med-trans (meet-l c₁ c₂) r₁b) u'
       ∙ f.pull-irr (Med-trans (meet-l c₁ c₂) r₁b) lb u'

    -- ... and the G component through c₂
    eG : G .DirectedFamily.pull la v ≡ G .DirectedFamily.pull lb v'
    eG = g.pull-irr la (Med-trans (meet-r c₁ c₂) r₂a) v
       ∙ sym (G .DirectedFamily.pull-∘ (meet-r c₁ c₂) r₂a
                (Med-trans (meet-r c₁ c₂) r₂a) v)
       ∙ cong (G .DirectedFamily.pull (meet-r c₁ c₂)) e₂
       ∙ G .DirectedFamily.pull-∘ (meet-r c₁ c₂) r₂b lb v'

    midEq : ( F .DirectedFamily.pull la u , G .DirectedFamily.pull la v )
          ≡ ( F .DirectedFamily.pull lb u' , G .DirectedFamily.pull lb v' )
    midEq i = eF i , eG i

    box : pairF .DirectedFamily.Core c → p.Quot
    box t = [ (c , t) ]

----------------------------------------------------------------------
-- The running instance: no least heap, and the comparison still works
----------------------------------------------------------------------

ℕGraph : DirectedGraph ℓ-zero ℓ-zero
ℕGraph .DirectedGraph.Heap      = ℕ
ℕGraph .DirectedGraph.Med a b   = b ≤ a
ℕGraph .DirectedGraph.Med-prop  = isProp≤
ℕGraph .DirectedGraph.Med-trans = λ r s → ≤-trans s r
ℕGraph .DirectedGraph.meet      = max
ℕGraph .DirectedGraph.meet-l    = λ a b → left-≤-max
ℕGraph .DirectedGraph.meet-r    = λ a b → right-≤-max

-- ... and it has NO least heap: a heap mediating into every other would
-- be a natural number above all of them.
no-least-heap :
  ¬ (Σ[ n ∈ ℕ ] ((m : ℕ) → DirectedGraph.Med ℕGraph n m))
no-least-heap (n , univ) = ¬m<m {m = n} (univ (suc n))
