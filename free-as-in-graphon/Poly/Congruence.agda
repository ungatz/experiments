{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- The generating relation, and why closing it is not optional
--
-- Ackerman, Freer, Kaddar, Karwowski, Moss, Roy, Staton and Yang give the
-- hom-sets of their polynomial category as a quotient of representatives by a
-- reindexing relation, with one injection chosen per block of the domain.
-- What is encoded here is that relation and the equality it generates, over
-- the finite graph-choice core: worlds are positive finite labelled simple
-- graphs, presented by symmetric loopless Boolean adjacency, and a
-- representative is a heap size together with a choice, for each world, of one
-- of its vertices.
--
-- OneStep is their one-block generating relation.  The quotient by its
-- reflexive-symmetric-transitive closure is the equality their construction
-- intends.  Two facts are proved about it.
--
-- First, the relation identifies the two programs it is designed to identify:
-- drawing once before a branch and drawing inside each branch are one step
-- apart.
--
-- Second, that identification does not survive composition.  Composing both
-- sides with a single further morphism, one that produces its argument by
-- drawing rather than receiving it, sends them to representatives that the
-- closure cannot join, and the obstruction is an invariant of the closure
-- rather than an accident of the witness.  So the relation as generated is not
-- a congruence, and composition does not descend to the quotient.
--
-- The two-relation form of the same obstruction is also here: no relation that
-- acts branch by branch can be closed under composition and still make the
-- identification, whatever injections it is allowed.  Closing the generating
-- relation is therefore not one repair among several.
--
-- Scope.  This is the combinatorial core, not an instantiation at their base:
-- the objects here are heap sizes and vertex choices, not families of graphs,
-- and no monoidal or coproduct structure is constructed.  The free object over
-- the closed relation is not built here.
------------------------------------------------------------------------

module Poly.Congruence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
  using (hProp ; isSetHProp ; isPropΠ ; isPropΠ2 ; isProp×)
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; Σ≡Prop)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Cubical.Data.Bool.Properties using (isSetBool)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties
  using (discreteFin ; isSetFin ; injSucFin ; znots)
open import Cubical.Data.FinData.FinSet using (DecΣ)
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.SetQuotients as SQ using ([_])

open import Poly.Base using (ZigZagQuotient)
open import Poly.Components using (module Invariant)
import Poly.Schemes as Branch

------------------------------------------------------------------------
-- Finite simple graphs
------------------------------------------------------------------------

Symmetric : {n : ℕ} → (Fin n → Fin n → Bool) → Type
Symmetric edge = ∀ x y → edge x y ≡ edge y x

Loopless : {n : ℕ} → (Fin n → Fin n → Bool) → Type
Loopless edge = ∀ x → edge x x ≡ false

Graph : ℕ → Type
Graph n = Σ[ edge ∈ (Fin n → Fin n → Bool) ]
          (Symmetric edge × Loopless edge)

graph-laws-prop : {n : ℕ} (edge : Fin n → Fin n → Bool)
                 → isProp (Symmetric edge × Loopless edge)
graph-laws-prop edge =
  isProp× (isPropΠ2 λ x y → isSetBool _ _)
          (isPropΠ λ x → isSetBool _ _)

graph-ext : {n : ℕ} {G H : Graph n}
          → (∀ x y → G .fst x y ≡ H .fst x y) → G ≡ H
graph-ext p = Σ≡Prop graph-laws-prop (funExt λ x → funExt λ y → p x y)

emptyGraph : {n : ℕ} → Graph n
emptyGraph = (λ _ _ → false) , ((λ _ _ → refl) , (λ _ → refl))

apart : {n : ℕ} → Fin n → Fin n → Bool
apart x y with discreteFin x y
... | yes _ = false
... | no  _ = true

apart-sym : {n : ℕ} (x y : Fin n) → apart x y ≡ apart y x
apart-sym x y with discreteFin x y | discreteFin y x
... | yes _  | yes _  = refl
... | no  _  | no  _  = refl
... | yes p  | no np  = Empty.rec (np (sym p))
... | no np  | yes p  = Empty.rec (np (sym p))

apart-loopless : {n : ℕ} (x : Fin n) → apart x x ≡ false
apart-loopless x with discreteFin x x
... | yes _ = refl
... | no nx = Empty.rec (nx refl)

completeGraph : {n : ℕ} → Graph n
completeGraph = apart , (apart-sym , apart-loopless)

------------------------------------------------------------------------
-- Split injections and graph restriction
------------------------------------------------------------------------

record SplitInj (k l : ℕ) : Type where
  field
    to        : Fin k → Fin l
    injective : {x y : Fin k} → to x ≡ to y → x ≡ y
    from      : Fin l → Fin k
    section   : ∀ x → from (to x) ≡ x

open SplitInj

-- Every injection with a positive finite source splits.  Search its finite
-- source for a preimage; outside the image use the distinguished first source
-- element.  This removes "split" as a hypothesis from the actual step
-- relation below.
preimage? : {k l : ℕ} (f : Fin k → Fin l) (y : Fin l)
          → Dec (Σ[ x ∈ Fin k ] f x ≡ y)
preimage? {k} f y = DecΣ k (λ x → f x ≡ y) (λ x → discreteFin (f x) y)

split-injection : {k l : ℕ} → Branch.Inj (suc k) l
                → SplitInj (suc k) l
split-injection {k} {l} (f , inj) = record
  { to = f
  ; injective = inj
  ; from = choose
  ; section = choose-section
  }
  where
  choose : Fin l → Fin (suc k)
  choose y with preimage? f y
  ... | yes (x , _) = x
  ... | no _ = zero

  choose-section : ∀ x → choose (f x) ≡ x
  choose-section x with preimage? f (f x)
  ... | yes (z , p) = inj p
  ... | no n = Empty.rec (n (x , refl))

restrict : {k l : ℕ} → SplitInj k l → Graph l → Graph k
restrict i G =
  (λ x y → G .fst (to i x) (to i y)) ,
  ((λ x y → G .snd .fst (to i x) (to i y)) ,
   (λ x → G .snd .snd (to i x)))

extend : {k l : ℕ} → SplitInj k l → Graph k → Graph l
extend i G =
  (λ x y → G .fst (from i x) (from i y)) ,
  ((λ x y → G .snd .fst (from i x) (from i y)) ,
   (λ x → G .snd .snd (from i x)))

restrict-extend : {k l : ℕ} (i : SplitInj k l) (G : Graph k)
                → restrict i (extend i G) ≡ G
restrict-extend i G = graph-ext λ x y →
  cong₂ (G .fst) (section i x) (section i y)

------------------------------------------------------------------------
-- One-block graph-dependent choice functions
------------------------------------------------------------------------

GraphChoice : Type
GraphChoice = Σ[ k ∈ ℕ ] (Graph (suc k) → Fin (suc k))

OneStep : GraphChoice → GraphChoice → Type
OneStep (k , f) (l , g) =
  Σ[ i ∈ Branch.Inj (suc k) (suc l) ]
    (∀ G → i .fst (f (restrict (split-injection i) G)) ≡ g G)

Constant : GraphChoice → Type
Constant (_ , f) = ∀ G H → f G ≡ f H

constant-prop : (x : GraphChoice) → isProp (Constant x)
constant-prop (_ , f) = isPropΠ2 λ G H → isSetFin _ _

constantHProp : GraphChoice → hProp ℓ-zero
constantHProp x = Constant x , constant-prop x

constant-preserved : {x y : GraphChoice} → OneStep x y
                   → Constant x → Constant y
constant-preserved {k , f} {l , g} (i , commute) cf G H =
  sym (commute G)
  ∙ cong (i .fst)
      (cf (restrict (split-injection i) G)
          (restrict (split-injection i) H))
  ∙ commute H

constant-reflected : {x y : GraphChoice} → OneStep x y
                   → Constant y → Constant x
constant-reflected {k , f} {l , g} (i , commute) cg G H =
  i .snd (
      cong (i .fst) (cong f (sym (restrict-extend si G)))
    ∙ commute (extend si G)
    ∙ cg (extend si G) (extend si H)
    ∙ sym (commute (extend si H))
    ∙ cong (i .fst) (cong f (restrict-extend si H)))
  where
  si = split-injection i

constant-step : {x y : GraphChoice} → OneStep x y
              → constantHProp x ≡ constantHProp y
constant-step {x} {y} st =
  Σ≡Prop (λ _ → isPropIsProp)
    (hPropExt (constant-prop x) (constant-prop y)
      (constant-preserved st) (constant-reflected st))

module ConstInvariant =
  Invariant {Step = OneStep} isSetHProp constantHProp constant-step

------------------------------------------------------------------------
-- The edge-test precomposition
------------------------------------------------------------------------

-- Add the two vertices inspected by the edge test at the front of the heap.
-- The old heap begins after them.  The branch chooses which old vertex to
-- return.
precomposeEdge : Branch.Rep → GraphChoice
precomposeEdge (k , (a , b)) = suc k , choose
  where
  choose : Graph (suc (suc k)) → Fin (suc (suc k))
  choose G = if G .fst zero (suc zero)
             then suc (suc a)
             else suc (suc b)

floated-constant : Constant (precomposeEdge Branch.shared)
floated-constant G H with G .fst zero (suc zero) | H .fst zero (suc zero)
... | true  | true  = refl
... | true  | false = refl
... | false | true  = refl
... | false | false = refl

branch-local-nonconstant : ¬ Constant (precomposeEdge Branch.fresh)
branch-local-nonconstant c =
  znots (injSucFin (injSucFin (c completeGraph emptyGraph)))

one-block-separates :
  ¬ (Path (ZigZagQuotient OneStep)
          [ precomposeEdge Branch.shared ]
          [ precomposeEdge Branch.fresh ])
one-block-separates = ConstInvariant.separates not-same
  where
  not-same : ¬ (constantHProp (precomposeEdge Branch.shared)
              ≡ constantHProp (precomposeEdge Branch.fresh))
  not-same p = branch-local-nonconstant
    (transport (cong fst p) floated-constant)

------------------------------------------------------------------------
-- Any branch-local repair fails closure under this precomposition
------------------------------------------------------------------------

module _ {ℓb ℓo : Level}
         (BranchRel : Branch.Rep → Branch.Rep → Type ℓb)
         (OneRel : GraphChoice → GraphChoice → Type ℓo) where

  IdentifiesBranches : Type ℓb
  IdentifiesBranches = BranchRel Branch.shared Branch.fresh

  RigidOnOneBlock : Type ℓo
  RigidOnOneBlock = {x y : GraphChoice} → OneRel x y
                  → Path (ZigZagQuotient OneStep) [ x ] [ y ]

  ClosedUnderPrecomposition : Type (ℓ-max ℓb ℓo)
  ClosedUnderPrecomposition = {x y : Branch.Rep} → BranchRel x y
                            → OneRel (precomposeEdge x) (precomposeEdge y)

  no-branch-local-repair : IdentifiesBranches → RigidOnOneBlock
                         → ¬ ClosedUnderPrecomposition
  no-branch-local-repair related rigid closed =
    one-block-separates (rigid (closed related))

-- Their independent, one-injection-per-branch step is a concrete
-- instance of condition (1), by the already checked witness.
independent-not-closed :
  {ℓo : Level} (OneRel : GraphChoice → GraphChoice → Type ℓo)
  → ({x y : GraphChoice} → OneRel x y
      → Path (ZigZagQuotient OneStep) [ x ] [ y ])
  → ¬ ({x y : Branch.Rep} → Branch.IStep x y
       → OneRel (precomposeEdge x) (precomposeEdge y))
independent-not-closed OneRel rigid =
  no-branch-local-repair Branch.IStep OneRel Branch.independent-step rigid
