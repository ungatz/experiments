{-# OPTIONS --cubical --safe --guardedness --no-import-sorts #-}

------------------------------------------------------------------------
-- Two reindexing schemes, and what separates them
--
-- Strip the polynomial category down to the combinatorial core of the
-- question.  A representative is a heap size together with a record of which
-- cell each of two branches reads:
--
--     Rep = Sigma k. (Fin k x Fin k)
--
-- Reindexing along an injection is composition with it, and the two schemes
-- differ in exactly one place, visible as two step relations below.  The
-- uniform scheme reindexes both branches by ONE injection.  The independent
-- scheme reindexes them by a PAIR, one injection per branch.
--
-- The two programs of interest are then literally two representatives: one
-- that draws a single cell and routes it into both branches, and one that
-- draws a cell in each branch.  Under the uniform scheme they stay apart, and
-- the invariant that keeps them apart is whether the two branches read the
-- same cell, which no single injection can change.  Under the independent
-- scheme one step identifies them.
--
-- So the choice of scheme is not presentational.  It decides whether the two
-- programs are equal, and the uniform scheme is Hermida and Tennent's.
--
-- This is the relation level only.  There is no monoidal category here, no
-- base and no interpretation: only finite sets and injections.  Nothing about
-- composition is proved in this module.
------------------------------------------------------------------------

module Poly.Schemes where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; true≢false)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.FinData.Properties using (discreteFin ; isContrFin1)
open import Cubical.Relation.Nullary using (¬_ ; yes ; no)
import Cubical.Data.Empty as Empty
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/)

open import Poly.Base
open import Poly.Components using (module Invariant)

----------------------------------------------------------------------
-- Injections, and the two representatives
----------------------------------------------------------------------

Inj : ℕ → ℕ → Type
Inj k l = Σ[ f ∈ (Fin k → Fin l) ] ({x y : Fin k} → f x ≡ f y → x ≡ y)

Rep : Type
Rep = Σ[ k ∈ ℕ ] (Fin k × Fin k)

shared : Rep
shared = 1 , (zero , zero)

fresh : Rep
fresh = 2 , (zero , suc zero)

----------------------------------------------------------------------
-- The two schemes
----------------------------------------------------------------------

-- One injection, applied to both branches.
UStep : Rep → Rep → Type
UStep (k , (a , b)) (l , (a' , b')) =
  Σ[ i ∈ Inj k l ] ((i .fst a ≡ a') × (i .fst b ≡ b'))

-- One injection PER BRANCH.  This is the only difference.
IStep : Rep → Rep → Type
IStep (k , (a , b)) (l , (a' , b')) =
  Σ[ i ∈ Inj k l ] Σ[ j ∈ Inj k l ] ((i .fst a ≡ a') × (j .fst b ≡ b'))

-- The uniform scheme is contained in the independent one: take j = i.
UStep→IStep : {x y : Rep} → UStep x y → IStep x y
UStep→IStep (i , (p , q)) = i , (i , (p , q))

----------------------------------------------------------------------
-- The invariant: do the two branches read the same cell?
----------------------------------------------------------------------

same? : {k : ℕ} → Fin k → Fin k → Bool
same? a b with discreteFin a b
... | yes _ = true
... | no  _ = false

chi : Rep → Bool
chi (_ , (a , b)) = same? a b

-- An injection cannot change the answer: it preserves equality by
-- congruence and reflects it by injectivity.  Both directions are used,
-- and this is the whole of the separation.
chi-UStep : {x y : Rep} → UStep x y → chi x ≡ chi y
chi-UStep {k , (a , b)} {l , (a' , b')} (i , (p , q)) = lemma
  where
  f = i .fst
  lemma : same? a b ≡ same? a' b'
  lemma with discreteFin a b | discreteFin a' b'
  ... | yes _  | yes _  = refl
  ... | no  _  | no  _  = refl
  ... | yes e  | no ne  = Empty.rec (ne (sym p ∙ cong f e ∙ q))
  ... | no  ne | yes e  = Empty.rec (ne (i .snd (p ∙ e ∙ sym q)))

----------------------------------------------------------------------
-- Half one: the uniform quotient keeps them apart
----------------------------------------------------------------------

open import Cubical.Data.Bool using (isSetBool)

module U = Invariant {Step = UStep} isSetBool chi chi-UStep

chi-shared : chi shared ≡ true
chi-shared = refl

chi-fresh : chi fresh ≡ false
chi-fresh = refl

-- THE FIRST HALF.  In the ordinary (uniform) construction the two
-- programs are not identified.
uniform-separates : ¬ (Path (ZigZagQuotient UStep) [ shared ] [ fresh ])
uniform-separates = U.separates λ e → true≢false (sym chi-shared ∙ e ∙ chi-fresh)

----------------------------------------------------------------------
-- Half two: the independent quotient identifies them
----------------------------------------------------------------------

-- Fin 1 -> Fin 2 hitting the first cell, and the second.
private
  to0 : Fin 1 → Fin 2
  to0 _ = zero

  to1 : Fin 1 → Fin 2
  to1 _ = suc zero

  -- Both are injective for the trivial reason that Fin 1 is
  -- contractible: any two elements of the source are already equal.
  -- Taken from the library rather than pattern-matched here, because
  -- matching on Fin 1 needs injectivity of `suc` at an index, which
  -- Cubical Agda flags as an unsupported indexed match.
  fin1-prop : (x y : Fin 1) → x ≡ y
  fin1-prop x y = sym (isContrFin1 .snd x) ∙ isContrFin1 .snd y

  inj0 : Inj 1 2
  inj0 = to0 , λ {x} {y} _ → fin1-prop x y

  inj1 : Inj 1 2
  inj1 = to1 , λ {x} {y} _ → fin1-prop x y

-- THE SECOND HALF.  With one injection per branch, the step exists.
independent-step : IStep shared fresh
independent-step = inj0 , (inj1 , (refl , refl))

independent-identifies : Path (ZigZagQuotient IStep) [ shared ] [ fresh ]
independent-identifies = eq/ shared fresh (zz-step independent-step)

----------------------------------------------------------------------
-- The separation, stated once
----------------------------------------------------------------------

-- The two schemes differ, and they differ at this pair.  The containment
-- runs one way: every uniform step IS an independent one, so the
-- independent quotient is coarser, and strictly so here.
schemes-differ :
  (¬ (Path (ZigZagQuotient UStep) [ shared ] [ fresh ]))
  × (Path (ZigZagQuotient IStep) [ shared ] [ fresh ])
schemes-differ = uniform-separates , independent-identifies
