------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Bool.Base using (T)
open import Data.Maybe.Relation.Unary.All
open import Data.Maybe.Relation.Unary.Any
open import Data.These.Base using (These; these; this; that)
open import Function.Base using (id)
open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- The base type and some operations

open import Data.Maybe.Base public

------------------------------------------------------------------------
-- Using Any and All to define Is-just and Is-nothing

Is-just : Maybe A → Set _
Is-just = Any (λ _ → ⊤)

Is-nothing : Maybe A → Set _
Is-nothing = All (λ _ → ⊥)

to-witness : ∀ {m : Maybe A} → Is-just m → A
to-witness (just {x = p} _) = p

to-witness-T : ∀ (m : Maybe A) → T (is-just m) → A
to-witness-T (just p) _  = p

------------------------------------------------------------------------
-- Aligning

alignWith : (These A B → C) → Maybe A → Maybe B → Maybe C
alignWith f (just a) (just b) = just (f (these a b))
alignWith f (just a) nothing  = just (f (this a))
alignWith f nothing  (just b) = just (f (that b))
alignWith f nothing  nothing  = nothing

align : Maybe A → Maybe B → Maybe (These A B)
align = alignWith id

------------------------------------------------------------------------
-- Injections.

thisM : A → Maybe B → These A B
thisM a = maybe′ (these a) (this a)

thatM : Maybe A → B → These A B
thatM = maybe′ these that
