------------------------------------------------------------------------
-- The Agda standard library
--
-- Categorical properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Negation.Categorical where

open import Category.Monad using (RawMonad)
open import Level using (Level)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬¬-map; contradiction; negated-stable)

private
  variable
    p : Level
    P : Set p

------------------------------------------------------------------------

-- Double-negation is a monad (if we assume that all elements of ¬ ¬ P
-- are equal).

¬¬-Monad : RawMonad (λ (P : Set p) → ¬ ¬ P)
¬¬-Monad = record
  { return = contradiction
  ; _>>=_  = λ x f → negated-stable (¬¬-map f x)
  }
