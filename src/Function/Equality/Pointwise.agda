------------------------------------------------------------------------
-- The Agda standard library
--
-- Function setoids, Pointwise versions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Equality.Pointwise where

import Function.Base as Fun
open import Level
open import Relation.Binary using (Setoid)
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
  as Trivial
open import Relation.Binary.PropositionalEquality using (setoid; refl)
open import Function.Equality using (Π; _⟶_; ≡-setoid)

------------------------------------------------------------------------
-- Pointwise equality

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b

infix 4 _≗_

_→-setoid_ : ∀ (A : Set a) (B : Set b) → Setoid _ _
A →-setoid B = ≡-setoid A (Trivial.indexedSetoid (setoid B))

_≗_ : (f g : A → B) → Set _
_≗_ {A = A} {B = B} = Setoid._≈_ (A →-setoid B)

:→-to-Π : ∀ {A : Set a} {B : IndexedSetoid A b ℓ} →
          ((x : A) → IndexedSetoid.Carrier B x) → Π (setoid A) B
:→-to-Π {B = B} f = record
  { _⟨$⟩_ = f
  ; cong  = λ { refl → IndexedSetoid.refl B }
  }
  where open IndexedSetoid B using (_≈_)

→-to-⟶ : ∀ {A : Set a} {B : Setoid b ℓ} →
         (A → Setoid.Carrier B) → setoid A ⟶ B
→-to-⟶ = :→-to-Π
