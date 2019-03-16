{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Unary
open import Relation.Binary hiding (Decidable)

module Data.FingerTree.Split.StoredPredicate
  {r m}
  (ℳ : Monoid r m)
  {s}
  {ℙ : Pred (Monoid.Carrier ℳ) s}
  (ℙ-resp : ℙ Respects (Monoid._≈_ ℳ))
  (ℙ? : Decidable ℙ)
  where

open Monoid ℳ renaming (Carrier to 𝓡)
open import Level using (_⊔_)
open import Relation.Nullary

infixl 2 _≈ℙ_[_]
record ⟪ℙ⟫ (x : 𝓡) : Set (s ⊔ r ⊔ m) where
  constructor _≈ℙ_[_]
  field
    result : Dec (ℙ x)
    stored : 𝓡
    equiv  : stored ≈ x
open ⟪ℙ⟫ public

⟪ℙ?⟫ : ∀ x → ⟪ℙ⟫ x
result (⟪ℙ?⟫ x) = ℙ? x
stored (⟪ℙ?⟫ x) = x
equiv  (⟪ℙ?⟫ x) = refl
