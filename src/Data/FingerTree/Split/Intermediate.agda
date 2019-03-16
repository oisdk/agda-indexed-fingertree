{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Unary
open import Relation.Binary hiding (Decidable)

module Data.FingerTree.Split.Intermediate
  {r m}
  (ℳ : Monoid r m)
  {s}
  {ℙ : Pred (Monoid.Carrier ℳ) s}
  (ℙ-resp : ℙ Respects (Monoid._≈_ ℳ))
  (ℙ? : Decidable ℙ)
  where

open import Relation.Nullary using (¬_; yes; no; Dec)
open import Level using (_⊔_)
open import Data.Product
open import Function
open import Data.List as List using (List; _∷_; [])

open import Data.FingerTree.Measures ℳ
open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Reasoning ℳ
open import Data.FingerTree.View ℳ using (deepₗ; deepᵣ)
open import Data.FingerTree.Cons ℳ using (listToTree)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; False; toWitnessFalse)

open σ ⦃ ... ⦄

open Monoid ℳ renaming (Carrier to 𝓡)

open import Data.FingerTree.Relation.Binary.Reasoning.FasterInference.Setoid setoid

open import Data.FingerTree.Split.Point ℳ ℙ-resp ℙ?
open import Data.FingerTree.Split.StoredPredicate ℳ ℙ-resp ℙ?

open import Data.Empty.Irrelevant using (⊥-elim)

record Split′ (i : 𝓡) {a b} (Σ : Set a) (A : Set b) ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ : Set (a ⊔ b ⊔ s) where
  constructor _∷⟨_⟩∷_[_]
  field
    left′  : Σ
    focus′ : A
    right′ : Σ
    .proof′ : i ∙ μ left′ ∣ μ focus′
open Split′ public
instance
  σ-Split′ : ∀  {a b} {Σ : Set a} {A : Set b} ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ {i : 𝓡} → σ (Split′ i Σ A)
  μ ⦃ σ-Split′ {i = i} ⦄ (l ∷⟨ x ⟩∷ r [ _ ]) = i ∙ (μ l ∙ (μ x ∙ μ r))

infixl 2 _i≈[_]
_i≈[_] : ∀ {a b} {Σ : Set a} {A : Set b} ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄
          → ∀ {i xs}
          → μ⟨ Split′ i Σ A ⟩≈ (i ∙ xs)
          → ∀ {j}
          → i ≈ j → μ⟨ Split′ j Σ A ⟩≈ (j ∙ xs)
xs ∷⟨ x ⟩∷ ys [ p₁ ] ⇑[ p₂ ] i≈[ i≈ ] = xs ∷⟨ x ⟩∷ ys [ p₁ ≈◄⟅ ≪∙ i≈ ⟆ ] ⇑[ ≪∙ sym i≈ ⍮ p₂ ⍮ ≪∙ i≈ ]
{-# INLINE _i≈[_] #-}
