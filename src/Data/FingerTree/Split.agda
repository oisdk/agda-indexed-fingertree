{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Unary
open import Relation.Binary hiding (Decidable)

module Data.FingerTree.Split
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
open import Data.FingerTree.Split.Intermediate ℳ ℙ-resp ℙ?
open import Data.FingerTree.Split.Structures ℳ ℙ-resp ℙ?

record Split {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (a ⊔ r ⊔ m ⊔ s) where
  constructor _∷⟨_⟩∷_[_]
  field
    left : Tree Σ
    focus : Σ
    right : Tree Σ
    is-split : μ left ∣ μ focus
open Split public

instance
  σ-Split : ∀  {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → σ (Split Σ)
  μ ⦃ σ-Split ⦄ (l ∷⟨ x ⟩∷ r [ _ ]) = μ l ∙ (μ x ∙ μ r)


split : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄
      → {¬ℙ⟨ε⟩ : False (ℙ? ε)}
      → (xs : Tree Σ)
      → {ℙ⟨xs⟩ : True (ℙ? (μ xs))}
      → μ⟨ Split Σ ⟩≈ μ xs
split {¬ℙ⟨ε⟩ = ¬ℙ⟨ε⟩} xs {ℙ⟨xs⟩} with splitTree ε xs (init-ℙ ¬ℙ⟨ε⟩ ℙ⟨xs⟩) ≈[ identityˡ _ ]
... | xs′ ∷⟨ x ⟩∷ ys [ p ] ⇑[ p₂ ] = xs′ ∷⟨ x ⟩∷ ys [ Relation.Nullary.recompute (_ ∣? _) p ≈◄⟅ identityˡ _ ⟆ ] ⇑[  sym (identityˡ _) ⍮ p₂ ]
