{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree.Structures
  {r m}
  (ℳ : Monoid r m)
  where

open import Level using (_⊔_)
open import Data.Product
open import Relation.Unary

open import Data.FingerTree.Measures ℳ
open import Data.FingerTree.Reasoning ℳ

open Monoid ℳ renaming (Carrier to 𝓡)
open σ ⦃ ... ⦄
{-# DISPLAY σ.μ _ = μ #-}

data Digit {a} (Σ : Set a) : Set a where
  D₁ : Σ → Digit Σ
  D₂ : Σ → Σ → Digit Σ
  D₃ : Σ → Σ → Σ → Digit Σ
  D₄ : Σ → Σ → Σ → Σ → Digit Σ

instance
  σ-Digit : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Digit Σ)
  μ ⦃ σ-Digit ⦄ (D₁ x₁) = μ x₁
  μ ⦃ σ-Digit ⦄ (D₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ σ-Digit ⦄ (D₃ x₁ x₂ x₃) = μ x₁ ∙ (μ x₂ ∙ μ x₃)
  μ ⦃ σ-Digit ⦄ (D₄ x₁ x₂ x₃ x₄) = μ x₁ ∙ (μ x₂ ∙ (μ x₃ ∙ μ x₄))

data Node {a} (Σ : Set a) : Set a where
  N₂ : Σ → Σ → Node Σ
  N₃ : Σ → Σ → Σ → Node Σ

instance
  σ-Node : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Node Σ)
  μ ⦃ σ-Node ⦄ (N₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ σ-Node ⦄ (N₃ x₁ x₂ x₃) = μ x₁ ∙ (μ x₂ ∙ μ x₃)

mutual
  infixr 5 _&_&_
  record Deep {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (r ⊔ a ⊔ m) where
    constructor _&_&_
    inductive
    field
      lbuff : Digit Σ
      tree  : Tree ⟪ Node Σ ⟫
      rbuff : Digit Σ

  data Tree {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (r ⊔ a ⊔ m) where
    empty : Tree Σ
    single : Σ → Tree Σ
    deep : ⟪ Deep Σ ⟫  → Tree Σ

  μ-deep : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Deep Σ → 𝓡
  μ-deep (l & x & r) = μ l ∙ (μ-tree x ∙ μ r)

  μ-tree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Tree Σ → 𝓡
  μ-tree empty = ε
  μ-tree (single x) = μ x
  μ-tree (deep xs) = xs .proj₁

  instance
    σ-Deep : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Deep Σ)
    μ ⦃ σ-Deep ⦄ = μ-deep

  instance
    σ-Tree : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Tree Σ)
    μ ⦃ σ-Tree ⦄ = μ-tree
open Deep

{-# DISPLAY μ-tree _ x = μ x #-}
{-# DISPLAY μ-deep _ x = μ x #-}

nodeToDigit : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Node Σ) →  ⟨ Digit Σ ⟩μ⁻¹ (μ xs)
nodeToDigit (N₂ x₁ x₂) = D₂ x₁ x₂ ↦ refl
nodeToDigit (N₃ x₁ x₂ x₃) = D₃ x₁ x₂ x₃ ↦ refl

digitToTree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Digit Σ ) → ⟨ Tree Σ ⟩μ⁻¹ (μ xs)
digitToTree (D₁ x₁ ) = single x₁ ↦ refl
digitToTree (D₂ x₁ x₂ ) = deep ⟪ D₁ x₁ & empty & D₁ x₂ ⇓⟫ ↦ (μ x₁ ∙ (ε ∙ μ x₂) ↢ ℳ ↯)
digitToTree (D₃ x₁ x₂ x₃ ) = deep ⟪ D₂ x₁ x₂ & empty & D₁ x₃ ⇓⟫ ↦ (μ (D₂ x₁ x₂) ∙ (ε ∙ μ x₃) ↢ ℳ ↯)
digitToTree (D₄ x₁ x₂ x₃ x₄ ) = deep ⟪ D₂ x₁ x₂ & empty & D₂ x₃ x₄ ⇓⟫ ↦ (μ (D₂ x₁ x₂) ∙ (ε ∙ μ (D₂ x₃ x₄)) ↢ ℳ ↯)
