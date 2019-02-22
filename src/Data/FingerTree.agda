{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Level using (_⊔_)

module Data.FingerTree
  {c ℓ}
  (measure : Monoid c ℓ)
  {s} {Source : Set s}
  (meas : Source → Monoid.Carrier measure)
  where

open import Data.Product

open Monoid measure

record Measured {a} (A : Set a) : Set (a ⊔ c) where
  field μ : A → Carrier
open Measured ⦃ ... ⦄ public

instance
  measuredSource : Measured Source
  μ ⦃ measuredSource ⦄ = meas

data Digit {a} (A : Set a) : Set a where
  D₁ : A → Digit A
  D₂ : A → A → Digit A
  D₃ : A → A → A → Digit A
  D₄ : A → A → A → A → Digit A

instance
  measuredDigit : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured (Digit A)
  μ ⦃ measuredDigit ⦄ (D₁ x₁) = μ x₁
  μ ⦃ measuredDigit ⦄ (D₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ measuredDigit ⦄ (D₃ x₁ x₂ x₃) = μ x₁ ∙ μ x₂ ∙ μ x₃
  μ ⦃ measuredDigit ⦄ (D₄ x₁ x₂ x₃ x₄) = μ x₁ ∙ μ x₂ ∙ μ x₃ ∙ μ x₄

data Node {a} (A : Set a) : Set a where
  N₂ : A → A → Node A
  N₃ : A → A → A → Node A

instance
  measuredNode : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured (Node A)
  μ ⦃ measuredNode ⦄ (N₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ measuredNode ⦄ (N₃ x₁ x₂ x₃) = μ x₁ ∙ μ x₂ ∙ μ x₃

data μ⟨_⟩⁻¹[_] {a} (A : Set a) ⦃ _ : Measured A ⦄ : Carrier → Set a where
  ⟅_⟆ : (x : A) → μ⟨ A ⟩⁻¹[ μ x ]

⟪_⟫ : ∀ {a} → (A : Set a) → ⦃ _ : Measured A ⦄ → Set (a ⊔ c)
⟪ A ⟫ = ∃ μ⟨ A ⟩⁻¹[_]

instance
  measuredCached : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured ⟪ A ⟫
  μ ⦃ measuredCached ⦄ = proj₁

mutual
  record Deep {a} (A : Set a) ⦃ _ : Measured A ⦄ : Set (c ⊔ a) where
    inductive
    field
      lbuff : Digit A
      tree  : FingerTree ⟪ Node A ⟫
      rbuff : Digit A

  data FingerTree {a} (A : Set a) ⦃ _ : Measured A ⦄ : Set (c ⊔ a) where
    empty : FingerTree A
    single : A → FingerTree A
    deep : ⟪ Deep A ⟫  → FingerTree A

  μ-deep : ∀ {a} {A : Set a} ⦃ _ : Measured A ⦄ → Deep A → Carrier
  μ-deep xs = μ (Deep.lbuff xs) ∙ μ-tree (Deep.tree xs) ∙ μ (Deep.rbuff xs)

  μ-tree : ∀ {a} {A : Set a} ⦃ _ : Measured A ⦄ → FingerTree A → Carrier
  μ-tree empty = ε
  μ-tree (single x₁) = μ x₁
  μ-tree (deep xs) = proj₁ xs

  instance
    measuredDeep : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured (Deep A)
    μ ⦃ measuredDeep ⦄ = μ-deep

  instance
    measuredFingerTree : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured (FingerTree A)
    μ ⦃ measuredFingerTree ⦄ = μ-tree
open Deep
