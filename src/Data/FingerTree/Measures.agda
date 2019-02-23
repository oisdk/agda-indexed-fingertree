{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree.Measures
  {r m}
  (ℳ : Monoid r m)
  where

open import Level using (_⊔_)

open Monoid ℳ renaming (Carrier to 𝓡)
open import Data.List as List using (List; _∷_; [])
open import Data.Product

record σ {a} (Σ : Set a) : Set (a ⊔ r) where field μ : Σ → 𝓡
open σ ⦃ ... ⦄
{-# DISPLAY σ.μ _ = μ #-}

-- This is of course just a foldr, but written explicitly like
-- this gives better type names
μ-list : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → List Σ → 𝓡
μ-list [] = ε
μ-list (x ∷ xs) = μ x ∙ μ-list xs

instance
  σ-List : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (List Σ)
  μ ⦃ σ-List ⦄ = μ-list
{-# DISPLAY μ-list _ xs = μ xs #-}


-- A "fiber" (I think).
--
--   ⟨ Σ ⟩μ⁻¹[ x ]
--
-- Means "The Σ such that μ Σ ≈ x"

infixr 4 _↦_
record ⟨_⟩μ⁻¹[_] {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (𝑌 : 𝓡) : Set (a ⊔ r ⊔ m) where
  constructor _↦_
  field
    𝓢 : Σ
    μ⟨𝓢⟩≈𝑌 : μ 𝓢 ≈ 𝑌
open ⟨_⟩μ⁻¹[_]

μ[_] : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (𝓢 : Σ) → ⟨ Σ ⟩μ⁻¹[ μ 𝓢 ]
𝓢 μ[ x ] = x
μ⟨𝓢⟩≈𝑌 μ[ x ] = refl

⟪_⟫ : ∀ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ → Set (a ⊔ r ⊔ m)
⟪ Σ ⟫ = ∃ ⟨ Σ ⟩μ⁻¹[_]

⟅_⟆ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Σ → ⟪ Σ ⟫
⟅ x ⟆ = μ x , μ[ x ]

infixr 2 ⟪⟫-syntax
⟪⟫-syntax : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (𝓢 : Σ) → (𝑌 : 𝓡) → μ 𝓢 ≈ 𝑌 → ⟪ Σ ⟫
⟪⟫-syntax 𝓢 𝑌 μ⟨𝓢⟩≈𝑌 = 𝑌 , 𝓢 ↦ μ⟨𝓢⟩≈𝑌

syntax ⟪⟫-syntax 𝓢 𝑌 μ⟨𝓢⟩≈𝑌 = 𝓢 μ≈⟨ μ⟨𝓢⟩≈𝑌 ⟩ 𝑌

instance
  σ-⟪⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → σ ⟪ Σ ⟫
  μ ⦃ σ-⟪⟫ ⦄ = proj₁
