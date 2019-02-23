{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree.View
  {r m}
  (ℳ : Monoid r m)
  where

open import Level using (_⊔_)
open import Data.Product
open import Function


open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Reasoning ℳ
open import Data.FingerTree.Measures ℳ
open σ ⦃ ... ⦄
{-# DISPLAY σ.μ _ = μ #-}
{-# DISPLAY μ-tree _ x = μ x #-}
{-# DISPLAY μ-deep _ x = μ x #-}

open Monoid ℳ renaming (Carrier to 𝓡)

infixr 5 _◃_
data Viewₗ {a b} (A : Set a) (Σ : Set b) : Set (a ⊔ b) where
  nilₗ : Viewₗ A Σ
  _◃_ : A → Σ → Viewₗ A Σ

instance
  σ-Viewₗ : ∀ {a b} {A : Set a} {Σ : Set b} ⦃ _ : σ A ⦄ ⦃ _ : σ Σ ⦄ → σ (Viewₗ A Σ)
  μ ⦃ σ-Viewₗ ⦄ nilₗ = ε
  μ ⦃ σ-Viewₗ ⦄ (x ◃ xs) = μ x ∙ μ xs

viewₗ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → ⟨ Viewₗ Σ (Tree Σ) ⟩μ⁻¹[ μ xs ]
viewₗ empty = nilₗ ↦ refl
viewₗ (single x) = x ◃ empty ↦ identityʳ _
viewₗ (deep (μ⟨xs⟩ , (D₂ a b     & m & rs) ↦ μ⟨xs⟩≈)) = a ◃ deep (_ , D₁ b     & m & rs ↦ refl) ↦ (ℳ ↯ ⍮′ μ⟨xs⟩≈)
viewₗ (deep (μ⟨xs⟩ , (D₃ a b c   & m & rs) ↦ μ⟨xs⟩≈)) = a ◃ deep (_ , D₂ b c   & m & rs ↦ refl) ↦ (μ a ∙ μ (D₂ b c   & m & rs) ↣⟨ ℳ ↯ ⟩↣ μ (D₃ a b c   & m & rs) ⍮′ μ⟨xs⟩≈)
viewₗ (deep (μ⟨xs⟩ , (D₄ a b c d & m & rs) ↦ μ⟨xs⟩≈)) = a ◃ deep (_ , D₃ b c d & m & rs ↦ refl) ↦ (μ a ∙ μ (D₃ b c d & m & rs) ↣⟨ ℳ ↯ ⟩↣ μ (D₄ a b c d & m & rs) ⍮′ μ⟨xs⟩≈)
viewₗ (deep (μ⟨xs⟩ , (D₁ a & m & rs) ↦ μ⟨xs⟩≈)) with viewₗ m
... | (μ⟨y⟩ , N₂ y₁ y₂ ↦ yp) ◃ ys ↦ p = a ◃ deep (μ m ∙ μ rs , D₂ y₁ y₂ & ys & rs ↦ (μ (D₂ y₁ y₂ & ys & rs) ↣⟨ ℳ ↯ ⟩↣ (μ y₁ ∙ μ y₂ ∙ μ ys ∙ μ rs) ⍮ ≪∙ (≪∙ yp ⍮ p))) ↦ μ⟨xs⟩≈
... | (μ⟨y⟩ , N₃ y₁ y₂ y₃ ↦ yp) ◃ ys ↦ p = a ◃ deep (μ m ∙ μ rs , D₃ y₁ y₂ y₃ & ys & rs ↦ (μ (D₃ y₁ y₂ y₃ & ys & rs) ↣⟨ ℳ ↯ ⟩↣ (μ y₁ ∙ (μ y₂ ∙ μ y₃) ∙ μ ys ∙ μ rs) ⍮ ≪∙ (≪∙ yp ⍮ p))) ↦ μ⟨xs⟩≈
... | nilₗ ↦ p with digitToTree rs
... | rs′ ↦ p′ = a ◃ rs′ ↦ (∙≫ (sym (identityˡ _) ⍮ ∙-cong p p′) ⍮ μ⟨xs⟩≈)
