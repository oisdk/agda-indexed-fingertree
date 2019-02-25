{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree.Cons
  {r m}
  (ℳ : Monoid r m)
  where

open import Data.Product

open import Data.FingerTree.Measures ℳ
open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Reasoning ℳ

open σ ⦃ ... ⦄
{-# DISPLAY σ.μ _ x = μ x #-}
{-# DISPLAY μ-tree _ x = μ x #-}
{-# DISPLAY μ-deep _ x = μ x #-}

open Monoid ℳ renaming (Carrier to 𝓡)

infixr 5 _◂_
infixl 5 _▸_

_◂_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (x : Σ) → (xs : Tree Σ) → μ⟨ Tree Σ ⟩≈ (μ x ∙ μ xs)
a ◂ empty = single a ⇑[ ℳ ↯ ]
a ◂ single b = deep ⟪ D₁ a & empty & D₁ b ⇓⟫ ⇑[ ℳ ↯ ]
a ◂ deep (𝓂 ↤ D₁ b       & m & rs ⇑[ 𝓂≈ ]) = deep (μ a ∙ 𝓂 ↤ D₂ a b     & m & rs ⇑[ assoc _ _ _ ⍮ ∙≫ 𝓂≈ ]) ⇑
a ◂ deep (𝓂 ↤ D₂ b c     & m & rs ⇑[ 𝓂≈ ]) = deep (μ a ∙ 𝓂 ↤ D₃ a b c   & m & rs ⇑[ assoc _ _ _ ⍮ ∙≫ 𝓂≈ ]) ⇑
a ◂ deep (𝓂 ↤ D₃ b c d   & m & rs ⇑[ 𝓂≈ ]) = deep (μ a ∙ 𝓂 ↤ D₄ a b c d & m & rs ⇑[ assoc _ _ _ ⍮ ∙≫ 𝓂≈ ]) ⇑
a ◂ deep (𝓂 ↤ D₄ b c d e & m & rs ⇑[ 𝓂≈ ]) with ⟪ N₃ c d e ⇓⟫ ◂ m
... | m′ ⇑[ m′≈ ] = deep (μ a ∙ 𝓂 ↤ D₂ a b & m′ & rs ⇑[ ∙≫ ≪∙ m′≈ ] ≈[ ℳ ↯ ] ≈[ ∙≫ 𝓂≈ ]′) ⇑

_▸_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → (x : Σ) → μ⟨ Tree Σ ⟩≈ (μ xs ∙ μ x)
empty ▸ a = single a ⇑[ ℳ ↯ ]
single a ▸ b = deep ⟪ D₁ a & empty & D₁ b ⇓⟫ ⇑[ ℳ ↯ ]
deep (𝓂 ↤ ls & m & D₁ a       ⇑[ 𝓂≈ ]) ▸ b = deep (𝓂 ∙ μ b ↤ ls & m & D₂ a b     ⇑[ ℳ ↯ ⍮′ ≪∙ 𝓂≈ ]) ⇑
deep (𝓂 ↤ ls & m & D₂ a b     ⇑[ 𝓂≈ ]) ▸ c = deep (𝓂 ∙ μ c ↤ ls & m & D₃ a b c   ⇑[ ℳ ↯ ⍮′ ≪∙ 𝓂≈ ]) ⇑
deep (𝓂 ↤ ls & m & D₃ a b c   ⇑[ 𝓂≈ ]) ▸ d = deep (𝓂 ∙ μ d ↤ ls & m & D₄ a b c d ⇑[ ℳ ↯ ⍮′ ≪∙ 𝓂≈ ]) ⇑
deep (𝓂 ↤ ls & m & D₄ a b c d ⇑[ 𝓂≈ ]) ▸ e with m ▸ ⟪ N₃ a b c ⇓⟫
... | m′ ⇑[ m′≈ ] = deep (𝓂 ∙ μ e ↤ ls & m′ & D₂ d e ⇑[ ∙≫ ≪∙ m′≈ ] ≈[ ℳ ↯ ] ≈[ ≪∙ 𝓂≈ ]′) ⇑

open import Data.List as List using (List; _∷_; [])

listToTree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : List Σ) → μ⟨ Tree Σ ⟩≈ (μ xs)
listToTree [] = empty ⇑
listToTree (x ∷ xs) = [ ℳ ↯ ]≈ do
  ys ← listToTree xs [ μ x ∙> s ⟿ s ]
  x ◂ ys
