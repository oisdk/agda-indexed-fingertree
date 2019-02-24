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
-- infixl 5 _▸_

_◂_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (x : Σ) → (xs : Tree Σ) → μ⟨ Tree Σ ⟩≈ (μ x ∙ μ xs)
a ◂ empty = single a ⇑[ ℳ ↯ ]
a ◂ single b = deep ⟪ D₁ a & empty & D₁ b ⇓⟫ ⇑[ ℳ ↯ ]
a ◂ deep (𝓂 ↤ (D₁ b       & m & rs ⇑[ 𝓂≈ ])) = pure (deep (μ a ∙ 𝓂 ↤ D₂ a b     & m & rs ⇑[ assoc _ _ _ ⍮ ∙≫ 𝓂≈ ]))
a ◂ deep (𝓂 ↤ (D₂ b c     & m & rs ⇑[ 𝓂≈ ])) = pure (deep (μ a ∙ 𝓂 ↤ D₃ a b c   & m & rs ⇑[ assoc _ _ _ ⍮ ∙≫ 𝓂≈ ]))
a ◂ deep (𝓂 ↤ (D₃ b c d   & m & rs ⇑[ 𝓂≈ ])) = pure (deep (μ a ∙ 𝓂 ↤ D₄ a b c d & m & rs ⇑[ assoc _ _ _ ⍮ ∙≫ 𝓂≈ ]))
a ◂ deep (𝓂 ↤ (D₄ b c d e & m & rs ⇑[ 𝓂≈ ])) with ⟪ N₃ c d e ⇓⟫ ◂ m
... | m′ ⇑[ m′≈ ] = pure (deep (μ a ∙ 𝓂 ↤ D₂ a b & m′ & rs ⇑[ ∙≫ ≪∙ m′≈ ] ≈[ ℳ ↯ ] ≈[ ∙≫ 𝓂≈ ]′))

_◂′_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (x : Σ) → ∀ {xs} → μ⟨ Tree Σ ⟩≈ xs → μ⟨ Tree Σ ⟩≈ (μ x ∙ xs)
x ◂′ (xs ⇑[ p ]) = (x ◂ xs) ≈[ ∙≫ p ]

open import Data.List as List using (List; _∷_; [])

listToTree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : List Σ) → μ⟨ Tree Σ ⟩≈ (μ xs)
listToTree [] = pure empty
listToTree (x ∷ xs) = listToTree xs [ _ ∙> s ⟿ s ] λ ys → x ◂ ys ≈[ ℳ ↯ ]

-- _▸_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → (x : Σ) → ⟨ Tree Σ ⟩μ⁻¹ (μ xs ∙ μ x)
-- empty ▸ a = single a ↦ ℳ ↯
-- single a ▸ b = deep ⟪ D₁ a & empty & D₁ b ⇓⟫ ↦ ℳ ↯
-- deep (μ⟨𝓢⟩ , ls & m & D₁ a       ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ b = deep (ls & m & D₂ a b     μ≈⟨ ℳ ↯ ⍮′ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ b) ↦ refl
-- deep (μ⟨𝓢⟩ , ls & m & D₂ a b     ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ c = deep (ls & m & D₃ a b c   μ≈⟨ ℳ ↯ ⍮′ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ c) ↦ refl
-- deep (μ⟨𝓢⟩ , ls & m & D₃ a b c   ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ d = deep (ls & m & D₄ a b c d μ≈⟨ ℳ ↯ ⍮′ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ d) ↦ refl
-- deep (μ⟨𝓢⟩ , ls & m & D₄ a b c d ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ e with m ▸ ⟪ N₃ a b c ⇓⟫
-- ... | m′ ↦ m∙a∙b∙c≈μ⟨m′⟩ = deep ( ls & m′ & D₂ d e μ≈⟨ lemma ⟩ μ⟨𝓢⟩ ∙ μ e ) ↦ refl
--   where
--   lemma =
--     begin
--       μ (ls & m′ & D₂ d e)
--     ≡⟨⟩
--       μ ls ∙ (μ m′ ∙ (μ d ∙ μ e))
--     ≈˘⟨ ∙≫ ≪∙ sym m∙a∙b∙c≈μ⟨m′⟩ ⟩
--       μ ls ∙ (μ m ∙ (μ a ∙ (μ b ∙ μ c)) ∙ (μ d ∙ μ e))
--     ≈⟨ ℳ ↯ ⟩
--       μ ls ∙ (μ m ∙ (μ a ∙ (μ b ∙ (μ c ∙ μ d)))) ∙ μ e
--     ≈⟨ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩
--       μ⟨𝓢⟩ ∙ μ e
--     ∎

-- _▸′_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → ∀ {xs} → ⟨ Tree Σ ⟩μ⁻¹ xs → (x : Σ) → ⟨ Tree Σ ⟩μ⁻¹ (xs ∙ μ x)
-- (xs ↦ p) ▸′ x = (xs ▸ x) ≈[ ≪∙ p ]
