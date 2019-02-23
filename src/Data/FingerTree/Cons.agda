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

open Monoid ℳ

_◂_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (x : Σ) → (xs : Tree Σ) → ⟨ Tree Σ ⟩μ⁻¹[ μ x ∙ μ xs ]
a ◂ empty = single a ↦ ℳ ↯
a ◂ single b = deep ⟅ D₁ a & empty & D₁ b ⟆ ↦ ℳ ↯
a ◂ deep (μ⟨𝓢⟩ , D₁ b       & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) = deep (D₂ a b     & m & rs μ≈⟨ assoc _ _ _ ⍮ ∙≫ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
a ◂ deep (μ⟨𝓢⟩ , D₂ b c     & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) = deep (D₃ a b c   & m & rs μ≈⟨ assoc _ _ _ ⍮ ∙≫ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
a ◂ deep (μ⟨𝓢⟩ , D₃ b c d   & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) = deep (D₄ a b c d & m & rs μ≈⟨ assoc _ _ _ ⍮ ∙≫ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
a ◂ deep (μ⟨𝓢⟩ , D₄ b c d e & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) with ⟅ N₃ c d e ⟆ ◂ m
... | m′ ↦ c∙d∙e∙m≈μ⟨m′⟩ = deep (D₂ a b & m′ & rs μ≈⟨ assoc _ _ _ ⍮ ∙≫ lemma ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
  where
  lemma =
    begin
      μ b ∙ (μ m′ ∙ μ rs)
    ≈˘⟨ ∙≫ (sym (assoc _ _ _) ⍮ ≪∙ sym c∙d∙e∙m≈μ⟨m′⟩) ⟩
      μ b ∙ ((μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ rs))
    ≈˘⟨ assoc _ _ _ ⟩
      μ b ∙ (μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ rs)
    ≈⟨ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩
      μ⟨𝓢⟩
    ∎

_▸_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → (x : Σ) → ⟨ Tree Σ ⟩μ⁻¹[ μ xs ∙ μ x ]
empty ▸ a = single a ↦ ℳ ↯
single a ▸ b = deep ⟅ D₁ a & empty & D₁ b ⟆ ↦ ℳ ↯
deep (μ⟨𝓢⟩ , ls & m & D₁ a       ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ b = deep (ls & m & D₂ a b     μ≈⟨ ℳ ↯ ⍮′ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ b) ↦ refl
deep (μ⟨𝓢⟩ , ls & m & D₂ a b     ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ c = deep (ls & m & D₃ a b c   μ≈⟨ ℳ ↯ ⍮′ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ c) ↦ refl
deep (μ⟨𝓢⟩ , ls & m & D₃ a b c   ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ d = deep (ls & m & D₄ a b c d μ≈⟨ ℳ ↯ ⍮′ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ d) ↦ refl
deep (μ⟨𝓢⟩ , ls & m & D₄ a b c d ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ e with m ▸ ⟅ N₃ a b c ⟆
... | m′ ↦ m∙a∙b∙c≈μ⟨m′⟩ = deep ( ls & m′ & D₂ d e μ≈⟨ lemma ⟩ μ⟨𝓢⟩ ∙ μ e ) ↦ refl
  where
  lemma =
    begin
      μ (ls & m′ & D₂ d e)
    ≡⟨⟩
      μ ls ∙ (μ m′ ∙ (μ d ∙ μ e))
    ≈˘⟨ ∙≫ ≪∙ sym m∙a∙b∙c≈μ⟨m′⟩ ⟩
      μ ls ∙ (μ m ∙ (μ a ∙ (μ b ∙ μ c)) ∙ (μ d ∙ μ e))
    ≈⟨ ℳ ↯ ⟩
      μ ls ∙ (μ m ∙ (μ a ∙ (μ b ∙ (μ c ∙ μ d)))) ∙ μ e
    ≈⟨ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩
      μ⟨𝓢⟩ ∙ μ e
    ∎
