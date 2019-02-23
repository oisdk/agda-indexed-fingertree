{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree.View
  {r m}
  (ℳ : Monoid r m)
  where

open import Level using (_⊔_)
open import Data.Product
open import Function

open import Data.List as List using (List; _∷_; [])

open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Reasoning ℳ
open import Data.FingerTree.Measures ℳ
open import Data.FingerTree.Cons ℳ
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

viewₗ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → ⟨ Viewₗ Σ (Tree Σ) ⟩μ⁻¹ (μ xs)
viewₗ empty = nilₗ ↦ refl
viewₗ (single x) = x ◃ empty ↦ identityʳ _
viewₗ (deep (μ⟨xs⟩ , (D₂ a b     & m & rs) ↦ μ⟨xs⟩≈)) = a ◃ deep (_ , D₁ b     & m & rs ↦ refl) ↦ (ℳ ↯ ⍮′ μ⟨xs⟩≈)
viewₗ (deep (μ⟨xs⟩ , (D₃ a b c   & m & rs) ↦ μ⟨xs⟩≈)) = a ◃ deep (_ , D₂ b c   & m & rs ↦ refl) ↦ (μ a ∙ μ (D₂ b c   & m & rs) ↣⟨ ℳ ↯ ⟩↣ μ (D₃ a b c   & m & rs) ⍮′ μ⟨xs⟩≈)
viewₗ (deep (μ⟨xs⟩ , (D₄ a b c d & m & rs) ↦ μ⟨xs⟩≈)) = a ◃ deep (_ , D₃ b c d & m & rs ↦ refl) ↦ (μ a ∙ μ (D₃ b c d & m & rs) ↣⟨ ℳ ↯ ⟩↣ μ (D₄ a b c d & m & rs) ⍮′ μ⟨xs⟩≈)
viewₗ (deep (μ⟨xs⟩ , (D₁ a & m & rs) ↦ μ⟨xs⟩≈)) with viewₗ m
... | (μ⟨y⟩ , N₂ y₁ y₂ ↦ yp) ◃ ys ↦ p = a ◃ deep (μ m ∙ μ rs , D₂ y₁ y₂ & ys & rs ↦ (μ (D₂ y₁ y₂ & ys & rs) ↣⟨ ℳ ↯ ⟩↣ (μ y₁ ∙ μ y₂ ∙ μ ys ∙ μ rs) ⍮′ ≪∙ (≪∙ yp ⍮ p))) ↦ μ⟨xs⟩≈
... | (μ⟨y⟩ , N₃ y₁ y₂ y₃ ↦ yp) ◃ ys ↦ p = a ◃ deep (μ m ∙ μ rs , D₃ y₁ y₂ y₃ & ys & rs ↦ (μ (D₃ y₁ y₂ y₃ & ys & rs) ↣⟨ ℳ ↯ ⟩↣ (μ y₁ ∙ (μ y₂ ∙ μ y₃) ∙ μ ys ∙ μ rs) ⍮ ≪∙ (≪∙ yp ⍮ p))) ↦ μ⟨xs⟩≈
... | nilₗ ↦ p with digitToTree rs
... | rs′ ↦ p′ = a ◃ rs′ ↦ (∙≫ (sym (identityˡ _) ⍮ ∙-cong p p′) ⍮ μ⟨xs⟩≈)

infixl 5 _▹_
data Viewᵣ {a b} (A : Set a) (Σ : Set b) : Set (a ⊔ b) where
  nilᵣ : Viewᵣ A Σ
  _▹_ : Σ → A → Viewᵣ A Σ

instance
  σ-Viewᵣ : ∀ {a b} {A : Set a} {Σ : Set b} ⦃ _ : σ A ⦄ ⦃ _ : σ Σ ⦄ → σ (Viewᵣ A Σ)
  μ ⦃ σ-Viewᵣ ⦄ nilᵣ = ε
  μ ⦃ σ-Viewᵣ ⦄ (xs ▹ x) = μ xs ∙ μ x

viewᵣ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → ⟨ Viewᵣ Σ (Tree Σ) ⟩μ⁻¹ (μ xs)
viewᵣ empty = nilᵣ ↦ refl
viewᵣ (single x) = empty ▹ x ↦ identityˡ _
viewᵣ (deep (μ⟨xs⟩ , (ls & m & D₂ a b    ) ↦ μ⟨xs⟩≈)) = (deep (_ , ls & m & D₁ a     ↦ refl) ▹ b) ↦ (μ (ls & m & D₁ a) ∙ μ b ↢ ℳ ↯ ⍮′ μ⟨xs⟩≈)
viewᵣ (deep (μ⟨xs⟩ , (ls & m & D₃ a b c  ) ↦ μ⟨xs⟩≈)) = (deep (_ , ls & m & D₂ a b   ↦ refl) ▹ c) ↦ (μ (ls & m & D₂ a b) ∙ μ c ↢ ℳ ↯ ⍮′ μ⟨xs⟩≈)
viewᵣ (deep (μ⟨xs⟩ , (ls & m & D₄ a b c d) ↦ μ⟨xs⟩≈)) = (deep (_ , ls & m & D₃ a b c ↦ refl) ▹ d) ↦ (μ (ls & m & D₃ a b c) ∙ μ d ↢ ℳ ↯ ⍮′ μ⟨xs⟩≈)
viewᵣ (deep (μ⟨xs⟩ , (ls & m & D₁ a) ↦ μ⟨xs⟩≈)) with viewᵣ m
... | ys ▹ (μ⟨y⟩ , N₂ y₁ y₂ ↦ yp) ↦ p = deep (μ ls ∙ μ m , ls & ys & D₂ y₁ y₂ ↦ (ℳ ↯ ⍮ ∙≫ (∙≫ yp ⍮ p))) ▹ a ↦ (assoc _ _ _ ⍮ μ⟨xs⟩≈)
... | ys ▹ (μ⟨y⟩ , N₃ y₁ y₂ y₃ ↦ yp) ↦ p = deep (μ ls ∙ μ m , ls & ys & D₃ y₁ y₂ y₃ ↦ (ℳ ↯ ⍮ ∙≫ (∙≫ yp ⍮ p))) ▹ a ↦ (assoc _ _ _ ⍮ μ⟨xs⟩≈)
... | nilᵣ ↦ p with digitToTree ls
... | ls′ ↦ p′ = ls′ ▹ a ↦ (∙-cong p′ (sym (identityˡ _) ⍮ ≪∙ p) ⍮ μ⟨xs⟩≈)

deepₗ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (l : List Σ) → (m : Tree ⟪ Node Σ ⟫) → (r : Digit Σ) → ⟨ Tree Σ ⟩μ⁻¹ (μ l ∙ (μ m ∙ μ r))
deepₗ [] m r with viewₗ m
deepₗ [] m r | nilₗ ↦ p = digitToTree r ≈[ sym (identityˡ _) ⍮ ≪∙ p ⍮ sym (identityˡ _) ]
deepₗ [] m r | (μ⟨y⟩ , y ↦ μ⟨y⟩≈) ◃ ys ↦ p with nodeToDigit y
deepₗ [] m r | (μ⟨y⟩ , y ↦ μ⟨y⟩≈) ◃ ys ↦ p | (y′ ↦ μ⟨y′⟩≈) = deep (μ m ∙ μ r , y′ & ys & r ↦ (sym (assoc _ _ _) ⍮ ≪∙ (≪∙ (μ⟨y′⟩≈ ⍮ μ⟨y⟩≈) ⍮ p))) ↦ sym (identityˡ _)
deepₗ (l ∷ ls) m r = go l ls m r
  where
  go : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (l : Σ) → (ls : List Σ) → (m : Tree ⟪ Node Σ ⟫) → (r : Digit Σ) → ⟨ Tree Σ ⟩μ⁻¹ (μ l ∙ μ ls ∙ (μ m ∙ μ r))
  go l [] m r = deep (_ , D₁ l & m & r ↦ refl) ↦ ℳ ↯
  go l₁ (l₂ ∷ ls) m r = l₁ ◂′ go l₂ ls m r ≈[ ℳ ↯ ]

deepᵣ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (l : Digit Σ) → (m : Tree ⟪ Node Σ ⟫) → (r : List Σ) → ⟨ Tree Σ ⟩μ⁻¹ (μ l ∙ (μ m ∙ μ r))
deepᵣ l m [] with viewᵣ m
deepᵣ l m [] | nilᵣ ↦ p = digitToTree l ≈[ sym (identityʳ _) ⍮ ∙≫ (p ⍮ sym (identityʳ _)) ]
deepᵣ l m [] | ys ▹ (μ⟨y⟩ , y ↦ μ⟨y⟩≈) ↦ p with nodeToDigit y
deepᵣ l m [] | ys ▹ (μ⟨y⟩ , y ↦ μ⟨y⟩≈) ↦ p | (y′ ↦ μ⟨y′⟩≈) = deep (μ l ∙ μ m , l & ys & y′ ↦ (∙≫ (∙≫ (μ⟨y′⟩≈ ⍮ μ⟨y⟩≈) ⍮ p))) ↦ ℳ ↯
deepᵣ l m (r ∷ rs) = go μ[ deep (_ , l & m & D₁ r ↦ refl) ] rs ≈[ ℳ ↯ ]
  where
  go : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → ∀ {xs} → ⟨ Tree Σ ⟩μ⁻¹ xs → (rs : List Σ) → ⟨ Tree Σ ⟩μ⁻¹ (xs ∙ μ rs)
  go xs [] = xs ≈[ sym (identityʳ _) ]
  go xs (r ∷ rs) = go (xs ▸′ r) rs ≈[ ℳ ↯ ]
