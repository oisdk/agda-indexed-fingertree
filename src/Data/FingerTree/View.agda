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

viewₗ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → μ⟨ Viewₗ Σ (Tree Σ) ⟩≈ (μ xs)
viewₗ empty = nilₗ ⇑
viewₗ (single x) = (x ◃ empty) ⇑[ ℳ ↯ ]
viewₗ (deep (𝓂 ↤ (D₂ a b     & m & rs) ⇑[ 𝓂≈ ])) = a ◃ deep ⟪ D₁ b     & m & rs ⇓⟫ ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
viewₗ (deep (𝓂 ↤ (D₃ a b c   & m & rs) ⇑[ 𝓂≈ ])) = a ◃ deep ⟪ D₂ b c   & m & rs ⇓⟫ ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
viewₗ (deep (𝓂 ↤ (D₄ a b c d & m & rs) ⇑[ 𝓂≈ ])) = a ◃ deep ⟪ D₃ b c d & m & rs ⇓⟫ ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
viewₗ (deep (𝓂 ↤ (D₁ a & m & rs) ⇑[ 𝓂≈ ])) with viewₗ m
... | (μ⟨y⟩ ↤ N₂ y₁ y₂    ⇑[ yp ]) ◃ ys ⇑[ p ] = a ◃ deep (μ m ∙ μ rs ↤ D₂ y₁ y₂    & ys & rs ⇑[ ℳ ↯ ] ≈[ ≪∙ (≪∙ yp ⍮ p) ]′) ⇑[ 𝓂≈ ]
... | (μ⟨y⟩ ↤ N₃ y₁ y₂ y₃ ⇑[ yp ]) ◃ ys ⇑[ p ] = a ◃ deep (μ m ∙ μ rs ↤ D₃ y₁ y₂ y₃ & ys & rs ⇑[ ℳ ↯ ] ≈[ ≪∙ (≪∙ yp ⍮ p) ]′) ⇑[ 𝓂≈ ]
... | nilₗ ⇑[ p ] = (digitToTree rs [ _ ∙> r ⟿ r ] >>= (λ rs′ → (a ◃ rs′) ⇑)) ≈[ ∙≫ sym (identityˡ _) ⍮ (∙≫ ≪∙ p) ⍮ 𝓂≈ ]

infixl 5 _▹_
data Viewᵣ {a b} (A : Set a) (Σ : Set b) : Set (a ⊔ b) where
  nilᵣ : Viewᵣ A Σ
  _▹_ : Σ → A → Viewᵣ A Σ

instance
  σ-Viewᵣ : ∀ {a b} {A : Set a} {Σ : Set b} ⦃ _ : σ A ⦄ ⦃ _ : σ Σ ⦄ → σ (Viewᵣ A Σ)
  μ ⦃ σ-Viewᵣ ⦄ nilᵣ = ε
  μ ⦃ σ-Viewᵣ ⦄ (xs ▹ x) = μ xs ∙ μ x

viewᵣ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → μ⟨ Viewᵣ Σ (Tree Σ) ⟩≈ (μ xs)
viewᵣ empty = nilᵣ ⇑
viewᵣ (single x) = empty ▹ x ⇑[ ℳ ↯ ]
viewᵣ (deep (𝓂 ↤ (ls & m & D₂ a b    ) ⇑[ 𝓂≈ ])) = (deep ⟪ ls & m & D₁ a     ⇓⟫ ▹ b) ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
viewᵣ (deep (𝓂 ↤ (ls & m & D₃ a b c  ) ⇑[ 𝓂≈ ])) = (deep ⟪ ls & m & D₂ a b   ⇓⟫ ▹ c) ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
viewᵣ (deep (𝓂 ↤ (ls & m & D₄ a b c d) ⇑[ 𝓂≈ ])) = (deep ⟪ ls & m & D₃ a b c ⇓⟫ ▹ d) ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
viewᵣ (deep (𝓂 ↤ (ls & m & D₁ a) ⇑[ 𝓂≈ ])) with viewᵣ m
... | ys ▹ (μ⟨y⟩ ↤ N₂ y₁ y₂    ⇑[ yp ]) ⇑[ p ] = deep (μ ls ∙ μ m ↤ ls & ys & D₂ y₁ y₂    ⇑[ ℳ ↯ ] ≈[ ∙≫ (∙≫ yp ⍮ p) ]′) ▹ a ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
... | ys ▹ (μ⟨y⟩ ↤ N₃ y₁ y₂ y₃ ⇑[ yp ]) ⇑[ p ] = deep (μ ls ∙ μ m ↤ ls & ys & D₃ y₁ y₂ y₃ ⇑[ ℳ ↯ ] ≈[ ∙≫ (∙≫ yp ⍮ p) ]′) ▹ a ⇑[ ℳ ↯ ] ≈[ 𝓂≈ ]′
... | nilᵣ ⇑[ p ] = (digitToTree ls [ l <∙ _ ⟿ l ] >>= (λ ls′ → (ls′ ▹ a) ⇑)) ≈[ ℳ ↯ ↣ μ ls ∙ (ε ∙ μ a) ] ≈[ ∙≫ ≪∙ p ⍮ 𝓂≈ ]′

deepₗ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (l : List Σ) → (m : Tree ⟪ Node Σ ⟫) → (r : Digit Σ) → μ⟨ Tree Σ ⟩≈ (μ l ∙ (μ m ∙ μ r))
deepₗ [] m r with viewₗ m
deepₗ [] m r | nilₗ ⇑[ n≈ ] = digitToTree r ≈[ ℳ ↯ ↣ ε ∙ (ε ∙ μ r) ] ≈[ ∙≫ ≪∙ n≈ ]′
deepₗ [] m r | ((μ⟨y⟩ ↤ N₂ y₁ y₂    ⇑[ yp ]) ◃ ys) ⇑[ ys≈ ] = deep (μ m ∙ μ r ↤ D₂ y₁ y₂    & ys & r ⇑[ ≪∙ yp ⍮ sym (assoc _ _ _) ⍮ ≪∙ ys≈ ]) ⇑[ ℳ ↯ ]
deepₗ [] m r | ((μ⟨y⟩ ↤ N₃ y₁ y₂ y₃ ⇑[ yp ]) ◃ ys) ⇑[ ys≈ ] = deep (μ m ∙ μ r ↤ D₃ y₁ y₂ y₃ & ys & r ⇑[ ≪∙ yp ⍮ sym (assoc _ _ _) ⍮ ≪∙ ys≈ ]) ⇑[ ℳ ↯ ]
deepₗ (l ∷ ls) m r = go l ls m r
  where
  go : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (l : Σ) → (ls : List Σ) → (m : Tree ⟪ Node Σ ⟫) → (r : Digit Σ) → μ⟨ Tree Σ ⟩≈ (μ l ∙ μ ls ∙ (μ m ∙ μ r))
  go l [] m r = deep ⟪ D₁ l & m & r ⇓⟫ ⇑[ ℳ ↯ ]
  go l₁ (l₂ ∷ ls) m r = (go l₂ ls m r [ _ ∙> ls′ ⟿ ls′ ] >>= (l₁ ◂_)) ≈[ ℳ ↯ ]

deepᵣ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (l : Digit Σ) → (m : Tree ⟪ Node Σ ⟫) → (r : List Σ) → μ⟨ Tree Σ ⟩≈ (μ l ∙ (μ m ∙ μ r))
deepᵣ l m [] with viewᵣ m
deepᵣ l m [] | nilᵣ ⇑[ p ] = digitToTree l ≈[ sym (identityʳ _) ⍮ ∙≫ (p ⍮ sym (identityʳ _)) ]
deepᵣ l m [] | (ys ▹ (μ⟨y⟩ ↤ N₂ y₁ y₂    ⇑[ μ⟨y⟩≈ ])) ⇑[ p ] = deep (μ l ∙ μ m ↤ l & ys & D₂ y₁ y₂    ⇑[ ∙≫ (∙≫ μ⟨y⟩≈ ⍮ p) ]) ⇑[ ℳ ↯ ]
deepᵣ l m [] | (ys ▹ (μ⟨y⟩ ↤ N₃ y₁ y₂ y₃ ⇑[ μ⟨y⟩≈ ])) ⇑[ p ] = deep (μ l ∙ μ m ↤ l & ys & D₃ y₁ y₂ y₃ ⇑[ ∙≫ (∙≫ μ⟨y⟩≈ ⍮ p) ]) ⇑[ ℳ ↯ ]
deepᵣ l m (r ∷ rs) = go  (deep ⟪ l & m & D₁ r ⇓⟫ ⇑) rs ≈[ ℳ ↯ ]
  where
  go : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → ∀ {xs} → μ⟨ Tree Σ ⟩≈ xs → (rs : List Σ) → μ⟨ Tree Σ ⟩≈ (xs ∙ μ rs)
  go xs [] = xs ≈[ sym (identityʳ _) ]
  go xs (r ∷ rs) = go (xs [ sz <∙ _ ⟿ sz ] >>= (_▸ r)) rs ≈[ ℳ ↯ ]
