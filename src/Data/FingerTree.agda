{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree
  {c ℓ}
  (meas : Monoid c ℓ)
  where

open Monoid meas renaming (Carrier to 𝓡)

open import Data.Product
open import Function
open import Level using (_⊔_)

record σ {a} (Σ : Set a) : Set (a ⊔ c) where field μ : Σ → 𝓡
open σ ⦃ ... ⦄ public
{-# DISPLAY σ.μ _ x = μ x #-}

record ⟪_⟫ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (a ⊔ c ⊔ ℓ) where
  constructor μ⟨_⟩≈_⟨_⟩
  field
    𝓢    : Σ
    μ⟨𝓢⟩ : 𝓡
    ⟪≈⟫  : μ 𝓢 ≈ μ⟨𝓢⟩
open ⟪_⟫

⟅_⟆ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Σ → ⟪ Σ ⟫
⟅ x ⟆ = μ⟨ x ⟩≈ μ x ⟨ refl ⟩

instance
  σ-⟪⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → σ ⟪ Σ ⟫
  μ ⦃ σ-⟪⟫ ⦄ = μ⟨𝓢⟩

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
  record Deep {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (c ⊔ a ⊔ ℓ) where
    constructor _&_&_
    inductive
    field
      lbuff : Digit Σ
      tree  : Tree ⟪ Node Σ ⟫
      rbuff : Digit Σ

  data Tree {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (c ⊔ a ⊔ ℓ) where
    empty : Tree Σ
    single : Σ → Tree Σ
    deep : ⟪ Deep Σ ⟫  → Tree Σ

  μ-deep : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Deep Σ → 𝓡
  μ-deep (l & x & r) = μ l ∙ (μ-tree x ∙ μ r)

  μ-tree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Tree Σ → 𝓡
  μ-tree empty = ε
  μ-tree (single x) = μ x
  μ-tree (deep xs) = xs .μ⟨𝓢⟩

  instance
    σ-Deep : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Deep Σ)
    μ ⦃ σ-Deep ⦄ = μ-deep

  instance
    σ-Tree : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Tree Σ)
    μ ⦃ σ-Tree ⦄ = μ-tree
open Deep

{-# DISPLAY μ-tree _ x = μ x #-}
{-# DISPLAY μ-deep _ x = μ x #-}

open import Relation.Binary.Reasoning.Setoid setoid

infixr 2 ∙≫_ ≪∙_
∙≫_ : ∀ {x y z} → x ≈ y → z ∙ x ≈ z ∙ y
∙≫_ = ∙-cong refl

≪∙_ : ∀ {x y z} → x ≈ y → x ∙ z ≈ y ∙ z
≪∙_ = flip ∙-cong refl

_◂_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (x : Σ) → (xs : Tree Σ) → Σ[ ys ∈ Tree Σ ] (μ x ∙ μ xs ≈ μ ys)
a ◂ empty = single a , identityʳ _
a ◂ single b = deep ⟅ D₁ a & empty & D₁ b ⟆ , (∙≫ sym (identityˡ _))
a ◂ deep μ⟨ D₁ b & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ = deep μ⟨ D₂ a b & m & xs ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ ⟪≈⟫ ⟩ , refl
a ◂ deep μ⟨ D₂ b c & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ = deep μ⟨ D₃ a b c & m & xs ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ ⟪≈⟫ ⟩ , refl
a ◂ deep μ⟨ D₃ b c d & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ = deep μ⟨ D₄ a b c d & m & xs ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ ⟪≈⟫ ⟩ , refl
a ◂ deep μ⟨ D₄ b c d e & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ with ⟅ N₃ c d e ⟆ ◂ m
... | m′ , ⟪≈⟫′ = deep μ⟨ D₂ a b & m′ & xs  ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ lemma ⟩ , refl
  where
  lemma =
    begin
      μ b ∙ (μ m′ ∙ μ xs)
    ≈˘⟨ ∙≫ (sym (assoc _ _ _) ⟨ trans ⟩ ≪∙ ⟪≈⟫′) ⟩
      μ b ∙ ((μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ xs))
    ≈˘⟨ assoc _ _ _ ⟩
      μ b ∙ (μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ xs)
    ≈⟨ ⟪≈⟫ ⟩
      μ⟨𝓢⟩
    ∎
