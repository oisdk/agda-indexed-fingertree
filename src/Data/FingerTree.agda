{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree
  {c ℓ}
  (measure : Monoid c ℓ)
  where

open import Data.Product
open import Function
open import Level using (_⊔_)

open Monoid measure

record Measured {a} (A : Set a) : Set (a ⊔ c) where
  field μ : A → Carrier
open Measured ⦃ ... ⦄ public

{-# DISPLAY Measured.μ _ x = μ x #-}

data Digit {a} (A : Set a) : Set a where
  D₁ : A → Digit A
  D₂ : A → A → Digit A
  D₃ : A → A → A → Digit A
  D₄ : A → A → A → A → Digit A

instance
  measuredDigit : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured (Digit A)
  μ ⦃ measuredDigit ⦄ (D₁ x₁) = μ x₁
  μ ⦃ measuredDigit ⦄ (D₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ measuredDigit ⦄ (D₃ x₁ x₂ x₃) = μ x₁ ∙ (μ x₂ ∙ μ x₃)
  μ ⦃ measuredDigit ⦄ (D₄ x₁ x₂ x₃ x₄) = μ x₁ ∙ (μ x₂ ∙ (μ x₃ ∙ μ x₄))

data Node {a} (A : Set a) : Set a where
  N₂ : A → A → Node A
  N₃ : A → A → A → Node A

instance
  measuredNode : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured (Node A)
  μ ⦃ measuredNode ⦄ (N₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ measuredNode ⦄ (N₃ x₁ x₂ x₃) = μ x₁ ∙ (μ x₂ ∙ μ x₃)

data μ⟨_⟩⁻¹[_] {a} (A : Set a) ⦃ _ : Measured A ⦄ (m : Carrier) : Set (a ⊔ ℓ) where
  ⟅_,_⟆ : (x : A) → m ≈ μ x →  μ⟨ A ⟩⁻¹[ m ]

⟪_⟫ : ∀ {a} → (A : Set a) → ⦃ _ : Measured A ⦄ → Set (a ⊔ c ⊔ ℓ)
⟪ A ⟫ = ∃ μ⟨ A ⟩⁻¹[_]

instance
  measuredCached : ∀ {a} {A : Set a} → ⦃ _ : Measured A ⦄ → Measured ⟪ A ⟫
  μ ⦃ measuredCached ⦄ = proj₁

mutual
  record Deep {a} (A : Set a) ⦃ _ : Measured A ⦄ : Set (c ⊔ a ⊔ ℓ) where
    constructor _&_&_
    inductive
    field
      lbuff : Digit A
      tree  : FingerTree ⟪ Node A ⟫
      rbuff : Digit A

  data FingerTree {a} (A : Set a) ⦃ _ : Measured A ⦄ : Set (c ⊔ a ⊔ ℓ) where
    empty : FingerTree A
    single : A → FingerTree A
    deep : ⟪ Deep A ⟫  → FingerTree A

  μ-deep : ∀ {a} {A : Set a} ⦃ _ : Measured A ⦄ → Deep A → Carrier
  μ-deep xs = μ (Deep.lbuff xs) ∙ (μ-tree (Deep.tree xs) ∙ μ (Deep.rbuff xs))

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

{-# DISPLAY μ-tree _ x = μ x #-}
{-# DISPLAY μ-deep _ x = μ x #-}

open import Relation.Binary.Reasoning.Setoid setoid

infixr 2 ∙≫_ ≪∙_
∙≫_ : ∀ {x y z} → x ≈ y → z ∙ x ≈ z ∙ y
∙≫_ = ∙-cong refl

≪∙_ : ∀ {x y z} → x ≈ y → x ∙ z ≈ y ∙ z
≪∙_ = flip ∙-cong refl

_◂_ : ∀ {a} {A : Set a} ⦃ _ : Measured A ⦄ → (x : A) → (xs : FingerTree A) → μ⟨ FingerTree A ⟩⁻¹[ μ x ∙ μ xs ]
a ◂ empty    = ⟅ single a , identityʳ _ ⟆
a ◂ single b = ⟅ deep (μ a ∙ μ b , ⟅  D₁ a & empty & D₁ b , ∙≫ sym (identityˡ _) ⟆) , refl ⟆
a ◂ deep (v , ⟅ D₁ b & m & xs , p ⟆) = ⟅ deep ((μ a ∙ v) , ⟅ D₂ a b & m & xs , ∙≫ p ⟨ trans ⟩ sym (assoc _ _ _) ⟆) , refl ⟆
a ◂ deep (v , ⟅ D₂ b c & m & xs , p ⟆) = ⟅ deep ((μ a ∙ v) , ⟅ D₃ a b c & m & xs , ∙≫ p ⟨ trans ⟩ sym (assoc _ _ _) ⟆) , refl ⟆
a ◂ deep (v , ⟅ D₃ b c d & m & xs , p ⟆) = ⟅ deep ((μ a ∙ v) , ⟅ D₄ a b c d & m & xs , ∙≫ p ⟨ trans ⟩ sym (assoc _ _ _) ⟆) , refl ⟆
a ◂ deep (v , ⟅ D₄ b c d e & m & xs , p ⟆) with (μ c ∙ (μ d ∙ μ e) ,  ⟅ N₃ c d e , refl ⟆) ◂ m
... | ⟅ m′ , p′ ⟆ = ⟅ deep ((μ a ∙ v) , ⟅ D₂ a b & m′ & xs , lemma ⟆) , refl ⟆
  where
  lemma =
    begin
      μ a ∙ v
    ≈⟨ ∙≫ p ⟩
      μ a ∙ ((μ b ∙ (μ c ∙ (μ d ∙ μ e))) ∙ (μ m ∙ μ xs))
    ≈⟨ ∙≫ assoc _ _ _ ⟩
      μ a ∙ (μ b ∙ ((μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ xs)))
    ≈˘⟨ assoc _ _ _ ⟩
      (μ a ∙ μ b) ∙ ((μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ xs))
    ≈⟨ ∙≫ (sym (assoc _ _ _) ⟨ trans ⟩ ≪∙ p′) ⟩
      (μ a ∙ μ b) ∙ (μ m′ ∙ μ xs)
    ≡⟨⟩
      μ (D₂ a b) ∙ (μ m′ ∙ μ xs)
    ≡⟨⟩
      μ (D₂ a b & m′ & xs)
    ∎
