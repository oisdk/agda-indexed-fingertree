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

infixl 2 _⇑[_]
record μ⟨_⟩≈_ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (𝓂 : 𝓡) : Set (a ⊔ r ⊔ m) where
  constructor _⇑[_]
  field
    𝓢 : Σ
    𝒻 : μ 𝓢 ≈ 𝓂
open μ⟨_⟩≈_ public

pure : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ (𝓢 : Σ) → μ⟨ Σ ⟩≈ μ 𝓢
𝓢 (pure x) = x
𝒻 (pure x) = refl

infixl 2 _≈[_]
_≈[_] : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ {x : 𝓡} → μ⟨ Σ ⟩≈ x → ∀ {y} → x ≈ y → μ⟨ Σ ⟩≈ y
x ⇑[ x≈y ] ≈[ y≈z ] = x ⇑[ trans x≈y y≈z ]

-- A memoized application of μ
record ⟪_⟫ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (a ⊔ r ⊔ m) where
  field
    𝔐 : 𝓡
    𝓕 : μ⟨ Σ ⟩≈ 𝔐
open ⟪_⟫ public

-- Construct the memoized version
⟪_⇓⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Σ → ⟪ Σ ⟫
𝔐 ⟪ x ⇓⟫ = μ x
𝓕 ⟪ x ⇓⟫ = pure x

instance
  σ-⟪⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → σ ⟪ Σ ⟫
  μ ⦃ σ-⟪⟫ ⦄ = 𝔐

open import Algebra.FunctionProperties _≈_

record Arg {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (f : 𝓡 → 𝓡) (𝓂 : 𝓡) : Set (r ⊔ m ⊔ a) where
  constructor _⇓[_]
  field
    arg   : μ⟨ Σ ⟩≈ 𝓂
    focus : Congruent₁ f

  infixl 1 _>>=_
  _>>=_ : ∀ {b} {Σ′ : Set b} ⦃ _ : σ Σ′ ⦄
        → ((x : Σ) → μ⟨ Σ′ ⟩≈ f (μ x))
        → μ⟨ Σ′ ⟩≈ f 𝓂
  _>>=_ k = k (𝓢 arg) ≈[ focus (𝒻 arg) ]
open Arg public
open import Function

example : ∀ {a b} {Σ₁ : Set a} {Σ₂ : Set b} ⦃ _ : σ Σ₁ ⦄ ⦃ _ : σ Σ₂ ⦄ {𝓂₁ 𝓂₂ : 𝓡}
        → μ⟨ Σ₁ ⟩≈ 𝓂₁
        → μ⟨ Σ₂ ⟩≈ 𝓂₂
        → μ⟨ Σ₁ ⟩≈ 𝓂₁
example xs ys = do
  x ← xs ⇓[ id ]
  y ← ys ⇓[ const refl ]
  pure x


record MemoArg {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (f : 𝓡 → 𝓡) (𝓂 : 𝓡) : Set (r ⊔ m ⊔ a) where
  constructor _⟪⇓⟫[_]
  field
    ⟪arg⟫ : μ⟨ ⟪ Σ ⟫ ⟩≈ 𝓂
    ⟪focus⟫ : Congruent₁ f

  infixl 1 _⟪>>=⟫_
  _⟪>>=⟫_ : ∀ {b} {Σ′ : Set b} ⦃ _ : σ Σ′ ⦄
        → ((x : Σ) → μ⟨ Σ′ ⟩≈ f (μ x))
        → μ⟨ ⟪ Σ′ ⟫ ⟩≈ f 𝓂
  ((_⟪>>=⟫_ k) .𝓢) .𝔐 = f (⟪arg⟫ .𝓢 .𝔐)
  ((_⟪>>=⟫_ k) .𝓢) .𝓕 = k (⟪arg⟫ .𝓢 .𝓕 .𝓢) ≈[ ⟪focus⟫ (⟪arg⟫ .𝓢 .𝓕 .𝒻) ]
  (_⟪>>=⟫_ k) .𝒻 = ⟪focus⟫ (⟪arg⟫ .𝒻)
open MemoArg public
