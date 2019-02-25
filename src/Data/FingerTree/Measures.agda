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
{-# INLINE pure #-}

infixl 2 _≈[_] ≈-rev
_≈[_] : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ {x : 𝓡} → μ⟨ Σ ⟩≈ x → ∀ {y} → x ≈ y → μ⟨ Σ ⟩≈ y
𝓢 (xs ≈[ y≈z ]) = 𝓢 xs
𝒻 (xs ≈[ y≈z ]) = trans (𝒻 xs) y≈z
{-# INLINE _≈[_] #-}

≈-rev : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ {x : 𝓡} → ∀ {y} → x ≈ y → μ⟨ Σ ⟩≈ x → μ⟨ Σ ⟩≈ y
𝓢 (≈-rev y≈z xs) = 𝓢 xs
𝒻 (≈-rev y≈z xs) = trans (𝒻 xs) y≈z
{-# INLINE ≈-rev #-}

syntax ≈-rev y≈z x↦y = x↦y ≈[ y≈z ]′

infixr 2 ≈-right
≈-right : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ {x : 𝓡} → μ⟨ Σ ⟩≈ x → ∀ {y} → x ≈ y → μ⟨ Σ ⟩≈ y
≈-right (x ⇑[ x≈y ]) y≈z = x ⇑[ trans x≈y y≈z ]

syntax ≈-right x x≈ = [ x≈ ]≈ x

infixr 1 _↤_
-- A memoized application of μ
record ⟪_⟫ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (a ⊔ r ⊔ m) where
  constructor _↤_
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

infixl 2 arg-syntax
record Arg {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (𝓂 : 𝓡) (f : 𝓡 → 𝓡) : Set (m ⊔ r ⊔ a) where
  constructor arg-syntax
  field
    ⟨f⟩ : Congruent₁ f
    arg : μ⟨ Σ ⟩≈ 𝓂
open Arg

syntax arg-syntax (λ sz → e₁) xs = xs [ e₁ ⟿ sz ]

infixl 1 _>>=_
_>>=_ : ∀ {a b} {Σ₁ : Set a} {Σ₂ : Set b} ⦃ _ : σ Σ₁ ⦄ ⦃ _ : σ Σ₂ ⦄ {𝓂 f}
      → Arg Σ₁ 𝓂 f
      → ((x : Σ₁) → ⦃ x≈ : μ x ≈ 𝓂 ⦄ → μ⟨ Σ₂ ⟩≈ f (μ x))
      → μ⟨ Σ₂ ⟩≈ f 𝓂
xs >>= k = k (𝓢 (arg xs)) ⦃ 𝒻 (arg xs) ⦄ ≈[ ⟨f⟩ xs (𝒻 (arg xs)) ]
{-# INLINE _>>=_ #-}

_≈?_ : ∀ x y → ⦃ x≈y : x ≈ y ⦄ → x ≈ y
_≈?_ _ _ ⦃ x≈y ⦄ = x≈y
