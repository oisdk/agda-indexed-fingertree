{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree.Measures
  {r m}
  (ℳ : Monoid r m)
  where

open import Level using (_⊔_)

open Monoid ℳ renaming (Carrier to 𝓡)
open import Algebra.FunctionProperties _≈_
open import Data.List as List using (List; _∷_; [])
open import Data.Product
open import Data.FingerTree.Reasoning ℳ

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

-- A "fiber" (I think).
--
--   ⟨ Σ ⟩μ⁻¹ x
--
-- Means "The Σ such that μ Σ ≈ x"

infixr 4 _↦_
record ⟨_⟩μ⁻¹ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (𝑌 : 𝓡) : Set (a ⊔ r ⊔ m) where
  constructor _↦_
  field
    𝓢 : Σ
    fib : μ 𝓢 ≈ 𝑌
open ⟨_⟩μ⁻¹ public

μ[_] : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (𝓢 : Σ) → ⟨ Σ ⟩μ⁻¹ (μ 𝓢)
𝓢   μ[ x ] = x
fib μ[ x ] = refl


infixr 2 _≈[_]
_≈[_] : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ {x : 𝓡} → ⟨ Σ ⟩μ⁻¹ x → ∀ {y} → x ≈ y → ⟨ Σ ⟩μ⁻¹ y
((𝓈 ↦ 𝓂) ≈[ x≈y ]) .𝓢 = 𝓈
((𝓈 ↦ x) ≈[ x≈y ]) .fib = trans x x≈y

infixr 4 [_]_
record Arg {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (f : 𝓡 → 𝓡) (𝓂 : 𝓡) : Set (a ⊔ r ⊔ m) where
  constructor [_]_
  field
    cng : Congruent₁ f
    arg : ⟨ Σ ⟩μ⁻¹ 𝓂
open Arg

-- [_]_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → {g : 𝓡 → 𝓡} → (Congruent₁ g) → ∀ {𝓂} → ⟨ Σ ⟩μ⁻¹ 𝓂 → Arg Σ g 𝓂
-- ([ cng ] xs) .arg = xs
-- ([ prf ] xs) .cng = prf

infixl 1 _>>=_
_>>=_ : ∀ {a b} {Σ₁ : Set a} {Σ₂ : Set b} ⦃ _ : σ Σ₁ ⦄ ⦃ _ : σ Σ₂ ⦄
          → {g : 𝓡 → 𝓡}
          → ∀ {𝓂}
          → (xs : Arg Σ₁ g 𝓂)
          → (f : (x : Σ₁) → ⟨ Σ₂ ⟩μ⁻¹ (g (μ x)))
          → ⟨ Σ₂ ⟩μ⁻¹ (g 𝓂)
([ cng ] (x ↦ x≈)) >>= f = f x ≈[ cng x≈ ]

-- A memoized application of μ
⟪_⟫ : ∀ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ → Set (a ⊔ r ⊔ m)
⟪ Σ ⟫ = ∃ ⟨ Σ ⟩μ⁻¹

open import Function


-- Construct the memoized version
⟪_⇓⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Σ → ⟪ Σ ⟫
⟪ x ⇓⟫ = -, μ[ x ]

infixr 2 ⟪⟫-syntax
⟪⟫-syntax : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (𝓢 : Σ) → (𝑌 : 𝓡) → μ 𝓢 ≈ 𝑌 → ⟪ Σ ⟫
⟪⟫-syntax 𝓢 𝑌 fib = 𝑌 , 𝓢 ↦ fib

syntax ⟪⟫-syntax 𝓢 𝑌 fib = 𝓢 μ≈⟨ fib ⟩ 𝑌

instance
  σ-⟪⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → σ ⟪ Σ ⟫
  μ ⦃ σ-⟪⟫ ⦄ = proj₁

infixl 1 _⟪>>=⟫_
_⟪>>=⟫_ : ∀ {a b} {Σ₁ : Set a} {Σ₂ : Set b} ⦃ _ : σ Σ₁ ⦄ ⦃ _ : σ Σ₂ ⦄
        → {g : 𝓡 → 𝓡}
        → ∀ {𝓂}
        → (xs : Arg ⟪ Σ₁ ⟫ g 𝓂)
        → (f : (x : Σ₁) → ⟨ Σ₂ ⟩μ⁻¹ (g (μ x)))
        → ⟨ ⟪ Σ₂ ⟫ ⟩μ⁻¹ (g 𝓂)
_⟪>>=⟫_ {g = g} ([ cng ] ((c , x ↦ c≈μ⟨x⟩) ↦ x≈)) f = (g c , (f x ≈[ cng c≈μ⟨x⟩ ])) ↦ cng x≈

