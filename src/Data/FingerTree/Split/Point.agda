{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Unary
open import Relation.Binary hiding (Decidable)

module Data.FingerTree.Split.Point
  {r m}
  (ℳ : Monoid r m)
  {s}
  {ℙ : Pred (Monoid.Carrier ℳ) s}
  (ℙ-resp : ℙ Respects (Monoid._≈_ ℳ))
  (ℙ? : Decidable ℙ)
  where

open import Relation.Nullary using (¬_; yes; no; Dec)
open import Level using (_⊔_)
open import Data.Product
open import Function
open import Data.List as List using (List; _∷_; [])

open import Data.FingerTree.Measures ℳ
open import Data.FingerTree.Reasoning ℳ

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; False; toWitnessFalse)

open σ ⦃ ... ⦄

open Monoid ℳ renaming (Carrier to 𝓡)

open import Data.FingerTree.Relation.Binary.Reasoning.FasterInference.Setoid setoid

infixr 5 _∣_
record _∣_ (left focus : 𝓡) : Set s where
  constructor ¬[_]ℙ[_]
  field
    ¬ℙ : ¬ ℙ left
    !ℙ : ℙ (left ∙ focus)
open _∣_ public

_∣?_ : ∀ x y → Dec (x ∣ y)
x ∣? y with ℙ? x
... | yes p = no λ c → ¬ℙ c p
... | no ¬p with ℙ? (x ∙ y)
... | no ¬c = no (¬c ∘ !ℙ)
... | yes p = yes ¬[ ¬p ]ℙ[ p ]

infixl 2 _≈◄⟅_⟆ _≈▻⟅_⟆ _≈⟅_∣_⟆ _◄_ _▻_
_◄_ : ∀ {l f₁ f₂} → l ∣ f₁ ∙ f₂ → ¬ ℙ (l ∙ f₁) → (l ∙ f₁) ∣ f₂
!ℙ (p ◄ ¬ℙf) = ℙ-resp (sym (assoc _ _ _)) (!ℙ p)
¬ℙ (p ◄ ¬ℙf) = ¬ℙf

_▻_ : ∀ {l f₁ f₂} → l ∣ f₁ ∙ f₂ → ℙ (l ∙ f₁) → l ∣ f₁
!ℙ (p ▻ ℙf) = ℙf
¬ℙ (p ▻ ℙf) = ¬ℙ p

_≈◄⟅_⟆ : ∀ {x y z} → x ∣ y → x ≈ z → z ∣ y
¬ℙ (x⟅y⟆ ≈◄⟅ x≈z ⟆) = ¬ℙ x⟅y⟆ ∘ ℙ-resp (sym x≈z)
!ℙ (x⟅y⟆ ≈◄⟅ x≈z ⟆) = ℙ-resp (≪∙ x≈z) (!ℙ x⟅y⟆)

_≈▻⟅_⟆ : ∀ {x y z} → x ∣ y → y ≈ z → x ∣ z
¬ℙ (x⟅y⟆ ≈▻⟅ y≈z ⟆) = ¬ℙ x⟅y⟆
!ℙ (x⟅y⟆ ≈▻⟅ y≈z ⟆) = ℙ-resp (∙≫ y≈z) (!ℙ x⟅y⟆)

_≈⟅_∣_⟆ : ∀ {x₁ y₁ x₂ y₂} → x₁ ∣ y₁ → x₁ ≈ x₂ → y₁ ≈ y₂ → x₂ ∣ y₂
¬ℙ (x⟅y⟆ ≈⟅ x≈ ∣ y≈ ⟆) = ¬ℙ x⟅y⟆ ∘ ℙ-resp (sym x≈)
!ℙ (x⟅y⟆ ≈⟅ x≈ ∣ y≈ ⟆) = ℙ-resp (∙-cong x≈ y≈) (!ℙ x⟅y⟆)

¬∄ℙ : ∀ {i} → ¬ (i ∣ ε)
¬∄ℙ i⟅ε⟆ = ¬ℙ i⟅ε⟆ (ℙ-resp (identityʳ _) (!ℙ i⟅ε⟆))
