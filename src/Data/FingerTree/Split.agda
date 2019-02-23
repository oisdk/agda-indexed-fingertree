{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Unary
open import Relation.Binary hiding (Decidable)

module Data.FingerTree.Split
  {r m}
  (ℳ : Monoid r m)
  {s}
  {ℙ : Pred (Monoid.Carrier ℳ) s}
  (ℙ-resp : ℙ Respects (Monoid._≈_ ℳ))
  (ℙ? : Decidable ℙ)
  (mono-ℙ : ∀ x y → ℙ x → ℙ (Monoid._∙_ ℳ x y))
  where

open import Relation.Nullary using (¬_; yes; no)
open import Level using (_⊔_)
open import Data.Product
open import Function
open import Data.List as List using (List; _∷_; [])

open import Data.FingerTree.Measures ℳ
open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Reasoning ℳ

open Monoid ℳ renaming (Carrier to 𝓡)

mono-¬ℙ : ∀ x y → ¬ ℙ (x ∙ y) → ¬ ℙ x
mono-¬ℙ x y ¬ℙ⟨x∙y⟩ ℙ⟨x⟩ = ¬ℙ⟨x∙y⟩ (mono-ℙ x y ℙ⟨x⟩)

∃¬ℙ⇒¬ℙ⟨ε⟩ : ∃[ x ] (¬ ℙ x) → ¬ ℙ ε
∃¬ℙ⇒¬ℙ⟨ε⟩ (x , ¬ℙ⟨x⟩) ℙ⟨ε⟩ = ¬ℙ⟨x⟩ (ℙ-resp (identityˡ _) (mono-ℙ ε x ℙ⟨ε⟩))

_⇒_⟨_⟩ : ∀ {x} → ℙ x → ∀ y → x ≈ y → ℙ y
ℙ⟨x⟩ ⇒ y ⟨ x≈y ⟩ = ℙ-resp x≈y ℙ⟨x⟩

_⇏_⟨_⟩ : ∀ {x} → ¬ ℙ x → ∀ y → x ≈ y → ¬ ℙ y
ℙ⟨x⟩ ⇏ y ⟨ x≈y ⟩ = ℙ⟨x⟩ ∘ ℙ-resp (sym x≈y)

infixr 5 _∷⟨_⟩∷_[_,_]
record Split {a b} (i : 𝓡) (Σ : Set a) (A : Set b) ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ : Set (r ⊔ a ⊔ s ⊔ b) where
  constructor _∷⟨_⟩∷_[_,_]
  field
    before : Σ
    cursor : A
    ?ℙ : Σ
    ¬ℙ : ¬ ℙ (i ∙ μ before)
    !ℙ : ℙ (i ∙ (μ before ∙ μ cursor))

instance
  σ-Split : ∀  {i : 𝓡} {a b} {Σ : Set a} {A : Set b} ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ → σ (Split i Σ A)
  μ ⦃ σ-Split {i} ⦄ (l ∷⟨ x ⟩∷ r [ _ , _ ]) =  i ∙ (μ l ∙ (μ x ∙ μ r))

open import Data.Empty using (⊥-elim)

module _ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ where
  splitList : ∀ i → ¬ ℙ i → (xs : List Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (List Σ) Σ ⟩μ⁻¹[ i ∙ μ xs ]
  splitList i ¬ℙ⟨i⟩ [] ℙ⟨i∙xs⟩ = ⊥-elim ( ¬ℙ⟨i⟩ (ℙ-resp (identityʳ _) ℙ⟨i∙xs⟩))
  splitList i ¬ℙ⟨i⟩ (x ∷ xs) ℙ⟨i∙xs⟩ with ℙ? (i ∙ μ x)
  ... | yes p = [] ∷⟨ x ⟩∷ xs [ ¬ℙ⟨i⟩ ∘ ℙ-resp (identityʳ _) , p ⇒ i ∙ (ε ∙ μ x) ⟨ ℳ ↯ ⟩ ] ↦ ℳ ↯
  ... | no ¬p with splitList (i ∙ μ x) ¬p xs (ℙ-resp (sym (assoc _ _ _)) ℙ⟨i∙xs⟩)
  ... | ys ∷⟨ y ⟩∷ zs [ ¬ℙ⟨ys⟩ , ℙ⟨y⟩ ] ↦ i∙x∙ys∙y∙zs≈i∙x∙xs = (x ∷ ys) ∷⟨ y ⟩∷ zs [ ¬ℙ⟨ys⟩ ∘ ℙ-resp (sym (assoc _ _ _)) ,  ℙ⟨y⟩ ⇒ i ∙ (μ x ∙ μ ys ∙ μ y) ⟨ ℳ ↯ ⟩ ] ↦ lemma
    where
    lemma =
      begin
        i ∙ (μ x ∙ μ ys ∙ (μ y ∙ μ zs))
      ≈⟨ ℳ ↯ ⟩
        i ∙ μ x ∙ (μ ys ∙ (μ y ∙ μ zs))
      ≈⟨ i∙x∙ys∙y∙zs≈i∙x∙xs ⟩
        i ∙ μ x ∙ μ xs
      ≈⟨ assoc _ _ _ ⟩
        i ∙ (μ x ∙ μ xs)
      ∎

  nodeToList : (xs : Node Σ) → ⟨ List Σ ⟩μ⁻¹[ μ xs ]
  nodeToList (N₂ x₁ x₂) = x₁ ∷ x₂ ∷ [] ↦ ℳ ↯
  nodeToList (N₃ x₁ x₂ x₃) = x₁ ∷ x₂ ∷ x₃ ∷ [] ↦ ℳ ↯

  digitToList : (xs : Digit Σ) → ⟨ List Σ ⟩μ⁻¹[ μ xs ]
  digitToList (D₁ x₁) = x₁ ∷ [] ↦ ℳ ↯
  digitToList (D₂ x₁ x₂) = x₁ ∷ x₂ ∷ [] ↦ ℳ ↯
  digitToList (D₃ x₁ x₂ x₃) = x₁ ∷ x₂ ∷ x₃ ∷ [] ↦ ℳ ↯
  digitToList (D₄ x₁ x₂ x₃ x₄) = x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [] ↦ ℳ ↯

  splitNode : ∀ i → ¬ ℙ i → (xs : Node Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (List Σ) Σ ⟩μ⁻¹[ i ∙ μ xs ]
  splitNode i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ with nodeToList xs
  splitNode i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ with splitList i ¬ℙ⟨i⟩ ys (ℙ-resp (∙≫ sym μ⟨ys⟩≈μ⟨xs⟩) ℙ⟨i∙xs⟩)
  splitNode i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ | zs ↦ i∙μ⟨zs⟩≈i∙μ⟨ys⟩ = zs ↦ (i∙μ⟨zs⟩≈i∙μ⟨ys⟩ ⍮ ∙≫ μ⟨ys⟩≈μ⟨xs⟩)


  splitDigit : ∀ i → ¬ ℙ i → (xs : Digit Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (List Σ) Σ ⟩μ⁻¹[ i ∙ μ xs ]
  splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ with digitToList xs
  splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ with splitList i ¬ℙ⟨i⟩ ys (ℙ-resp (∙≫ sym μ⟨ys⟩≈μ⟨xs⟩) ℙ⟨i∙xs⟩)
  splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ | zs ↦ i∙μ⟨zs⟩≈i∙μ⟨ys⟩ = zs ↦ (i∙μ⟨zs⟩≈i∙μ⟨ys⟩ ⍮ ∙≫ μ⟨ys⟩≈μ⟨xs⟩)
