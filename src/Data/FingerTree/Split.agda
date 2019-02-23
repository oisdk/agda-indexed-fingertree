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

open import Relation.Nullary using (¬_; yes; no; Dec)
open import Level using (_⊔_)
open import Data.Product
open import Function
open import Data.List as List using (List; _∷_; [])

open import Data.FingerTree.Measures ℳ
open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Reasoning ℳ
open import Data.FingerTree.View ℳ using (deepₗ; deepᵣ)
open import Data.FingerTree.Cons ℳ using (listToTree)

open σ ⦃ ... ⦄

{-# DISPLAY σ.μ _ = μ #-}

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

data ⟪ℙ?_⟫ (x : 𝓡) : Set (s ⊔ r ⊔ m) where
  ⟪_⟨_⟩_?⟫ : ∀ y → x ≈ y → Dec (ℙ x) → ⟪ℙ? x ⟫

⟪ℙ?_⇓⟫ : ∀ x → ⟪ℙ? x ⟫
⟪ℙ? x ⇓⟫ = ⟪ x ⟨ refl ⟩ ℙ? x ?⟫

module _ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ where
  splitList : ∀ i → ¬ ℙ i → (xs : List Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (List Σ) Σ ⟩μ⁻¹ (i ∙ μ xs)
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

  nodeToList : (xs : Node Σ) → ⟨ List Σ ⟩μ⁻¹ (μ xs)
  nodeToList (N₂ x₁ x₂) = x₁ ∷ x₂ ∷ [] ↦ ℳ ↯
  nodeToList (N₃ x₁ x₂ x₃) = x₁ ∷ x₂ ∷ x₃ ∷ [] ↦ ℳ ↯

  digitToList : (xs : Digit Σ) → ⟨ List Σ ⟩μ⁻¹ (μ xs)
  digitToList (D₁ x₁) = x₁ ∷ [] ↦ ℳ ↯
  digitToList (D₂ x₁ x₂) = x₁ ∷ x₂ ∷ [] ↦ ℳ ↯
  digitToList (D₃ x₁ x₂ x₃) = x₁ ∷ x₂ ∷ x₃ ∷ [] ↦ ℳ ↯
  digitToList (D₄ x₁ x₂ x₃ x₄) = x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [] ↦ ℳ ↯

  splitNode : ∀ i → ¬ ℙ i → (xs : Node Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (List Σ) Σ ⟩μ⁻¹ (i ∙ μ xs)
  splitNode i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ with nodeToList xs
  splitNode i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ with splitList i ¬ℙ⟨i⟩ ys (ℙ-resp (∙≫ sym μ⟨ys⟩≈μ⟨xs⟩) ℙ⟨i∙xs⟩)
  splitNode i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ | zs ↦ i∙μ⟨zs⟩≈i∙μ⟨ys⟩ = zs ↦ (i∙μ⟨zs⟩≈i∙μ⟨ys⟩ ⍮ ∙≫ μ⟨ys⟩≈μ⟨xs⟩)

  splitDigit : ∀ i → ¬ ℙ i → (xs : Digit Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (List Σ) Σ ⟩μ⁻¹ (i ∙ μ xs)
  splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ with digitToList xs
  splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ with splitList i ¬ℙ⟨i⟩ ys (ℙ-resp (∙≫ sym μ⟨ys⟩≈μ⟨xs⟩) ℙ⟨i∙xs⟩)
  splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ | zs ↦ i∙μ⟨zs⟩≈i∙μ⟨ys⟩ = zs ↦ (i∙μ⟨zs⟩≈i∙μ⟨ys⟩ ⍮ ∙≫ μ⟨ys⟩≈μ⟨xs⟩)


  splitTree-l : ∀ i → ¬ ℙ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫)  → (rs : Digit Σ) → ℙ (i ∙ μ ls) → ⟨ Split i (Tree Σ) Σ ⟩μ⁻¹ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
  splitTree-l i ¬ℙ⟨i⟩ ls m rs ℙ⟨i∙ls⟩ with splitDigit i ¬ℙ⟨i⟩ ls ℙ⟨i∙ls⟩
  ... | lsₗ ∷⟨ mₗ ⟩∷ rsₗ [ p₁ , p₂ ] ↦ p₃ with listToTree lsₗ | deepₗ rsₗ m rs
  ... | ls′ ↦ ls′≈ | rs′ ↦ rs′≈ = ls′ ∷⟨ mₗ ⟩∷ rs′ [ p₁ ∘′ ℙ-resp (∙≫ ls′≈) , ℙ-resp (∙≫ ≪∙ sym ls′≈) p₂ ] ↦ lemma
    where
    lemma =
      begin
        i ∙ (μ ls′ ∙ (μ mₗ ∙ μ rs′))
      ≈⟨ ∙≫ ≪∙ ls′≈ ⟩
        i ∙ (μ lsₗ ∙ (μ mₗ ∙ μ rs′))
      ≈⟨ ∙≫ ∙≫ ∙≫ rs′≈  ⟩
        i ∙ (μ lsₗ ∙ (μ mₗ ∙ (μ rsₗ ∙ (μ m ∙ μ rs))))
      ≈⟨ ℳ ↯ ⟩
        i ∙ (μ lsₗ ∙ (μ mₗ ∙ μ rsₗ)) ∙ (μ m ∙ μ rs)
      ≈⟨ ≪∙ p₃ ⟩
        i ∙ μ ls ∙ (μ m ∙ μ rs)
      ≈⟨ ℳ ↯ ⟩
        i ∙ (μ ls ∙ (μ m ∙ μ rs))
      ∎

  splitTree-r : ∀ i → ¬ ℙ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫)  → (rs : Digit Σ) → ℙ (i ∙ (μ ls ∙ (μ m ∙ μ rs))) → ∀ i′ → i′ ≈ i ∙(μ ls ∙ μ m) → ¬ ℙ (i ∙ (μ ls ∙ μ m)) → ⟨ Split i (Tree Σ) Σ ⟩μ⁻¹ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
  splitTree-r i ¬ℙ⟨i⟩ ls m rs ℙ⟨xs⟩ i′ ⟪i′⟫ ¬ℙ⟨i∙ls∙m⟩ with splitDigit i′ (¬ℙ⟨i∙ls∙m⟩ ∘′ ℙ-resp ⟪i′⟫) rs (ℙ-resp (ℳ ↯ ⍮′ ≪∙ sym ⟪i′⟫) ℙ⟨xs⟩)
  splitTree-r i ¬ℙ⟨i⟩ ls m rs ℙ⟨xs⟩ i′ ⟪i′⟫ ¬ℙ⟨i∙ls∙m⟩ | lsᵣ ∷⟨ mᵣ ⟩∷ rsᵣ [ p₁ , p₂ ] ↦ p₃ with deepᵣ ls m lsᵣ | listToTree rsᵣ
  splitTree-r i ¬ℙ⟨i⟩ ls m rs ℙ⟨xs⟩ i′ ⟪i′⟫ ¬ℙ⟨i∙ls∙m⟩ | lsᵣ ∷⟨ mᵣ ⟩∷ rsᵣ [ p₁ , p₂ ] ↦ p₃ | ls′ ↦ ls′≈ | rs′ ↦ rs′≈ = ls′ ∷⟨ mᵣ ⟩∷ rs′ [ p₁ ∘′ ℙ-resp lemma₁ , ℙ-resp lemma₂ p₂ ] ↦ lemma₃
    where
    lemma₁ =
      begin
        i ∙ μ ls′
      ≈⟨ ∙≫ ls′≈ ⟩
        i ∙ (μ ls ∙ (μ m ∙ μ lsᵣ))
      ≈⟨ ℳ ↯ ⟩
        (i ∙ (μ ls ∙ μ m)) ∙ μ lsᵣ
      ≈˘⟨ ≪∙ ⟪i′⟫ ⟩
        i′ ∙ μ lsᵣ
      ∎
    lemma₂ =
      begin
        i′ ∙ (μ lsᵣ ∙ μ mᵣ)
      ≈⟨ ≪∙ ⟪i′⟫ ⟩
        (i ∙ (μ ls ∙ μ m)) ∙ (μ lsᵣ ∙ μ mᵣ)
      ≈⟨ ℳ ↯ ⟩
        i ∙ ((μ ls ∙ (μ m ∙ μ lsᵣ)) ∙ μ mᵣ)
      ≈˘⟨ ∙≫ ≪∙ ls′≈ ⟩
        i ∙ (μ ls′ ∙ μ mᵣ)
      ∎
    lemma₃ =
      begin
        i ∙ (μ ls′ ∙ (μ mᵣ ∙ μ rs′))
      ≈⟨ ∙≫ ∙-cong ls′≈ (∙≫ rs′≈) ⟩
        i ∙ ((μ ls ∙ (μ m ∙ μ lsᵣ)) ∙ (μ mᵣ ∙ μ rsᵣ))
      ≈⟨ ℳ ↯ ⟩
        (i ∙ (μ ls ∙ μ m)) ∙ (μ lsᵣ ∙ (μ mᵣ ∙ μ rsᵣ))
      ≈˘⟨ ≪∙ ⟪i′⟫ ⟩
        i′ ∙ (μ lsᵣ ∙ (μ mᵣ ∙ μ rsᵣ))
      ≈⟨ p₃ ⟩
        i′ ∙ μ rs
      ≈⟨ ≪∙ ⟪i′⟫ ⟩
        (i ∙ (μ ls ∙ μ m)) ∙ μ rs
      ≈⟨ ℳ ↯ ⟩
        i ∙ (μ ls ∙ (μ m ∙ μ rs))
      ∎



splitTree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → ∀ i → ¬ ℙ i → (xs : Tree Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (Tree Σ) Σ ⟩μ⁻¹ (i ∙ μ xs)
splitTree i ¬ℙ⟨i⟩ empty ℙ⟨i∙xs⟩ = ⊥-elim (¬ℙ⟨i⟩ (ℙ-resp (identityʳ _) ℙ⟨i∙xs⟩))
splitTree i ¬ℙ⟨i⟩ (single x) ℙ⟨i∙xs⟩ = empty ∷⟨ x ⟩∷ empty [ ¬ℙ⟨i⟩ ∘ ℙ-resp (identityʳ _) , ℙ⟨i∙xs⟩ ⇒ i ∙ (ε ∙ μ x) ⟨ ℳ ↯ ⟩ ] ↦ ℳ ↯
splitTree i ¬ℙ⟨i⟩ (deep (μ⟨xs⟩ , ls & m & rs ↦ μ⟨xs⟩≈)) ℙ⟨i∙xs⟩ with ⟪ℙ? (i ∙ μ ls) ⇓⟫
... | ⟪ i′ ⟨ ⟪i′⟫ ⟩ yes p ?⟫ = splitTree-l i ¬ℙ⟨i⟩ ls m rs p ≈[ ∙≫ μ⟨xs⟩≈ ]
... | ⟪ i′ ⟨ ⟪i′⟫ ⟩ no ¬p ?⟫ with ⟪ℙ? (i′ ∙ μ m) ⇓⟫
... | ⟪ i″ ⟨ ⟪i″⟫ ⟩ no ¬p′ ?⟫ = splitTree-r i ¬ℙ⟨i⟩ ls m rs (ℙ-resp (∙≫ sym (μ⟨xs⟩≈)) ℙ⟨i∙xs⟩) i″ (sym ⟪i″⟫ ⍮ (≪∙ sym ⟪i′⟫ ⍮ assoc _ _ _)) (¬p′ ∘′ ℙ-resp (sym (assoc _ _ _) ⍮ ≪∙ ⟪i′⟫)) ≈[ ∙≫ μ⟨xs⟩≈ ]
... | ⟪ i″ ⟨ ⟪i″⟫ ⟩ yes p′ ?⟫ with splitTree i′ (¬p ∘′ ℙ-resp (sym ⟪i′⟫)) m p′
... | lsₘ ∷⟨ μ⟨mₘ⟩ , mₘ ↦ mₘ≈ ⟩∷ rsₘ [ p₁ , p₂ ] ↦ p₃ with splitNode (i′ ∙ μ lsₘ) p₁ mₘ (ℙ-resp (sym (assoc _ _ _) ⍮ ∙≫ sym mₘ≈) p₂)
... | l ∷⟨ x ⟩∷ r [ p₄ , p₅ ] ↦ p₆ with deepᵣ ls lsₘ l | deepₗ r rsₘ rs
... | ls′ ↦ ls′≈ | rs′ ↦ rs′≈ = ls′ ∷⟨ x ⟩∷ rs′ [ p₄ ∘′ ℙ-resp lemma₁ , ℙ-resp lemma₂ p₅ ] ↦ (lemma₃ ⍮ ∙≫ μ⟨xs⟩≈)
  where
  lemma₁ =
    begin
      i ∙ μ ls′
    ≈⟨ ∙≫ ls′≈ ⟩
      i ∙ (μ ls ∙ (μ lsₘ ∙ μ l))
    ≈˘⟨ assoc _ _ _ ⟩
      (i ∙ μ ls) ∙ (μ lsₘ ∙ μ l)
    ≈⟨ ≪∙ ⟪i′⟫ ⟩
      i′ ∙ (μ lsₘ ∙ μ l)
    ≈˘⟨ assoc _ _ _ ⟩
      i′ ∙ μ lsₘ ∙ μ l
    ∎
  lemma₂ =
    begin
      i′ ∙ μ lsₘ ∙ (μ l ∙ μ x)
    ≈˘⟨ ≪∙ ≪∙ ⟪i′⟫ ⟩
      (i ∙ μ ls) ∙ μ lsₘ ∙ (μ l ∙ μ x)
    ≈⟨ ℳ ↯ ⟩
      i ∙ ((μ ls ∙ (μ lsₘ ∙ μ l)) ∙ μ x)
    ≈˘⟨ ∙≫ ≪∙ ls′≈ ⟩
      i ∙ (μ ls′ ∙ μ x)
    ∎
  lemma₃ =
    begin
      i ∙ (μ ls′ ∙ (μ x ∙ μ rs′))
    ≈⟨ ∙≫ ∙-cong ls′≈ (∙≫ rs′≈) ⟩
      i ∙ ((μ ls ∙ (μ lsₘ ∙ μ l)) ∙ (μ x ∙ (μ r ∙ (μ rsₘ ∙ μ rs))))
    ≈⟨ ℳ ↯ ⟩
      (i ∙ μ ls) ∙ (μ lsₘ ∙ μ l) ∙ (μ x ∙ (μ r ∙ (μ rsₘ ∙ μ rs)))
    ≈⟨ ≪∙ ≪∙ ⟪i′⟫ ⟩
      i′ ∙ (μ lsₘ ∙ μ l) ∙ (μ x ∙ (μ r ∙ (μ rsₘ ∙ μ rs)))
    ≈⟨ ℳ ↯ ⟩
      (i′ ∙ μ lsₘ ∙ (μ l ∙ (μ x ∙ μ r))) ∙ (μ rsₘ ∙ μ rs)
    ≈⟨ ≪∙ p₆ ⟩
      (i′ ∙ μ lsₘ ∙ μ mₘ) ∙ (μ rsₘ ∙ μ rs)
    ≈⟨ ≪∙ ∙≫ mₘ≈ ⟩
      (i′ ∙ μ lsₘ ∙ μ⟨mₘ⟩) ∙ (μ rsₘ ∙ μ rs)
    ≈⟨ ℳ ↯ ⟩
      (i′ ∙ (μ lsₘ ∙ (μ⟨mₘ⟩ ∙ μ rsₘ))) ∙ μ rs
    ≈⟨ ≪∙ p₃ ⟩
      i′ ∙ μ m ∙ μ rs
    ≈⟨ assoc _ _ _ ⟩
      i′ ∙ (μ m ∙ μ rs)
    ≈⟨ (≪∙ sym ⟪i′⟫ ⍮ assoc _ _ _) ⟩
      i ∙ (μ ls ∙ (μ m ∙ μ rs))
    ∎
