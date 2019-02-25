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
  (mono-ℙ : ∀ {x y} → ℙ x → ℙ (Monoid._∙_ ℳ x y))
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

import Relation.Binary.Construct.FromPred setoid ℙ as PredRel
open import Relation.Binary.Reasoning.FasterInference.Preorder (PredRel.preorder ℙ-resp)

infixl 5 _⟅_⟆
record _⟅_⟆ (left focus : 𝓡) : Set s where
  constructor _∣_
  field
    ¬ℙ : ¬ ℙ left
    !ℙ : ℙ (left ∙ focus)
open _⟅_⟆

infixl 2 _≈◄⟅_⟆ _≈▻⟅_⟆ _≈⟅_∣_⟆ _◄_ _▻_
_◄_ : ∀ {l f₁ f₂} → l ⟅ f₁ ∙ f₂ ⟆ → ¬ ℙ (l ∙ f₁) → l ∙ f₁ ⟅ f₂ ⟆
!ℙ (p ◄ ¬ℙf) = ℙ-resp (sym (assoc _ _ _)) (!ℙ p)
¬ℙ (p ◄ ¬ℙf) = ¬ℙf

_▻_ : ∀ {l f₁ f₂} → l ⟅ f₁ ∙ f₂ ⟆ → ℙ (l ∙ f₁) → l ⟅ f₁ ⟆
!ℙ (p ▻ ℙf) = ℙf
¬ℙ (p ▻ ℙf) = ¬ℙ p

_≈◄⟅_⟆ : ∀ {x y z} → x ⟅ y ⟆ → x ≈ z → z ⟅ y ⟆
¬ℙ (x⟅y⟆ ≈◄⟅ x≈z ⟆) = ¬ℙ x⟅y⟆ ∘ ℙ-resp (sym x≈z)
!ℙ (x⟅y⟆ ≈◄⟅ x≈z ⟆) = ℙ-resp (≪∙ x≈z) (!ℙ x⟅y⟆)

_≈▻⟅_⟆ : ∀ {x y z} → x ⟅ y ⟆ → y ≈ z → x ⟅ z ⟆
(¬ℙ ∣ !ℙ) ≈▻⟅ p ⟆ = ¬ℙ ∣ ℙ-resp (∙≫ p) !ℙ

_≈⟅_∣_⟆ : ∀ {x₁ y₁ x₂ y₂} → x₁ ⟅ y₁ ⟆ → x₁ ≈ x₂ → y₁ ≈ y₂ → x₂ ⟅ y₂ ⟆
¬ℙ (x⟅y⟆ ≈⟅ x≈ ∣ y≈ ⟆) = ¬ℙ x⟅y⟆ ∘ ℙ-resp (sym x≈)
!ℙ (x⟅y⟆ ≈⟅ x≈ ∣ y≈ ⟆) = ℙ-resp (∙-cong x≈ y≈) (!ℙ x⟅y⟆)

¬∄ℙ : ∀ {i} → ¬ i ⟅ ε ⟆
¬∄ℙ (¬ℙ ∣ !ℙ) = ¬ℙ (ℙ-resp (identityʳ _) !ℙ)

record Split (i : 𝓡) {a b} (Σ : Set a) (A : Set b) ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ : Set (a ⊔ b ⊔ s) where
  constructor _∷⟨_⟩∷_[_]
  field
    left  : Σ
    focus : A
    right : Σ
    proof : i ∙ μ left ⟅ μ focus ⟆
open Split


instance
  σ-Split : ∀  {a b} {Σ : Set a} {A : Set b} ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ {i : 𝓡} → σ (Split i Σ A)
  μ ⦃ σ-Split {i = i} ⦄ (l ∷⟨ x ⟩∷ r [ _ ]) = i ∙ (μ l ∙ (μ x ∙ μ r))

infixl 2 _i≈[_]
_i≈[_] : ∀ {a b} {Σ : Set a} {A : Set b} ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ → ∀ {i xs} → μ⟨ Split i Σ A ⟩≈ (i ∙ xs) → ∀ {j} → i ≈ j → μ⟨ Split j Σ A ⟩≈ (j ∙ xs)
xs ∷⟨ x ⟩∷ ys [ p₁ ] ⇑[ p₂ ] i≈[ i≈ ] = xs ∷⟨ x ⟩∷ ys [ p₁ ≈◄⟅ ≪∙ i≈ ⟆ ] ⇑[ ≪∙ sym i≈ ⍮ p₂ ⍮ ≪∙ i≈ ]

open import Data.Empty using (⊥-elim)

infixl 2 _≈ℙ_[_]
record ⟪ℙ⟫ (x : 𝓡) : Set (s ⊔ r ⊔ m) where
  constructor _≈ℙ_[_]
  field
    result : Dec (ℙ x)
    stored : 𝓡
    equiv  : stored ≈ x
open ⟪ℙ⟫

⟪ℙ?⟫ : ∀ x → ⟪ℙ⟫ x
result (⟪ℙ?⟫ x) = ℙ? x
stored (⟪ℙ?⟫ x) = x
equiv  (⟪ℙ?⟫ x) = refl

module _ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ where
  splitList : (i : 𝓡) → (xs : List Σ) → i ⟅ μ xs ⟆ → μ⟨ Split i (List Σ) Σ ⟩≈ (i ∙ μ xs)
  splitList i [] s = ⊥-elim (¬∄ℙ s)
  splitList i (x ∷ xs) s with ⟪ℙ?⟫ (i ∙ μ x)
  ... | yes p ≈ℙ i∙x [ i∙x≈ ] = [] ∷⟨ x ⟩∷ xs [ s ▻ p ≈◄⟅ ℳ ↯ ⟆  ] ⇑[ ℳ ↯ ]
  ... | no ¬p ≈ℙ i∙x [ i∙x≈ ] with splitList i∙x xs (s ◄ ¬p ≈◄⟅ sym i∙x≈ ⟆) i≈[ i∙x≈ ]
  ... | ys ∷⟨ y ⟩∷ zs [ s′ ] ⇑[ ys≈ ] = (x ∷ ys) ∷⟨ y ⟩∷ zs [ s′ ≈◄⟅ ℳ ↯ ⟆ ] ⇑[ ℳ ↯ ] ≈[ ys≈ ]′ ≈[ ℳ ↯ ]

  nodeToList : (xs : Node Σ) → μ⟨ List Σ ⟩≈ (μ xs)
  nodeToList (N₂ x₁ x₂) = x₁ ∷ x₂ ∷ [] ⇑[ ℳ ↯ ]
  nodeToList (N₃ x₁ x₂ x₃) = x₁ ∷ x₂ ∷ x₃ ∷ [] ⇑[ ℳ ↯ ]

  digitToList : (xs : Digit Σ) → μ⟨ List Σ ⟩≈ (μ xs)
  digitToList (D₁ x₁) = x₁ ∷ [] ⇑[ ℳ ↯ ]
  digitToList (D₂ x₁ x₂) = x₁ ∷ x₂ ∷ [] ⇑[ ℳ ↯ ]
  digitToList (D₃ x₁ x₂ x₃) = x₁ ∷ x₂ ∷ x₃ ∷ [] ⇑[ ℳ ↯ ]
  digitToList (D₄ x₁ x₂ x₃ x₄) = x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [] ⇑[ ℳ ↯ ]

  splitNode : ∀ i → (xs : Node Σ) → i ⟅ μ xs ⟆ → μ⟨ Split i (List Σ) Σ ⟩≈ (i ∙ μ xs)
  splitNode i xs s = do
    ys ← nodeToList xs [ _ ∙> sz ⟿ sz ]
    splitList i ys (s ≈▻⟅ sym (_ ≈? _) ⟆)


  splitDigit : ∀ i → (xs : Digit Σ) → i ⟅ μ xs ⟆ → μ⟨ Split i (List Σ) Σ ⟩≈ (i ∙ μ xs)
  splitDigit i xs s = digitToList xs [ _ ∙> sz ⟿ sz ] >>= λ ys → splitList i ys (s ≈▻⟅ sym (_ ≈? _) ⟆)

  splitTree-l : ∀ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫) → (rs : Digit Σ) → i ⟅ μ ls ⟆ → μ⟨ Split i (Tree Σ) Σ ⟩≈ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
  splitTree-l i ls m rs s with splitDigit i ls s
  splitTree-l i ls m rs s | lsₗ ∷⟨ mₗ ⟩∷ rsₗ [ p ] ⇑[ l≈ ] = [ ( ℳ ↯ ⍮′ ≪∙ l≈ ⍮ assoc _ _ _) ]≈ do
    ls′ ← listToTree lsₗ [ i ∙> (sz <∙ _) ⟿ sz ]
    rs′ ← deepₗ rsₗ m rs [ i ∙> (_ ∙> (_ ∙> sz)) ⟿ sz ]
    pure (ls′ ∷⟨ mₗ ⟩∷ rs′ [ p ≈◄⟅ ∙≫ sym (_ ≈? _)  ⟆ ])

  splitTree-r : ∀ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫) → (rs : Digit Σ) → ∀ i∙ls∙m → i∙ls∙m ≈  (i ∙ μ ls ∙ μ m) → (i ∙ μ ls ∙ μ m) ⟅ μ rs ⟆ → μ⟨ Split i (Tree Σ) Σ ⟩≈ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
  splitTree-r i ls m rs i′ i′≈ s with splitDigit i′ rs (s ≈◄⟅ sym i′≈ ⟆)
  splitTree-r i ls m rs i′ i′≈ s | lsᵣ ∷⟨ mᵣ ⟩∷ rsᵣ [ p ] ⇑[ r≈ ] = [ lemma ]≈ do
      ls′ ← deepᵣ ls m lsᵣ [ i ∙> (sz <∙ _) ⟿ sz ]
      rs′ ← listToTree rsᵣ [ i ∙> (_ ∙> (_ ∙> sz)) ⟿ sz ]
      pure (ls′ ∷⟨ mᵣ ⟩∷ rs′ [ p ≈◄⟅ ≪∙ i′≈ ⍮ ℳ ↯ ⍮′ ∙≫ sym (μ ls′ ≈? (μ ls ∙ (μ m ∙ μ lsᵣ))) ⟆ ])
    where
    lemma = begin-equality
      i ∙ (μ ls ∙ (μ m ∙ μ lsᵣ) ∙ (μ mᵣ ∙ μ rsᵣ))
        ≈⟨ ℳ ↯ ⟩
      i ∙ μ ls ∙ μ m ∙ (μ lsᵣ ∙ (μ mᵣ ∙ μ rsᵣ))
        ≈⟨ ≪∙ sym i′≈ ⟩
      i′ ∙ (μ lsᵣ ∙ (μ mᵣ ∙ μ rsᵣ))
        ≈⟨ r≈ ⟩
      i′ ∙ μ rs
        ≈⟨ ≪∙ i′≈ ⟩
      i ∙ μ ls ∙ μ m ∙ μ rs
        ≈⟨ ℳ ↯ ⟩
      i ∙ (μ ls ∙ (μ m ∙ μ rs)) ∎

splitTree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄
          → ∀ i
          → (xs : Tree Σ)
          → i ⟅ μ xs ⟆
          → μ⟨ Split i (Tree Σ) Σ ⟩≈ (i ∙ μ xs)
splitTree i empty s = ⊥-elim (¬∄ℙ s)
splitTree i (single x) s = empty ∷⟨ x ⟩∷ empty [ s ≈◄⟅ ℳ ↯ ⟆ ] ⇑[ ℳ ↯ ]
splitTree i (deep (𝓂 ↤ ls & m & rs ⇑[ 𝓂≈ ])) s with ⟪ℙ?⟫ (i ∙ μ ls)
... | yes p₁ ≈ℙ i∙ls [ i∙ls≈ ] = splitTree-l i ls m rs (¬ℙ s ∣ p₁) ≈[ ∙≫ 𝓂≈ ]
... | no ¬p₁ ≈ℙ i∙ls [ i∙ls≈ ] with ⟪ℙ?⟫ (i∙ls ∙ μ m)
... | no ¬p₂ ≈ℙ i∙ls∙m [ i∙ls∙m≈ ] = splitTree-r i ls m rs i∙ls∙m (i∙ls∙m≈ ⍮ ≪∙ i∙ls≈) (s ≈▻⟅ sym 𝓂≈ ⟆ ◄ ¬p₁ ≈◄⟅ sym i∙ls≈ ⟆ ◄ ¬p₂ ≈◄⟅ ≪∙ i∙ls≈ ⟆) ≈[ ∙≫ 𝓂≈ ]
... | yes p₂ ≈ℙ i∙ls∙m [ i∙ls∙m≈ ] with splitTree i∙ls m (s ≈▻⟅ sym 𝓂≈ ⟆ ◄ ¬p₁ ≈◄⟅ sym i∙ls≈ ⟆ ▻ p₂)
... | lsₘ ∷⟨ μmₘ ↤ mₘ ⇑[ mₘ≈ ] ⟩∷ rsₘ [ sₘ ] ⇑[ m≈ ] with splitNode (i∙ls ∙ μ lsₘ) mₘ (sₘ ≈▻⟅ sym mₘ≈ ⟆)
... | lsₗ ∷⟨ mₗ ⟩∷ rsₗ [ sₗ ] ⇑[ l≈ ] = [ lemma ]≈ do
      ll ← deepᵣ ls lsₘ lsₗ [ i ∙> (sz <∙ _) ⟿ sz ]
      rr ← deepₗ rsₗ rsₘ rs [ i ∙> (_ ∙> (μ mₗ ∙> sz)) ⟿ sz ]
      pure (ll ∷⟨ mₗ ⟩∷ rr [ sₗ ≈◄⟅ ≪∙ ≪∙ i∙ls≈ ⍮ ℳ ↯ ⍮′ ∙≫ sym (_ ≈? _) ⟆ ])
  where
  lemma = begin-equality
    i ∙ (μ ls ∙ (μ lsₘ ∙ μ lsₗ) ∙ (μ mₗ ∙ (μ rsₗ ∙ (μ rsₘ ∙ μ rs))))
      ≈⟨ ℳ ↯ ⟩
    i ∙ μ ls ∙ μ lsₘ ∙ (μ lsₗ ∙ (μ mₗ ∙ μ rsₗ)) ∙ (μ rsₘ ∙ μ rs)
      ≈⟨ ≪∙ ≪∙ ≪∙ sym i∙ls≈ ⍮ l≈ <∙ (μ rsₘ ∙ μ rs) ⟩
    i∙ls ∙ μ lsₘ ∙ μ mₘ ∙ (μ rsₘ ∙ μ rs)
      ≈⟨ ≪∙ ∙≫ mₘ≈ ⟩
    i∙ls ∙ μ lsₘ ∙ μmₘ ∙ (μ rsₘ ∙ μ rs)
      ≈⟨ ℳ ↯ ⟩
    i∙ls ∙ (μ lsₘ ∙ (μmₘ ∙ μ rsₘ)) ∙ μ rs
      ≈⟨ m≈ <∙ μ rs ⟩
    i∙ls ∙ μ m ∙ μ rs
      ≈⟨ ≪∙ ≪∙ i∙ls≈ ⟩
    i ∙ μ ls ∙ μ m ∙ μ rs
      ≈⟨ ℳ ↯ ⟩
    i ∙ (μ ls ∙ (μ m ∙ μ rs))
      ≈⟨ ∙≫ 𝓂≈ ⟩
    i ∙ 𝓂 ∎

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; False; toWitnessFalse)

split : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄
      → {¬ℙ⟨ε⟩ : False (ℙ? ε)}
      → (xs : Tree Σ)
      → {ℙ⟨xs⟩ : True (ℙ? (μ xs))}
      → μ⟨ Split ε (Tree Σ) Σ ⟩≈ μ xs
split {¬ℙ⟨ε⟩ = ¬ℙ⟨ε⟩} xs {ℙ⟨xs⟩} = splitTree ε xs (toWitnessFalse ¬ℙ⟨ε⟩ ∣ ℙ-resp (sym (identityˡ _)) (toWitness ℙ⟨xs⟩)) ≈[ identityˡ _ ]
