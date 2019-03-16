{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Unary
open import Relation.Binary hiding (Decidable)

module Data.FingerTree.Split.Structures
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
open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Reasoning ℳ
open import Data.FingerTree.View ℳ using (deepₗ; deepᵣ)
open import Data.FingerTree.Cons ℳ using (listToTree)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; False; toWitnessFalse)

open σ ⦃ ... ⦄

open Monoid ℳ renaming (Carrier to 𝓡)

open import Data.FingerTree.Relation.Binary.Reasoning.FasterInference.Setoid setoid

open import Data.FingerTree.Split.Point ℳ ℙ-resp ℙ?
open import Data.FingerTree.Split.StoredPredicate ℳ ℙ-resp ℙ?
open import Data.FingerTree.Split.Intermediate ℳ ℙ-resp ℙ?

open import Data.Empty.Irrelevant using (⊥-elim)

module _ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ where
  splitList : (i : 𝓡) → (xs : List Σ) → .(i ∣ μ xs) → μ⟨ Split′ i (List Σ) Σ ⟩≈ (i ∙ μ xs)
  splitList i [] s = ⊥-elim (¬∄ℙ s)
  splitList i (x ∷ xs) s with ⟪ℙ?⟫ (i ∙ μ x)
  ... | yes p ≈ℙ i∙x [ i∙x≈ ] = [] ∷⟨ x ⟩∷ xs [ s ▻ p ≈◄⟅ ℳ ↯ ⟆  ] ⇑[ ℳ ↯ ]
  ... | no ¬p ≈ℙ i∙x [ i∙x≈ ] with splitList i∙x xs (s ◄ ¬p ≈◄⟅ sym i∙x≈ ⟆) i≈[ i∙x≈ ]
  ... | ys ∷⟨ y ⟩∷ zs [ s′ ] ⇑[ ys≈ ] = (x ∷ ys) ∷⟨ y ⟩∷ zs [ s′ ≈◄⟅ ℳ ↯ ⟆ ] ⇑[ ℳ ↯ ] ≈[ ys≈ ]′ ≈[ ℳ ↯ ]

  splitNode : ∀ i → (xs : Node Σ) → .(i ∣ μ xs) → μ⟨ Split′ i (List Σ) Σ ⟩≈ (i ∙ μ xs)
  splitNode i xs s = do
    ys ← nodeToList xs [ _ ∙> sz ⟿ sz ]
    splitList i ys (s ≈▻⟅ sym (_ ≈? _) ⟆)

  splitDigit : ∀ i → (xs : Digit Σ) → .(i ∣ μ xs) → μ⟨ Split′ i (List Σ) Σ ⟩≈ (i ∙ μ xs)
  splitDigit i xs s = digitToList xs [ _ ∙> sz ⟿ sz ] >>= λ ys → splitList i ys (s ≈▻⟅ sym (_ ≈? _) ⟆)

  splitTree-l : ∀ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫) → (rs : Digit Σ) → .(i ∣ μ ls) → μ⟨ Split′ i (Tree Σ) Σ ⟩≈ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
  splitTree-l i ls m rs s with splitDigit i ls s
  splitTree-l i ls m rs s | lsₗ ∷⟨ mₗ ⟩∷ rsₗ [ p ] ⇑[ l≈ ] = [ ( ℳ ↯ ⍮′ ≪∙ l≈ ⍮ assoc _ _ _) ]≈ do
    ls′ ← listToTree lsₗ [ i ∙> (sz <∙ _) ⟿ sz ]
    rs′ ← deepₗ rsₗ m rs [ i ∙> (_ ∙> (_ ∙> sz)) ⟿ sz ]
    ls′ ∷⟨ mₗ ⟩∷ rs′ [ p ≈◄⟅ ∙≫ sym (μ ls′ ≈? μ lsₗ)  ⟆ ] ⇑

  splitTree-r : ∀ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫) → (rs : Digit Σ) → ∀ i∙ls∙m → .(i∙ls∙m ≈  (i ∙ μ ls ∙ μ m)) → .((i ∙ μ ls ∙ μ m) ∣ μ rs) → μ⟨ Split′ i (Tree Σ) Σ ⟩≈ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
  splitTree-r i ls m rs i′ i′≈ s with splitDigit i′ rs (s ≈◄⟅ sym i′≈ ⟆)
  splitTree-r i ls m rs i′ i′≈ s | lsᵣ ∷⟨ mᵣ ⟩∷ rsᵣ [ p ] ⇑[ r≈ ] = [ lemma r≈ i′≈ ]≈ do
      ls′ ← deepᵣ ls m lsᵣ [ i ∙> (sz <∙ _) ⟿ sz ]
      rs′ ← listToTree rsᵣ [ i ∙> (_ ∙> (_ ∙> sz)) ⟿ sz ]
      ls′ ∷⟨ mᵣ ⟩∷ rs′ [ p ≈◄⟅ ≪∙ i′≈ ⍮ ℳ ↯ ⍮′ ∙≫ sym (μ ls′ ≈? (μ ls ∙ (μ m ∙ μ lsᵣ))) ⟆ ] ⇑
    where
    lemma = λ r≈ i′≈ → begin
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
          → .(i ∣ μ xs)
          → μ⟨ Split′ i (Tree Σ) Σ ⟩≈ (i ∙ μ xs)
splitTree i empty s = ⊥-elim (¬∄ℙ s)
splitTree i (single x) s = empty ∷⟨ x ⟩∷ empty [ s ≈◄⟅ ℳ ↯ ⟆ ] ⇑[ ℳ ↯ ]
splitTree i (deep (𝓂 ↤ ls & m & rs ⇑[ 𝓂≈ ])) s with ⟪ℙ?⟫ (i ∙ μ ls)
... | yes p₁ ≈ℙ i∙ls [ i∙ls≈ ] = splitTree-l i ls m rs ¬[ ¬ℙ s ]ℙ[ p₁ ]  ≈[ ∙≫ 𝓂≈ ]
... | no ¬p₁ ≈ℙ i∙ls [ i∙ls≈ ] with ⟪ℙ?⟫ (i∙ls ∙ μ m)
... | no ¬p₂ ≈ℙ i∙ls∙m [ i∙ls∙m≈ ] = splitTree-r i ls m rs i∙ls∙m (i∙ls∙m≈ ⍮ ≪∙ i∙ls≈) (s ≈▻⟅ sym 𝓂≈ ⟆ ◄ ¬p₁ ≈◄⟅ sym i∙ls≈ ⟆ ◄ ¬p₂ ≈◄⟅ ≪∙ i∙ls≈ ⟆) ≈[ ∙≫ 𝓂≈ ]
... | yes p₂ ≈ℙ i∙ls∙m [ i∙ls∙m≈ ] with splitTree i∙ls m (s ≈▻⟅ sym 𝓂≈ ⟆ ◄ ¬p₁ ≈◄⟅ sym i∙ls≈ ⟆ ▻ p₂)
... | lsₘ ∷⟨ μmₘ ↤ mₘ ⇑[ mₘ≈ ] ⟩∷ rsₘ [ sₘ ] ⇑[ m≈ ] with splitNode (i∙ls ∙ μ lsₘ) mₘ (sₘ ≈▻⟅ sym mₘ≈ ⟆)
... | lsₗ ∷⟨ mₗ ⟩∷ rsₗ [ sₗ ] ⇑[ l≈ ] = [ lemma 𝓂≈ m≈ mₘ≈ l≈ ]≈ do
      ll ← deepᵣ ls lsₘ lsₗ [ i ∙> (sz <∙ _) ⟿ sz ]
      rr ← deepₗ rsₗ rsₘ rs [ i ∙> (_ ∙> (μ mₗ ∙> sz)) ⟿ sz ]
      ll ∷⟨ mₗ ⟩∷ rr [ sₗ ≈◄⟅ ≪∙ ≪∙ i∙ls≈ ⍮ ℳ ↯ ⍮′ ∙≫ sym (μ ll ≈? (μ ls ∙ (μ lsₘ ∙ μ lsₗ))) ⟆ ] ⇑
  where
  lemma = λ 𝓂≈ m≈ mₘ≈ l≈ → begin
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


init-ℙ : ∀ {𝓂} → (¬ℙ⟨ε⟩ : False (ℙ? ε)) → (ℙ⟨xs⟩ : True (ℙ? 𝓂)) → ε ∣ 𝓂
¬ℙ (init-ℙ fl tr) = toWitnessFalse fl
!ℙ (init-ℙ fl tr) = ℙ-resp (sym (identityˡ _)) (toWitness tr)
