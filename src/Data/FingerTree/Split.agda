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

-- open import Relation.Binary.Construct.FromPred setoid ℙ as PredRel
-- open import Relation.Binary.Reasoning.Preorder (PredRel.preorder ℙ-resp)

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
  splitNode i xs s =  nodeToList xs [ _ ∙> sz ⟿ sz ] (λ ys {x≈} → splitList i ys (s ≈▻⟅ sym x≈ ⟆))

  splitDigit : ∀ i → (xs : Digit Σ) → i ⟅ μ xs ⟆ → μ⟨ Split i (List Σ) Σ ⟩≈ (i ∙ μ xs)
  splitDigit i xs s = digitToList xs [ _ ∙> sz ⟿ sz ] λ ys {x≈} → splitList i ys (s ≈▻⟅ sym x≈ ⟆)


  -- splitTree-l : ∀ i → ¬ ℙ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫)  → (rs : Digit Σ) → ℙ (i ∙ μ ls) → ⟨ Split i (Tree Σ) Σ ⟩μ⁻¹ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
--   splitTree-l i ¬ℙ⟨i⟩ ls m rs ℙ⟨i∙ls⟩ with splitDigit i ¬ℙ⟨i⟩ ls ℙ⟨i∙ls⟩
--   ... | lsₗ ∷⟨ mₗ ⟩∷ rsₗ [ p₁ , p₂ ] ↦ p₃ with listToTree lsₗ | deepₗ rsₗ m rs
--   ... | ls′ ↦ ls′≈ | rs′ ↦ rs′≈ = ls′ ∷⟨ mₗ ⟩∷ rs′ [ p₁ ∘′ ℙ-resp (∙≫ ls′≈) , ℙ-resp (∙≫ ≪∙ sym ls′≈) p₂ ] ↦ lemma
--     where
--     lemma =
--       begin
--         i ∙ (μ ls′ ∙ (μ mₗ ∙ μ rs′))
--       ≈⟨ ∙≫ ≪∙ ls′≈ ⟩
--         i ∙ (μ lsₗ ∙ (μ mₗ ∙ μ rs′))
--       ≈⟨ ∙≫ ∙≫ ∙≫ rs′≈  ⟩
--         i ∙ (μ lsₗ ∙ (μ mₗ ∙ (μ rsₗ ∙ (μ m ∙ μ rs))))
--       ≈⟨ ℳ ↯ ⟩
--         i ∙ (μ lsₗ ∙ (μ mₗ ∙ μ rsₗ)) ∙ (μ m ∙ μ rs)
--       ≈⟨ ≪∙ p₃ ⟩
--         i ∙ μ ls ∙ (μ m ∙ μ rs)
--       ≈⟨ ℳ ↯ ⟩
--         i ∙ (μ ls ∙ (μ m ∙ μ rs))
--       ∎

--   splitTree-r : ∀ i → ¬ ℙ i → (ls : Digit Σ) → (m : Tree ⟪ Node Σ ⟫)  → (rs : Digit Σ) → ℙ (i ∙ (μ ls ∙ (μ m ∙ μ rs))) → ∀ i′ → i′ ≈ i ∙(μ ls ∙ μ m) → ¬ ℙ (i ∙ (μ ls ∙ μ m)) → ⟨ Split i (Tree Σ) Σ ⟩μ⁻¹ (i ∙ (μ ls ∙ (μ m ∙ μ rs)))
--   splitTree-r i ¬ℙ⟨i⟩ ls m rs ℙ⟨xs⟩ i′ ⟪i′⟫ ¬ℙ⟨i∙ls∙m⟩ with splitDigit i′ (¬ℙ⟨i∙ls∙m⟩ ∘′ ℙ-resp ⟪i′⟫) rs (ℙ-resp (ℳ ↯ ⍮′ ≪∙ sym ⟪i′⟫) ℙ⟨xs⟩)
--   splitTree-r i ¬ℙ⟨i⟩ ls m rs ℙ⟨xs⟩ i′ ⟪i′⟫ ¬ℙ⟨i∙ls∙m⟩ | lsᵣ ∷⟨ mᵣ ⟩∷ rsᵣ [ p₁ , p₂ ] ↦ p₃ with deepᵣ ls m lsᵣ | listToTree rsᵣ
--   splitTree-r i ¬ℙ⟨i⟩ ls m rs ℙ⟨xs⟩ i′ ⟪i′⟫ ¬ℙ⟨i∙ls∙m⟩ | lsᵣ ∷⟨ mᵣ ⟩∷ rsᵣ [ p₁ , p₂ ] ↦ p₃ | ls′ ↦ ls′≈ | rs′ ↦ rs′≈ = ls′ ∷⟨ mᵣ ⟩∷ rs′ [ p₁ ∘′ ℙ-resp lemma₁ , ℙ-resp lemma₂ p₂ ] ↦ lemma₃
--     where
--     lemma₁ =
--       begin
--         i ∙ μ ls′
--       ≈⟨ ∙≫ ls′≈ ⟩
--         i ∙ (μ ls ∙ (μ m ∙ μ lsᵣ))
--       ≈⟨ ℳ ↯ ⟩
--         (i ∙ (μ ls ∙ μ m)) ∙ μ lsᵣ
--       ≈˘⟨ ≪∙ ⟪i′⟫ ⟩
--         i′ ∙ μ lsᵣ
--       ∎
--     lemma₂ =
--       begin
--         i′ ∙ (μ lsᵣ ∙ μ mᵣ)
--       ≈⟨ ≪∙ ⟪i′⟫ ⟩
--         (i ∙ (μ ls ∙ μ m)) ∙ (μ lsᵣ ∙ μ mᵣ)
--       ≈⟨ ℳ ↯ ⟩
--         i ∙ ((μ ls ∙ (μ m ∙ μ lsᵣ)) ∙ μ mᵣ)
--       ≈˘⟨ ∙≫ ≪∙ ls′≈ ⟩
--         i ∙ (μ ls′ ∙ μ mᵣ)
--       ∎
--     lemma₃ =
--       begin
--         i ∙ (μ ls′ ∙ (μ mᵣ ∙ μ rs′))
--       ≈⟨ ∙≫ ∙-cong ls′≈ (∙≫ rs′≈) ⟩
--         i ∙ ((μ ls ∙ (μ m ∙ μ lsᵣ)) ∙ (μ mᵣ ∙ μ rsᵣ))
--       ≈⟨ ℳ ↯ ⟩
--         (i ∙ (μ ls ∙ μ m)) ∙ (μ lsᵣ ∙ (μ mᵣ ∙ μ rsᵣ))
--       ≈˘⟨ ≪∙ ⟪i′⟫ ⟩
--         i′ ∙ (μ lsᵣ ∙ (μ mᵣ ∙ μ rsᵣ))
--       ≈⟨ p₃ ⟩
--         i′ ∙ μ rs
--       ≈⟨ ≪∙ ⟪i′⟫ ⟩
--         (i ∙ (μ ls ∙ μ m)) ∙ μ rs
--       ≈⟨ ℳ ↯ ⟩
--         i ∙ (μ ls ∙ (μ m ∙ μ rs))
--       ∎



splitTree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → ∀ i → (xs : Tree Σ) → i ⟅ μ xs ⟆ → μ⟨ Split i (Tree Σ) Σ ⟩≈ (i ∙ μ xs)
splitTree i empty s = ⊥-elim (¬∄ℙ s)
splitTree i (single x) s = empty ∷⟨ x ⟩∷ empty [ s ≈◄⟅ ℳ ↯ ⟆ ] ⇑[ ℳ ↯ ]
splitTree i (deep (𝓂 ↤ ls & m & rs ⇑[ 𝓂≈ ])) s with ⟪ℙ?⟫ (i ∙ μ ls)
... | yes p₁ ≈ℙ i∙ls [ i∙ls≈ ] = {!!}
... | no ¬p₁ ≈ℙ i∙ls [ i∙ls≈ ] with ⟪ℙ?⟫ (i∙ls ∙ μ m)
... | no ¬p₂ ≈ℙ i∙ls∙m [ i∙ls∙m≈ ] = {!!}
... | yes p₂ ≈ℙ i∙ls∙m [ i∙ls∙m≈ ] with splitTree i∙ls m (s ≈▻⟅ sym 𝓂≈ ⟆ ◄ ¬p₁ ≈◄⟅ sym i∙ls≈ ⟆ ▻ p₂)
... | res = {!!}

-- splitTree i ¬ℙ⟨i⟩ empty ℙ⟨i∙xs⟩ = ⊥-elim (¬ℙ⟨i⟩ (ℙ-resp (identityʳ _) ℙ⟨i∙xs⟩))
-- splitTree i ¬ℙ⟨i⟩ (single x) ℙ⟨i∙xs⟩ = empty ∷⟨ x ⟩∷ empty [ ¬ℙ⟨i⟩ ∘ ℙ-resp (identityʳ _) , ℙ⟨i∙xs⟩ ⇒ i ∙ (ε ∙ μ x) ⟨ ℳ ↯ ⟩ ] ↦ ℳ ↯
-- splitTree i ¬ℙ⟨i⟩ (deep (μ⟨xs⟩ , ls & m & rs ↦ μ⟨xs⟩≈)) ℙ⟨i∙xs⟩ with ⟪ℙ? (i ∙ μ ls) ⇓⟫
-- ... | ⟪ i′ ⟨ ⟪i′⟫ ⟩ yes p ?⟫ = splitTree-l i ¬ℙ⟨i⟩ ls m rs p ≈[ ∙≫ μ⟨xs⟩≈ ]
-- ... | ⟪ i′ ⟨ ⟪i′⟫ ⟩ no ¬p ?⟫ with ⟪ℙ? (i′ ∙ μ m) ⇓⟫
-- ... | ⟪ i″ ⟨ ⟪i″⟫ ⟩ no ¬p′ ?⟫ = splitTree-r i ¬ℙ⟨i⟩ ls m rs (ℙ-resp (∙≫ sym (μ⟨xs⟩≈)) ℙ⟨i∙xs⟩) i″ (sym ⟪i″⟫ ⍮ (≪∙ sym ⟪i′⟫ ⍮ assoc _ _ _)) (¬p′ ∘′ ℙ-resp (sym (assoc _ _ _) ⍮ ≪∙ ⟪i′⟫)) ≈[ ∙≫ μ⟨xs⟩≈ ]
-- ... | ⟪ i″ ⟨ ⟪i″⟫ ⟩ yes p′ ?⟫ with splitTree i′ (¬p ∘′ ℙ-resp (sym ⟪i′⟫)) m p′
-- ... | lsₘ ∷⟨ μ⟨mₘ⟩ , mₘ ↦ mₘ≈ ⟩∷ rsₘ [ p₁ , p₂ ] ↦ p₃ with splitNode (i′ ∙ μ lsₘ) p₁ mₘ (ℙ-resp (sym (assoc _ _ _) ⍮ ∙≫ sym mₘ≈) p₂)
-- ... | l ∷⟨ x ⟩∷ r [ p₄ , p₅ ] ↦ p₆ with deepᵣ ls lsₘ l | deepₗ r rsₘ rs
-- ... | ls′ ↦ ls′≈ | rs′ ↦ rs′≈ = ls′ ∷⟨ x ⟩∷ rs′ [ p₄ ∘′ ℙ-resp lemma₁ , ℙ-resp lemma₂ p₅ ] ↦ (lemma₃ ⍮ ∙≫ μ⟨xs⟩≈)
--   where
--   lemma₁ =
--     begin
--       i ∙ μ ls′
--     ≈⟨ ∙≫ ls′≈ ⟩
--       i ∙ (μ ls ∙ (μ lsₘ ∙ μ l))
--     ≈˘⟨ assoc _ _ _ ⟩
--       (i ∙ μ ls) ∙ (μ lsₘ ∙ μ l)
--     ≈⟨ ≪∙ ⟪i′⟫ ⟩
--       i′ ∙ (μ lsₘ ∙ μ l)
--     ≈˘⟨ assoc _ _ _ ⟩
--       i′ ∙ μ lsₘ ∙ μ l
--     ∎
--   lemma₂ =
--     begin
--       i′ ∙ μ lsₘ ∙ (μ l ∙ μ x)
--     ≈˘⟨ ≪∙ ≪∙ ⟪i′⟫ ⟩
--       (i ∙ μ ls) ∙ μ lsₘ ∙ (μ l ∙ μ x)
--     ≈⟨ ℳ ↯ ⟩
--       i ∙ ((μ ls ∙ (μ lsₘ ∙ μ l)) ∙ μ x)
--     ≈˘⟨ ∙≫ ≪∙ ls′≈ ⟩
--       i ∙ (μ ls′ ∙ μ x)
--     ∎
--   lemma₃ =
--     begin
--       i ∙ (μ ls′ ∙ (μ x ∙ μ rs′))
--     ≈⟨ ∙≫ ∙-cong ls′≈ (∙≫ rs′≈) ⟩
--       i ∙ ((μ ls ∙ (μ lsₘ ∙ μ l)) ∙ (μ x ∙ (μ r ∙ (μ rsₘ ∙ μ rs))))
--     ≈⟨ ℳ ↯ ⟩
--       (i ∙ μ ls) ∙ (μ lsₘ ∙ μ l) ∙ (μ x ∙ (μ r ∙ (μ rsₘ ∙ μ rs)))
--     ≈⟨ ≪∙ ≪∙ ⟪i′⟫ ⟩
--       i′ ∙ (μ lsₘ ∙ μ l) ∙ (μ x ∙ (μ r ∙ (μ rsₘ ∙ μ rs)))
--     ≈⟨ ℳ ↯ ⟩
--       (i′ ∙ μ lsₘ ∙ (μ l ∙ (μ x ∙ μ r))) ∙ (μ rsₘ ∙ μ rs)
--     ≈⟨ ≪∙ p₆ ⟩
--       (i′ ∙ μ lsₘ ∙ μ mₘ) ∙ (μ rsₘ ∙ μ rs)
--     ≈⟨ ≪∙ ∙≫ mₘ≈ ⟩
--       (i′ ∙ μ lsₘ ∙ μ⟨mₘ⟩) ∙ (μ rsₘ ∙ μ rs)
--     ≈⟨ ℳ ↯ ⟩
--       (i′ ∙ (μ lsₘ ∙ (μ⟨mₘ⟩ ∙ μ rsₘ))) ∙ μ rs
--     ≈⟨ ≪∙ p₃ ⟩
--       i′ ∙ μ m ∙ μ rs
--     ≈⟨ assoc _ _ _ ⟩
--       i′ ∙ (μ m ∙ μ rs)
--     ≈⟨ (≪∙ sym ⟪i′⟫ ⍮ assoc _ _ _) ⟩
--       i ∙ (μ ls ∙ (μ m ∙ μ rs))
--     ∎
