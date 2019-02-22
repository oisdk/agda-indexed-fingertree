{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree
  {c ℓ}
  (ℳ : Monoid c ℓ)
  where

open Monoid ℳ renaming (Carrier to 𝓡)
open import Data.Product
open import Function
open import Level using (_⊔_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; [])

open import MonoidSolver ℳ using (solve-macro)
open import Data.Unit using (⊤)
open import Reflection using (TC; Term)

macro
  _! : Term → Term → TC ⊤
  _! = solve-macro

record σ {a} (Σ : Set a) : Set (a ⊔ c) where field μ : Σ → 𝓡
open σ ⦃ ... ⦄ public
{-# DISPLAY σ.μ _ x = μ x #-}

instance
  σ-List : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (List Σ)
  μ ⦃ σ-List ⦄ = List.foldr (_∙_ ∘ μ) ε

record ⟪_⟫ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (a ⊔ c ⊔ ℓ) where
  constructor μ⟨_⟩≈_⟨_⟩
  field
    𝓢    : Σ
    μ⟨𝓢⟩ : 𝓡
    ⟪≈⟫  : μ 𝓢 ≈ μ⟨𝓢⟩
open ⟪_⟫

⟅_⟆ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Σ → ⟪ Σ ⟫
⟅ x ⟆ = μ⟨ x ⟩≈ μ x ⟨ refl ⟩

instance
  σ-⟪⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → σ ⟪ Σ ⟫
  μ ⦃ σ-⟪⟫ ⦄ = μ⟨𝓢⟩

data Digit {a} (Σ : Set a) : Set a where
  D₁ : Σ → Digit Σ
  D₂ : Σ → Σ → Digit Σ
  D₃ : Σ → Σ → Σ → Digit Σ
  D₄ : Σ → Σ → Σ → Σ → Digit Σ

instance
  σ-Digit : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Digit Σ)
  μ ⦃ σ-Digit ⦄ (D₁ x₁) = μ x₁
  μ ⦃ σ-Digit ⦄ (D₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ σ-Digit ⦄ (D₃ x₁ x₂ x₃) = μ x₁ ∙ (μ x₂ ∙ μ x₃)
  μ ⦃ σ-Digit ⦄ (D₄ x₁ x₂ x₃ x₄) = μ x₁ ∙ (μ x₂ ∙ (μ x₃ ∙ μ x₄))

data Node {a} (Σ : Set a) : Set a where
  N₂ : Σ → Σ → Node Σ
  N₃ : Σ → Σ → Σ → Node Σ

instance
  σ-Node : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Node Σ)
  μ ⦃ σ-Node ⦄ (N₂ x₁ x₂) = μ x₁ ∙ μ x₂
  μ ⦃ σ-Node ⦄ (N₃ x₁ x₂ x₃) = μ x₁ ∙ (μ x₂ ∙ μ x₃)


mutual
  record Deep {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (c ⊔ a ⊔ ℓ) where
    constructor _&_&_
    inductive
    field
      lbuff : Digit Σ
      tree  : Tree ⟪ Node Σ ⟫
      rbuff : Digit Σ

  data Tree {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (c ⊔ a ⊔ ℓ) where
    empty : Tree Σ
    single : Σ → Tree Σ
    deep : ⟪ Deep Σ ⟫  → Tree Σ

  μ-deep : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Deep Σ → 𝓡
  μ-deep (l & x & r) = μ l ∙ (μ-tree x ∙ μ r)

  μ-tree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Tree Σ → 𝓡
  μ-tree empty = ε
  μ-tree (single x) = μ x
  μ-tree (deep xs) = xs .μ⟨𝓢⟩

  instance
    σ-Deep : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Deep Σ)
    μ ⦃ σ-Deep ⦄ = μ-deep

  instance
    σ-Tree : ∀ {a} {Σ : Set a} → ⦃ _ : σ Σ ⦄ → σ (Tree Σ)
    μ ⦃ σ-Tree ⦄ = μ-tree
open Deep

{-# DISPLAY μ-tree _ x = μ x #-}
{-# DISPLAY μ-deep _ x = μ x #-}

open import FasterReasoning setoid

infixr 2 ∙≫_ ≪∙_
∙≫_ : ∀ {x y z} → x ≈ y → z ∙ x ≈ z ∙ y
∙≫_ = ∙-cong refl

≪∙_ : ∀ {x y z} → x ≈ y → x ∙ z ≈ y ∙ z
≪∙_ = flip ∙-cong refl

trans⁻¹ : ∀ {x y z : 𝓡} → y ≈ z → x ≈ y → x ≈ z
trans⁻¹ = flip trans

_◂_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (x : Σ) → (xs : Tree Σ) → Σ[ ys ∈ Tree Σ ] (μ x ∙ μ xs ≈ μ ys)
a ◂ empty = single a , identityʳ _
a ◂ single b = deep ⟅ D₁ a & empty & D₁ b ⟆ , ℳ !
a ◂ deep μ⟨ D₁ b & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ = deep μ⟨ D₂ a b & m & xs ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ ⟪≈⟫ ⟩ , refl
a ◂ deep μ⟨ D₂ b c & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ = deep μ⟨ D₃ a b c & m & xs ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ ⟪≈⟫ ⟩ , refl
a ◂ deep μ⟨ D₃ b c d & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ = deep μ⟨ D₄ a b c d & m & xs ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ ⟪≈⟫ ⟩ , refl
a ◂ deep μ⟨ D₄ b c d e & m & xs ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ with ⟅ N₃ c d e ⟆ ◂ m
... | m′ , ⟪≈⟫′ = deep μ⟨ D₂ a b & m′ & xs  ⟩≈ μ a ∙ μ⟨𝓢⟩ ⟨ assoc _ _ _ ⟨ trans ⟩ ∙≫ lemma ⟩ , refl
  where
  lemma =
    begin
      μ b ∙ (μ m′ ∙ μ xs)
    ≈˘⟨ ∙≫ (sym (assoc _ _ _) ⟨ trans ⟩ ≪∙ ⟪≈⟫′) ⟩
      μ b ∙ ((μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ xs))
    ≈˘⟨ assoc _ _ _ ⟩
      μ b ∙ (μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ xs)
    ≈⟨ ⟪≈⟫ ⟩
      μ⟨𝓢⟩
    ∎

_▸_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → (x : Σ) → Σ[ ys ∈ Tree Σ ] (μ xs ∙ μ x ≈ μ ys)
empty ▸ a = single a , ℳ !
single a ▸ b = deep ⟅ D₁ a & empty & D₁ b ⟆ , ℳ !
deep μ⟨ xs & m & D₁ a ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ ▸ b = deep μ⟨ xs & m & D₂ a b ⟩≈ μ⟨𝓢⟩ ∙ μ b ⟨ ≪∙ ⟪≈⟫ ⟨ trans⁻¹ ⟩ ℳ ! ⟩ , refl
deep μ⟨ xs & m & D₂ a b ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ ▸ c = deep μ⟨ xs & m & D₃ a b c ⟩≈ μ⟨𝓢⟩ ∙ μ c ⟨ ≪∙ ⟪≈⟫ ⟨ trans⁻¹ ⟩ ℳ ! ⟩ , refl
deep μ⟨ xs & m & D₃ a b c ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ ▸ d = deep μ⟨ xs & m & D₄ a b c d ⟩≈ μ⟨𝓢⟩ ∙ μ d ⟨ ≪∙ ⟪≈⟫ ⟨ trans⁻¹ ⟩ ℳ ! ⟩ , refl
deep μ⟨ xs & m & D₄ a b c d ⟩≈ μ⟨𝓢⟩ ⟨ ⟪≈⟫ ⟩ ▸ e with m ▸ ⟅ N₃ a b c ⟆
... | m′ , ⟪≈⟫′ = deep μ⟨ xs & m′ & D₂ d e ⟩≈ μ⟨𝓢⟩ ∙ μ e ⟨ lemma ⟩ , refl
  where
  lemma =
    begin
      μ (xs & m′ & D₂ d e)
    ≡⟨⟩
      μ xs ∙ (μ m′ ∙ (μ d ∙ μ e))
    ≈˘⟨ ∙≫ ≪∙ ⟪≈⟫′ ⟩
      μ xs ∙ (μ m ∙ (μ a ∙ (μ b ∙ μ c)) ∙ (μ d ∙ μ e))
    ≈⟨ ℳ ! ⟩
      μ xs ∙ (μ m ∙ (μ a ∙ (μ b ∙ (μ c ∙ μ d)))) ∙ μ e
    ≈⟨ ≪∙ ⟪≈⟫ ⟩
      μ⟨𝓢⟩ ∙ μ e
    ∎

open import Relation.Unary
open import Relation.Nullary
open import Relation.Binary hiding (Decidable)

module Splitting
  {s}
  {ℙ : Pred 𝓡 s}
  (ℙ-resp : ℙ Respects _≈_)
  (ℙ? : Decidable ℙ)
  (mono-ℙ : ∀ x y → ℙ x → ℙ (x ∙ y))
  where
  open import Data.Empty using (⊥-elim)

  mono-¬ℙ : ∀ x y → ¬ ℙ (x ∙ y) → ¬ ℙ x
  mono-¬ℙ x y ¬ℙ⟨x∙y⟩ ℙ⟨x⟩ = ¬ℙ⟨x∙y⟩ (mono-ℙ x y ℙ⟨x⟩)

  ∃¬ℙ⇒¬ℙ⟨ε⟩ : ∃[ x ] (¬ ℙ x) → ¬ ℙ ε
  ∃¬ℙ⇒¬ℙ⟨ε⟩ (x , ¬ℙ⟨x⟩) ℙ⟨ε⟩ = ¬ℙ⟨x⟩ (ℙ-resp (identityˡ _) (mono-ℙ ε x ℙ⟨ε⟩))

  record Split {a b} (Σ : Set a) (A : Set b) ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ : Set (s ⊔ a ⊔ b) where
    constructor _∷⟨_⟩∷_
    field
      ¬ℙ : Σ[ xs ∈ Σ ] ¬ ℙ (μ xs)
      !ℙ : Σ[ x  ∈ A ] ℙ (μ x)
      ?ℙ : Σ
  open Split

  instance
    σ-Split : ∀ {a b} {Σ : Set a} {A : Set b} ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ → σ (Split Σ A)
    μ ⦃ σ-Split ⦄ ((l , _) ∷⟨ x , _ ⟩∷ r) = μ l ∙ (μ x ∙ μ r)

  -- splitNode : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → ∃[ x ] (¬ ℙ x) → (xs : Node Σ) → ℙ (μ xs) → Σ[ ys ∈ Split (List Σ) Σ ] (μ xs ≈ μ ys)
  -- splitNode (x₁ , ¬ℙx) (N₂ x₂ x₃) ℙ⟨xs⟩ with ℙ? (x₁ ∙ μ x₂)
  -- splitNode i (N₂ x₂ x₃) ℙ⟨xs⟩ | yes p = (([] , ∃¬ℙ⇒¬ℙ⟨ε⟩ i) ∷⟨ x₂ , {!!} ⟩∷ (x₃ ∷ [])) , ℳ !
  -- splitNode (x₁ , ¬ℙx) (N₂ x₂ x₃) ℙ⟨xs⟩ | no ¬p = ((x₂ ∷ [] , {!!} ∘ ℙ-resp (identityʳ _)) ∷⟨ x₃ , {!!} ⟩∷ []) , ℳ !
  -- splitNode (x₁ , ¬ℙx) (N₃ x₂ x₃ x₄) ℙ⟨xs⟩ = {!!}

