{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree
  {c m}
  (ℳ : Monoid c m)
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
  _↯ : Term → Term → TC ⊤
  _↯ = solve-macro

record σ {a} (Σ : Set a) : Set (a ⊔ c) where field μ : Σ → 𝓡
open σ ⦃ ... ⦄ public
{-# DISPLAY σ.μ _ x = μ x #-}

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
--   ⟨ Σ ⟩μ⁻¹[ x ]
--
-- Means "The Σ such that μ Σ ≈ x"

infixr 4 _↦_
record ⟨_⟩μ⁻¹[_] {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (𝑌 : 𝓡) : Set (a ⊔ c ⊔ m) where
  constructor _↦_
  field
    𝓢 : Σ
    μ⟨𝓢⟩≈𝑌 : μ 𝓢 ≈ 𝑌
open ⟨_⟩μ⁻¹[_]

μ[_] : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (𝓢 : Σ) → ⟨ Σ ⟩μ⁻¹[ μ 𝓢 ]
𝓢 μ[ x ] = x
μ⟨𝓢⟩≈𝑌 μ[ x ] = refl

⟪_⟫ : ∀ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ → Set (a ⊔ c ⊔ m)
⟪ Σ ⟫ = ∃ ⟨ Σ ⟩μ⁻¹[_]

⟅_⟆ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Σ → ⟪ Σ ⟫
⟅ x ⟆ = μ x , μ[ x ]

infixr 2 ⟪⟫-syntax
⟪⟫-syntax : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (𝓢 : Σ) → (𝑌 : 𝓡) → μ 𝓢 ≈ 𝑌 → ⟪ Σ ⟫
⟪⟫-syntax 𝓢 𝑌 μ⟨𝓢⟩≈𝑌 = 𝑌 , 𝓢 ↦ μ⟨𝓢⟩≈𝑌

syntax ⟪⟫-syntax 𝓢 𝑌 μ⟨𝓢⟩≈𝑌 = 𝓢 μ≈⟨ μ⟨𝓢⟩≈𝑌 ⟩ 𝑌


instance
  σ-⟪⟫ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → σ ⟪ Σ ⟫
  μ ⦃ σ-⟪⟫ ⦄ = proj₁

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
  infixr 5 _&_&_
  record Deep {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (c ⊔ a ⊔ m) where
    constructor _&_&_
    inductive
    field
      lbuff : Digit Σ
      tree  : Tree ⟪ Node Σ ⟫
      rbuff : Digit Σ

  data Tree {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ : Set (c ⊔ a ⊔ m) where
    empty : Tree Σ
    single : Σ → Tree Σ
    deep : ⟪ Deep Σ ⟫  → Tree Σ

  μ-deep : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Deep Σ → 𝓡
  μ-deep (l & x & r) = μ l ∙ (μ-tree x ∙ μ r)

  μ-tree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → Tree Σ → 𝓡
  μ-tree empty = ε
  μ-tree (single x) = μ x
  μ-tree (deep xs) = xs .proj₁

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

infixl 1 _；_
_；_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
_；_ = trans

infixl 1 trans⁻¹
trans⁻¹ : ∀ {x y z : 𝓡} → y ≈ z → x ≈ y → x ≈ z
trans⁻¹ = flip trans

syntax trans⁻¹ y≈z x≈y = x≈y ⍮ y≈z

_◂_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (x : Σ) → (xs : Tree Σ) → ⟨ Tree Σ ⟩μ⁻¹[ μ x ∙ μ xs ]
a ◂ empty = single a ↦ ℳ ↯
a ◂ single b = deep ⟅ D₁ a & empty & D₁ b ⟆ ↦ ℳ ↯
a ◂ deep (μ⟨𝓢⟩ , D₁ b       & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) = deep (D₂ a b     & m & rs μ≈⟨ assoc _ _ _ ； ∙≫ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
a ◂ deep (μ⟨𝓢⟩ , D₂ b c     & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) = deep (D₃ a b c   & m & rs μ≈⟨ assoc _ _ _ ； ∙≫ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
a ◂ deep (μ⟨𝓢⟩ , D₃ b c d   & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) = deep (D₄ a b c d & m & rs μ≈⟨ assoc _ _ _ ； ∙≫ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
a ◂ deep (μ⟨𝓢⟩ , D₄ b c d e & m & rs ↦ μ⟨xs⟩≈μ⟨𝓢⟩) with ⟅ N₃ c d e ⟆ ◂ m
... | m′ ↦ c∙d∙e∙m≈μ⟨m′⟩ = deep (D₂ a b & m′ & rs μ≈⟨ assoc _ _ _ ； ∙≫ lemma ⟩ μ a ∙ μ⟨𝓢⟩) ↦ refl
  where
  lemma =
    begin
      μ b ∙ (μ m′ ∙ μ rs)
    ≈˘⟨ ∙≫ (sym (assoc _ _ _) ⟨ trans ⟩ ≪∙ sym c∙d∙e∙m≈μ⟨m′⟩) ⟩
      μ b ∙ ((μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ rs))
    ≈˘⟨ assoc _ _ _ ⟩
      μ b ∙ (μ c ∙ (μ d ∙ μ e)) ∙ (μ m ∙ μ rs)
    ≈⟨ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩
      μ⟨𝓢⟩
    ∎

_▸_ : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : Tree Σ) → (x : Σ) → ⟨ Tree Σ ⟩μ⁻¹[ μ xs ∙ μ x ]
empty ▸ a = single a ↦ ℳ ↯
single a ▸ b = deep ⟅ D₁ a & empty & D₁ b ⟆ ↦ ℳ ↯
deep (μ⟨𝓢⟩ , ls & m & D₁ a       ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ b = deep (ls & m & D₂ a b     μ≈⟨ ℳ ↯ ⍮ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ b) ↦ refl
deep (μ⟨𝓢⟩ , ls & m & D₂ a b     ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ c = deep (ls & m & D₃ a b c   μ≈⟨ ℳ ↯ ⍮ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ c) ↦ refl
deep (μ⟨𝓢⟩ , ls & m & D₃ a b c   ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ d = deep (ls & m & D₄ a b c d μ≈⟨ ℳ ↯ ⍮ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩ μ⟨𝓢⟩ ∙ μ d) ↦ refl
deep (μ⟨𝓢⟩ , ls & m & D₄ a b c d ↦ μ⟨xs⟩≈μ⟨𝓢⟩) ▸ e with m ▸ ⟅ N₃ a b c ⟆
... | m′ ↦ m∙a∙b∙c≈μ⟨m′⟩ = deep ( ls & m′ & D₂ d e μ≈⟨ lemma ⟩ μ⟨𝓢⟩ ∙ μ e ) ↦ refl
  where
  lemma =
    begin
      μ (ls & m′ & D₂ d e)
    ≡⟨⟩
      μ ls ∙ (μ m′ ∙ (μ d ∙ μ e))
    ≈˘⟨ ∙≫ ≪∙ sym m∙a∙b∙c≈μ⟨m′⟩ ⟩
      μ ls ∙ (μ m ∙ (μ a ∙ (μ b ∙ μ c)) ∙ (μ d ∙ μ e))
    ≈⟨ ℳ ↯ ⟩
      μ ls ∙ (μ m ∙ (μ a ∙ (μ b ∙ (μ c ∙ μ d)))) ∙ μ e
    ≈⟨ ≪∙ μ⟨xs⟩≈μ⟨𝓢⟩ ⟩
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

  mono-¬ℙ : ∀ x y → ¬ ℙ (x ∙ y) → ¬ ℙ x
  mono-¬ℙ x y ¬ℙ⟨x∙y⟩ ℙ⟨x⟩ = ¬ℙ⟨x∙y⟩ (mono-ℙ x y ℙ⟨x⟩)

  ∃¬ℙ⇒¬ℙ⟨ε⟩ : ∃[ x ] (¬ ℙ x) → ¬ ℙ ε
  ∃¬ℙ⇒¬ℙ⟨ε⟩ (x , ¬ℙ⟨x⟩) ℙ⟨ε⟩ = ¬ℙ⟨x⟩ (ℙ-resp (identityˡ _) (mono-ℙ ε x ℙ⟨ε⟩))

  _⇒_⟨_⟩ : ∀ {x} → ℙ x → ∀ y → x ≈ y → ℙ y
  ℙ⟨x⟩ ⇒ y ⟨ x≈y ⟩ = ℙ-resp x≈y ℙ⟨x⟩

  _⇏_⟨_⟩ : ∀ {x} → ¬ ℙ x → ∀ y → x ≈ y → ¬ ℙ y
  ℙ⟨x⟩ ⇏ y ⟨ x≈y ⟩ = ℙ⟨x⟩ ∘ ℙ-resp (sym x≈y)

  infixr 5 _∷⟨_⟩∷_[_,_]
  record Split {a b} (i : 𝓡) (Σ : Set a) (A : Set b) ⦃ _ : σ Σ ⦄ ⦃ _ : σ A ⦄ : Set (c ⊔ a ⊔ s ⊔ b) where
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

  data ⟪Dec⟫ (x : 𝓡) : Set (c ⊔ s ⊔ m) where
    ⟪yes⟫ : ∀ y → y ≈ x → ℙ y → ⟪Dec⟫ x
    ⟪no⟫  : ∀ y → y ≈ x → ¬ ℙ y → ⟪Dec⟫ x

  ⟪ℙ?⟫ : ∀ x → ⟪Dec⟫ x
  ⟪ℙ?⟫ x with ℙ? x
  ⟪ℙ?⟫ x | yes p = ⟪yes⟫ x refl p
  ⟪ℙ?⟫ x | no ¬p = ⟪no⟫ x refl ¬p

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
    splitNode i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ | zs ↦ i∙μ⟨zs⟩≈i∙μ⟨ys⟩ = zs ↦ (i∙μ⟨zs⟩≈i∙μ⟨ys⟩ ； ∙≫ μ⟨ys⟩≈μ⟨xs⟩)


    splitDigit : ∀ i → ¬ ℙ i → (xs : Digit Σ) → ℙ (i ∙ μ xs) → ⟨ Split i (List Σ) Σ ⟩μ⁻¹[ i ∙ μ xs ]
    splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ with digitToList xs
    splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ with splitList i ¬ℙ⟨i⟩ ys (ℙ-resp (∙≫ sym μ⟨ys⟩≈μ⟨xs⟩) ℙ⟨i∙xs⟩)
    splitDigit i ¬ℙ⟨i⟩ xs ℙ⟨i∙xs⟩ | ys ↦ μ⟨ys⟩≈μ⟨xs⟩ | zs ↦ i∙μ⟨zs⟩≈i∙μ⟨ys⟩ = zs ↦ (i∙μ⟨zs⟩≈i∙μ⟨ys⟩ ； ∙≫ μ⟨ys⟩≈μ⟨xs⟩)
