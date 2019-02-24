{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree.Reasoning
  {r m}
  (ℳ : Monoid r m)
  where

open Monoid ℳ renaming (Carrier to 𝓡)
open import FasterReasoning setoid public

open import MonoidSolver ℳ using (solve-macro)

open import Data.Unit using (⊤)
open import Reflection using (TC; Term)

macro
  _↯ : Term → Term → TC ⊤
  _↯ = solve-macro

infixr 2 ∙≫_ ≪∙_
∙≫_ : ∀ {x y z} → x ≈ y → z ∙ x ≈ z ∙ y
∙≫_ = ∙-cong refl

≪∙_ : ∀ {x y z} → x ≈ y → x ∙ z ≈ y ∙ z
≪∙ x = ∙-cong x refl

infixl 1 _⍮_
_⍮_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
_⍮_ = trans

infixl 1 trans⁻¹
trans⁻¹ : ∀ {x y z : 𝓡} → y ≈ z → x ≈ y → x ≈ z
trans⁻¹ x y = trans y x

syntax trans⁻¹ y≈z x≈y = x≈y ⍮′ y≈z

infixr 2 _↢_ ↣-syntax ↣↣-syntax
_↢_ : ∀ x {y} → x ≈ y → x ≈ y
_ ↢ x≈y = x≈y

↣-syntax : ∀ {x} y → x ≈ y → x ≈ y
↣-syntax _ x≈y = x≈y

syntax ↣-syntax y x≈y = x≈y ↣ y

↣↣-syntax : ∀ x y → x ≈ y → x ≈ y
↣↣-syntax _ _ x≈y = x≈y

syntax ↣↣-syntax x y x≈y = x ↣⟨ x≈y ⟩↣ y

infixl 6 _∙>_ _<∙_
_∙>_ : ∀ x {y z} → y ≈ z → x ∙ y ≈ x ∙ z
_ ∙> y≈z = ∙≫ y≈z

_<∙_ : ∀ {x y} → x ≈ y → ∀ z → x ∙ z ≈ y ∙ z
x≈y <∙ _ = ≪∙ x≈y
