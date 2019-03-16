open import Algebra

module Data.FingerTree.AssocFree {ℓ₁ ℓ₂} (m : Monoid ℓ₁ ℓ₂) where

open import Function

open Monoid m

Assoc : Set ℓ₁
Assoc = Carrier → Carrier

⟦_⇑⟧ : Carrier → Assoc
⟦_⇑⟧ = _∙_

⟦_⇓⟧ : Assoc → Carrier
⟦ x ⇓⟧ = x ε

⇑↔⇓ : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≈ x
⇑↔⇓ = identityʳ

_⟦∙⟧_ : Assoc → Assoc → Assoc
_⟦∙⟧_ = _∘′_

⟦ε⟧ : Assoc
⟦ε⟧ = id

∙-homo : ∀ x y → ⟦ ⟦ x ⇑⟧ ⟦∙⟧ ⟦ y ⇑⟧ ⇓⟧ ≈ x ∙ y
∙-homo x y = sym (assoc _ _ _) ⟨ trans ⟩ identityʳ _

ε-homo : ⟦ ⟦ε⟧ ⇓⟧ ≈ ε
ε-homo = refl
