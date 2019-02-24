open import Relation.Binary

module Relation.Binary.Reasoning.FasterInference.Preorder {ℓ₁ ℓ₂ ℓ₃} (preorder : Preorder ℓ₁ ℓ₂ ℓ₃) where

open import Level using (Level; _⊔_)
open Preorder preorder
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Function

data _IsRelatedTo_ (x y : Carrier) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  nonstrict : (x∼y : x ∼ y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

levelOf : ∀ {x y} → x IsRelatedTo y → Level
levelOf (nonstrict x∼y) = ℓ₃
levelOf (equals    x≈y) = ℓ₂

relOf : ∀ {x y} (r : x IsRelatedTo y) → Rel Carrier (levelOf r)
relOf (nonstrict x∼y) = _∼_
relOf (equals x≈y) = _≈_

data IsEquality {x y} : x IsRelatedTo y → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? (nonstrict _) = no λ()
IsEquality? (equals x≈y)  = yes (isEquality x≈y)

extractEquality : ∀ {x y} {x≲y : x IsRelatedTo y} → IsEquality x≲y → x ≈ y
extractEquality (isEquality x≈y) = x≈y

infix -1 begin_ begin-equality_

begin_ : ∀ {x y} (r : x IsRelatedTo y) → x ∼ y
begin (nonstrict x∼y) = x∼y
begin (equals x≈y) = reflexive x≈y

begin-equality_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsEquality? r)} → x ≈ y
begin-equality_ r {s} = extractEquality (toWitness s)

infix 1 _∎

_∎ : ∀ x → x IsRelatedTo x
x ∎ = equals Eq.refl

infixr 0 _≡⟨⟩_
_≡⟨⟩_ : ∀ (x : Carrier) {y} → x IsRelatedTo y → x IsRelatedTo y
x ≡⟨⟩ x≲y = x≲y

infixr 0 step-≈ step-≈˘ step-≡ step-≡˘ step-∼
step-≈ : ∀ x {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
step-≈ _ (nonstrict y∼z) x≈y = nonstrict (proj₂ ∼-resp-≈ (Eq.sym x≈y) y∼z)
step-≈ _ (equals    y≈z) x≈y = equals (Eq.trans x≈y y≈z)

syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ x yRz y≈x = step-≈ x yRz (Eq.sym y≈x)

syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z

step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ x (nonstrict y∼z) x≡y = nonstrict (case x≡y of λ where ≡.refl → y∼z)
step-≡ x (equals    y≈z) x≡y = equals    (case x≡y of λ where ≡.refl → y≈z)

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ x y≈z y≡x = step-≡ x y≈z (≡.sym y≡x)

syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

step-∼ : ∀ x {y z} → y IsRelatedTo z → x ∼ y → x IsRelatedTo z
step-∼ _ (nonstrict y∼z) x∼y = nonstrict (trans x∼y y∼z)
step-∼ _ (equals    y≈z) x∼y = nonstrict (proj₁ ∼-resp-≈ y≈z x∼y)

syntax step-∼ x y≈z x∼y = x ∼⟨ x∼y ⟩ y≈z
