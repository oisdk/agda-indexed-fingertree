{-# OPTIONS --without-K --safe #-}

open import Algebra using (Monoid)

module MonoidSolver {ℓ₁ ℓ₂} (mon : Monoid ℓ₁ ℓ₂) where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; []; foldr; _++_)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Fin as Fin using (Fin)
open import Data.String as String using (String)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)

open import Relation.Binary using (Setoid)

open import Function
open import Reflection
open import Agda.Builtin.Reflection

open Monoid mon

data Expr : Set ℓ₁ where
  K   : Carrier → Expr
  _⊕_ : Expr → Expr → Expr
  E   : Expr

⟦_⟧ : Expr → Carrier
⟦ K x ⟧ = x
⟦ x ⊕ y ⟧ = ⟦ x ⟧ ∙ ⟦ y ⟧
⟦ E ⟧ = ε

Normal : Set ℓ₁
Normal = List Carrier

norm : Expr → Normal
norm (K x) = x ∷ []
norm (x ⊕ y) = norm x ++ norm y
norm E = []

⟦_,_⟧⁺⇓ : Carrier → Normal → Carrier
⟦ x , [] ⟧⁺⇓ = x
⟦ x₁ , x₂ ∷ xs ⟧⁺⇓ = x₁ ∙ ⟦ x₂ , xs ⟧⁺⇓

⟦_⟧⇓ : Normal → Carrier
⟦ [] ⟧⇓ = ε
⟦ x ∷ xs ⟧⇓ = ⟦ x , xs ⟧⁺⇓

++-homo : (xs ys : Normal) → ⟦ xs ++ ys ⟧⇓ ≈ ⟦ xs ⟧⇓ ∙ ⟦ ys ⟧⇓
++-homo [] ys = sym (identityˡ ⟦ ys ⟧⇓)
++-homo (x ∷ xs) ys = go x xs ys
  where
  go : ∀ x xs ys → ⟦ x , xs ++ ys ⟧⁺⇓ ≈ ⟦ x , xs ⟧⁺⇓ ∙ ⟦ ys ⟧⇓
  go x [] [] = sym (identityʳ x)
  go x [] (y ∷ ys) = refl
  go x₁ (x₂ ∷ xs) ys = ∙-cong refl (go x₂ xs ys) ⟨ trans ⟩ sym (assoc _ _ _)

open import FasterReasoning setoid

correct : (e : Expr) → ⟦ norm e ⟧⇓ ≈ ⟦ e ⟧
correct (K x) = refl
correct (x ⊕ y) = ++-homo (norm x) (norm y) ⟨ trans ⟩ (correct x ⟨ ∙-cong ⟩ correct y )
correct E = refl

infixr 5 _⟨∷⟩_ _⟅∷⟆_
pattern _⟨∷⟩_ x xs = arg (arg-info visible relevant) x ∷ xs
pattern _⟅∷⟆_ x xs = arg (arg-info hidden relevant) x ∷ xs

mutual
  E₂ : List (Arg Term) → Term
  E₂ (x ⟨∷⟩ y ⟨∷⟩ []) = quote _⊕_ ⟨ con ⟩ E′ x ⟨∷⟩ E′ y ⟨∷⟩ []
  E₂ (x ∷ xs) = E₂ xs
  E₂ _ = unknown

  E′ : Term → Term
  E′ (def (quote Monoid._∙_) xs) = E₂ xs
  E′ (def (quote Monoid.ε) _) = quote E ⟨ con ⟩ []
  E′ t = quote K ⟨ con ⟩ (t ⟨∷⟩ [])

getVisible : Arg Term → Maybe Term
getVisible (arg (arg-info visible relevant) x) = just x
getVisible (arg (arg-info visible irrelevant) x) = nothing
getVisible (arg (arg-info hidden r) x) = nothing
getVisible (arg (arg-info instance′ r) x) = nothing

getArgs : ∀ n → Term → Maybe (Vec Term n)
getArgs n (def _ xs) = Maybe.map Vec.reverse (List.foldl f b (List.mapMaybe getVisible xs) n)
  where
  f : (∀ n → Maybe (Vec Term n)) → Term → ∀ n → Maybe (Vec Term n)
  f xs x zero = just Vec.[]
  f xs x (suc n) = Maybe.map (x Vec.∷_) (xs n)

  b : ∀ n → Maybe (Vec Term n)
  b zero = just Vec.[]
  b (suc _ ) = nothing
getArgs _ _ = nothing

infixr 5 _⋯⟅∷⟆_
_⋯⟅∷⟆_ : ℕ → List (Arg Term) → List (Arg Term)
zero  ⋯⟅∷⟆ xs = xs
suc i ⋯⟅∷⟆ xs = unknown ⟅∷⟆ i ⋯⟅∷⟆ xs

constructSoln : Term → Term → Term → Term
constructSoln mon lhs rhs =
  quote Monoid.trans ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩
    (quote Monoid.sym ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩ (quote correct ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩ E′ lhs ⟨∷⟩ []) ⟨∷⟩ [])
    ⟨∷⟩
    (quote correct ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩ E′ rhs ⟨∷⟩ []) ⟨∷⟩
    []

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

solve-macro : Term → Term → TC ⊤
solve-macro mon hole = do
  hole′ ← inferType hole >>= normalise
  just (lhs ∷ rhs ∷ []) ← returnTC (getArgs 2 hole′)
    where nothing → typeError (termErr hole′ ∷ [])
  let soln = constructSoln mon lhs rhs
  unify hole soln ⟨ catchTC ⟩ typeError (termErr soln ∷ termErr lhs ∷ termErr rhs ∷ [])
