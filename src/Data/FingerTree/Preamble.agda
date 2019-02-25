module Data.FingerTree.Preamble where

open import Algebra public
open import Function public
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl) public
open import Level as ℓ using (_⊔_) public
open import Data.List using (List; _∷_; []; foldr) public
open import Data.Vec using (Vec; _∷_; []) public
import Data.FingerTree.Measures
record Imports c m a : Set (ℓ.suc (c ⊔ m ⊔ a)) where
  field
    ℳ : Monoid c m
  open Monoid ℳ hiding (refl) renaming (Carrier to 𝓡) public
  field
    A : Set a
  open Data.FingerTree.Measures ℳ using (σ) public
  open σ ⦃ ... ⦄ public
  field
    ⦃ σ-A ⦄ : σ A
  open import Algebra.FunctionProperties _≈_ public
  open import Data.FingerTree.Reasoning ℳ public
  open import Data.FingerTree.Cons ℳ using (_◂_) public
  open import Data.FingerTree.Structures ℳ public
