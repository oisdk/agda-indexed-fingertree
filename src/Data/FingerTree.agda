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
open import Data.FingerTree.Measures ℳ
open import MonoidSolver ℳ using (solve-macro)
open import Data.Unit using (⊤)
open import Reflection using (TC; Term)
open import Data.FingerTree.Reasoning ℳ
open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Cons ℳ

open import Relation.Unary
open import Relation.Nullary
open import Relation.Binary hiding (Decidable)
