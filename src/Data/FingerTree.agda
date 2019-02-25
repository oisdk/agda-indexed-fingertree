{-# OPTIONS --without-K --safe #-}

open import Algebra

module Data.FingerTree
  {c m}
  (ℳ : Monoid c m)
  where

open import Data.FingerTree.Structures ℳ
open import Data.FingerTree.Cons       ℳ
open import Data.FingerTree.View       ℳ
open import Data.FingerTree.Split      ℳ
open import Data.FingerTree.Measures   ℳ
