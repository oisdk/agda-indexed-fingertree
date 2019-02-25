{-# OPTIONS --without-K --safe #-}

open import Data.FingerTree.Preamble

module Data.FingerTree
  {c m a}
  (imports : Imports c m a)
  where

open Imports imports

--
--    ╭──┬─────◯ ◯─────┬──┬──╮
--    │  │     │ │     │  │  │
--    t  h     │ │     r  e  e
--   ╭──────┬──◯ ◯────┬─────────╮
--   │      │  │ │    │         │
--   │      │  ╰◯╯    │         │
-- ╭─◯─╮  ╭─◯─╮   ╭───◯───╮   ╭─◯─╮
-- │   │  │   │   │   │   │   │   │
-- i   s  i   s   n   o   t   a   t
--
-- As I have talked about [previously](/posts/2019-01-15-binomial-urn.html), a
-- large class of divide-and conquer algorithms rely on "good" partitioning for the
-- divide step. If you then want to make the algorithms incremental, you keep all
-- of those partitions (with their summaries) in some "good" arrangement
-- [@mu_queueing_2016].  Several common data structures are designed around this
-- principle: binomial heaps, for instance, store partitions of size $2^n$.
-- Different ways of storing partitions favours different use cases: switch from a
-- binomial heap to a skew binomial, for instance, and you get constant-time
-- `cons`.

-- The standout data structure in this area is Hinze and Paterson's
-- [@Hinze-Paterson:FingerTree]. It caches summaries in a pretty amazing way,
-- allowing for (amortised) 𝒪(1) cons and snoc and
-- 𝒪(\log n) `split` and `append`. These features allow it to be used
-- for a huge variety of things:
-- [Data.Sequence](http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Sequence.html)
-- uses it as a random-access sequence, but it can also work as a priority queue, a
-- search tree, a priority search tree [@hinze_simple_2001], an interval tree, an
-- order statistic tree...

-- All of these applications solely rely on an underlying monoid. As a result, I
-- thought it would be a great data structure to implement in Agda, so that you'd
-- get all of the other data structures with minimal effort [similar thinking
-- motivated a Coq implementation; @sozeau_program-ing_2007].

open import Data.FingerTree.Structures ℳ

-- ┌──────────────────────────────────────────────────────────────────────────────┐
-- │                                                                              │
-- │                    ____                                __                    │
-- │                   / ___|  ___ ___  _ __   ___    ___  / _|                   │
-- │                   \___ \ / __/ _ \| '_ \ / _ \  / _ \| |_                    │
-- │                    ___) | (_| (_) | |_) |  __/ | (_) |  _|                   │
-- │                   |____/ \___\___/| .__/ \___|  \___/|_|                     │
-- │                                   |_|                                        │
-- │             __     __        _  __ _           _   _                         │
-- │             \ \   / /__ _ __(_)/ _(_) ___ __ _| |_(_) ___  _ __              │
-- │              \ \ / / _ \ '__| | |_| |/ __/ _` | __| |/ _ \| '_ \             │
-- │               \ V /  __/ |  | |  _| | (_| (_| | |_| | (_) | | | |            │
-- │                \_/ \___|_|  |_|_| |_|\___\__,_|\__|_|\___/|_| |_|            │
-- │                                                                              │
-- └──────────────────────────────────────────────────────────────────────────────┘
-- There would be no real point to implementing a finger tree in Agda if we didn't
-- also prove some things about it. The scope of the proofs I've done so far are
-- intrinsic proofs of the summaries in the tree. In other words, the type of
-- `cons` is as follows:
open import Data.FingerTree.Cons ℳ using (_◂_)

_ : (x : A) → (xs : Tree A) → μ⟨ Tree A ⟩≈ (μ x ∙ μ xs)
_ = _◂_
-- This is enough to prove things about the derived data structures (like the
-- correctness of sorting if it's used as a priority queue), but it's worth
-- pointing out what I *haven't* proved (yet):
--
--   1. Invariants on the structure ("safe" and "unsafe" digits and so on).
--   2. The time complexity or performance of any operations.
--
-- To be honest, I'm not even sure that my current implementation is correct in
-- these regards! I'll probably have a go at proving them in the future [possibly
-- using @danielsson_lightweight_2008].
-- ┌──────────────────────────────────────────────────────────────────────────────┐
-- │                                                                              │
-- │           __  __                   _     _                       _           │
-- │          |  \/  | ___  _ __   ___ (_) __| |___    __ _ _ __   __| |          │
-- │          | |\/| |/ _ \| '_ \ / _ \| |/ _` / __|  / _` | '_ \ / _` |          │
-- │          | |  | | (_) | | | | (_) | | (_| \__ \ | (_| | | | | (_| |          │
-- │          |_|  |_|\___/|_| |_|\___/|_|\__,_|___/  \__,_|_| |_|\__,_|          │
-- │                                                                              │
-- │                         ____                   __                            │
-- │                        |  _ \ _ __ ___   ___  / _|___                        │
-- │                        | |_) | '__/ _ \ / _ \| |_/ __|                       │
-- │                        |  __/| | | (_) | (_) |  _\__ \                       │
-- │                        |_|   |_|  \___/ \___/|_| |___/                       │
-- │                                                                              │
-- └──────────────────────────────────────────────────────────────────────────────┘

-- The bad news is that finger trees are a relatively complex data structure, and
-- we're going to need a *lot* of proofs to write a verified version. The good news
-- is that monoids (in contrast to rings) are extremely easy to prove
-- automatically. In this project, I used reflection to do so, but I think it
-- should be possible to do with instance resolution also.
-- ┌──────────────────────────────────────────────────────────────────────────────┐
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                   __  __                                                     │
-- │                  |  \/  | ___  __ _ ___ _   _ _ __ ___  ___                  │
-- │                  | |\/| |/ _ \/ _` / __| | | | '__/ _ \/ __|                 │
-- │                  | |  | |  __/ (_| \__ \ |_| | | |  __/\__ \                 │
-- │                  |_|  |_|\___|\__,_|___/\__,_|_|  \___||___/                 │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- └──────────────────────────────────────────────────────────────────────────────┘
--
-- First things first, we need a way to talk about the summaries of elements we're
-- interested in. This is captured by the σ class, which has one method μ.
_ : A → 𝓡
_ = μ
-- 𝓡 is the type of the summaries, and μ means "summarise". The silly symbols
-- are used for brevity: we're going to be using this thing everywhere, so it's
-- important to keep it short. Here's an example instance for lists:
_ : (xs : List A) → μ xs ≡ foldr (_∙_ ∘ μ) ε xs
_ = λ xs → refl
-- ┌──────────────────────────────────────────────────────────────────────────────┐
-- │                                                                              │
-- │                                                                              │
-- │        __        __         _    _                        _ _   _            │
-- │        \ \      / /__  _ __| | _(_)_ __   __ _  __      _(_) |_| |__         │
-- │         \ \ /\ / / _ \| '__| |/ / | '_ \ / _` | \ \ /\ / / | __| '_ \        │
-- │          \ V  V / (_) | |  |   <| | | | | (_| |  \ V  V /| | |_| | | |       │
-- │           \_/\_/ \___/|_|  |_|\_\_|_| |_|\__, |   \_/\_/ |_|\__|_| |_|       │
-- │                                          |___/                               │
-- │                        ____       _        _     _                           │
-- │                       / ___|  ___| |_ ___ (_) __| |___                       │
-- │                       \___ \ / _ \ __/ _ \| |/ _` / __|                      │
-- │                        ___) |  __/ || (_) | | (_| \__ \                      │
-- │                       |____/ \___|\__\___/|_|\__,_|___/                      │
-- │                                                                              │
-- │                                                                              │
-- └──────────────────────────────────────────────────────────────────────────────┘

-- As I mentioned, the tree is going to be verified intrinsically. In other word
-- its type will look something like this:

SimpleTree : Set _
SimpleTree = 𝓡 → Set

-- But before running off to define that the obvious way, I should mention that I
-- made the annoying decision to use a setoid (rather than propositional equality)
-- based monoid. This means that we don't get substitution, making the obvious
-- definition untenable.

-- I figured out a solution to the problem, but I'm not sure if I'm happy with it.
-- That's actually the main motivation for writing this post: I'm curious if other
-- people have better techniques for this kind of thing.

-- To clarify: "this kind of thing" is writing intrinsic (correct-by-construction)
-- proofs when a setoid is involved. Intrinsic proofs usually lend themselves to
-- elegance: to prove that `map` preserves a vector's length, for instance,
-- basically requires no proof at all:

map : ∀ {a b n} {A : Set a} {B : Set b}
    → (A → B)
    → Vec A n
    → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- But that's because pattern matching works well with propositional equality: in
-- the first clause, `n` is set to `0` automatically. If we were working with
-- setoid equality, we'd instead maybe get a proof that `n ≈ 0`, and we'd have to
-- figure a way to work that into the types.

-- ┌──────────────────────────────────────────────────────────────────────────────┐
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                          _____ _ _                                           │
-- │                         |  ___(_) |__  _ __ ___  ___                         │
-- │                         | |_  | | '_ \| '__/ _ \/ __|                        │
-- │                         |  _| | | |_) | | |  __/\__ \                        │
-- │                         |_|   |_|_.__/|_|  \___||___/                        │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- └──────────────────────────────────────────────────────────────────────────────┘

-- The first part of the solution is to define a wrapper type which stores
-- information about the size of the thing it contains:
module Fibre where
  record ′μ⟨_⟩≈_ {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (𝓂 : 𝓡) : Set (a ⊔ c ⊔ m) where
    constructor _⇑[_]
    field
      𝓢 : Σ
      𝒻 : μ 𝓢 ≈ 𝓂

-- Technically speaking, I think this is known as a "fibre". `μ⟨ Σ ⟩≈ 𝓂` means "There
-- exists a `Σ` such that `μ Σ ≈ 𝓂`". Next, we'll need some combinators to work
-- with:

infixl 2 _≈[_]
_≈[_] : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ {x : 𝓡} → μ⟨ Σ ⟩≈ x → ∀ {y} → x ≈ y → μ⟨ Σ ⟩≈ y
𝓢 (xs ≈[ y≈z ]) = 𝓢 xs
𝒻 (xs ≈[ y≈z ]) = trans (𝒻 xs) y≈z

-- This makes it possible to "rewrite" the summary, given a proof of equivalence.

-- ┌──────────────────────────────────────────────────────────────────────────────┐
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │             ____          _   _       _        _   _                         │
-- │            |  _ \  ___   | \ | | ___ | |_ __ _| |_(_) ___  _ __              │
-- │            | | | |/ _ \  |  \| |/ _ \| __/ _` | __| |/ _ \| '_ \             │
-- │            | |_| | (_) | | |\  | (_) | || (_| | |_| | (_) | | | |            │
-- │            |____/ \___/  |_| \_|\___/ \__\__,_|\__|_|\___/|_| |_|            │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- │                                                                              │
-- └──────────────────────────────────────────────────────────────────────────────┘

-- The wrapper on its own isn't enough to save us from hundreds of lines of proofs.
-- Once you do computation on its contents, you still need to join it up with its
-- original proof of equivalence. In other words, you'll need to drill into the
-- return type of a function, find the place you used the relevant type variable,
-- and apply the relevant proof from the type above. This can really clutter
-- proofs. Instead, we can use Agda's new support for do notation to try and get a
-- cleaner notation for everything. Here's a big block of code:

infixl 2 arg-syntax
record Arg {a} (Σ : Set a) ⦃ _ : σ Σ ⦄ (𝓂 : 𝓡) (f : 𝓡 → 𝓡) : Set (m ⊔ c ⊔ a) where
  constructor arg-syntax
  field
    ⟨f⟩ : Congruent₁ f
    arg : μ⟨ Σ ⟩≈ 𝓂
open Arg

syntax arg-syntax (λ sz → e₁) xs = xs [ e₁ ⟿ sz ]

infixl 1 _>>=_
_>>=_ : ∀ {a b} {Σ₁ : Set a} {Σ₂ : Set b} ⦃ _ : σ Σ₁ ⦄ ⦃ _ : σ Σ₂ ⦄ {𝓂 f}
      → Arg Σ₁ 𝓂 f
      → ((x : Σ₁) → ⦃ x≈ : μ x ≈ 𝓂 ⦄ → μ⟨ Σ₂ ⟩≈ f (μ x))
      → μ⟨ Σ₂ ⟩≈ f 𝓂
arg-syntax cng xs >>= k = k (𝓢 xs) ⦃ 𝒻 xs ⦄ ≈[ cng (𝒻 xs) ]

listToTree : ∀ {a} {Σ : Set a} ⦃ _ : σ Σ ⦄ → (xs : List Σ) → μ⟨ Tree Σ ⟩≈ μ xs
listToTree [] = empty ⇑
listToTree (x ∷ xs) = [ ℳ ↯ ]≈ do
  ys ← listToTree xs [ μ x ∙> s ⟿ s ]
  x ◂ ys

-- The first line is the base case, nothing interesting going on there. The second
-- line begins the do-notation, but first applies `[ ℳ ↯ ]≈`: this calls the
-- automated solver. The second line makes the recursive call, and with the syntax:

-- ```agda
-- [ μ x ∙> s ⟿ s ]
-- ```

-- It tells us where the size of the bound variable will end up in the outer
-- expression.
