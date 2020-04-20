module naryapplicative where

open import Agda.Primitive

it : ∀ { ℓ } { a : Set ℓ } ⦃ _ : a ⦄ → a
it ⦃ x ⦄ = x

module Functor
  where

  record functor { κ ℓ } (f : Set κ → Set ℓ) : Set (lsuc κ ⊔ ℓ)
    where
    field
      _<$>_ : ∀ { a b } → (a → b) → f a → f b
    infixl 4 _<$>_


open Functor
open functor ⦃ ... ⦄

module Applicative
  where

  record applicative { κ ℓ } (f : Set κ → Set ℓ) : Set (lsuc κ ⊔ ℓ)
    where
    field
      ⦃ functorF ⦄ : functor f
      pure : ∀ { a } → a → f a
      _<*>_ : ∀ { a b } → f (a → b) → f a → f b
    infixl 4 _<*>_

  open applicative ⦃ ... ⦄

  lift2 : ∀ { κ ℓ } { f : Set κ → Set ℓ } { a b c : Set κ } ⦃ _ : applicative f ⦄ → (a → b → c) → f a → f b → f c
  lift2 f x y = f <$> x <*> y

open Applicative
open applicative ⦃ ... ⦄

module Nat
  where

  data nat : Set
    where
    zero : nat
    succ : nat → nat

  {-# BUILTIN NATURAL nat #-}

  _+_ : nat → nat → nat
  0 + x = x
  succ x + y = succ (x + y)

open Nat

module Bool
  where

  data bool : Set
    where
    true : bool
    false : bool

open Bool

module Vec
  where

  data vec { ℓ } : nat → Set ℓ → Set ℓ
    where
    [] : ∀ { a } → vec 0 a
    _∷_ : ∀ { n } { a } → a → vec n a → vec (succ n) a

  infixr 5 _∷_

  replicate : ∀ { ℓ } { a : Set ℓ } → (n : nat) → a → vec n a
  replicate zero     _ = []
  replicate (succ n) a = a ∷ replicate n a

  instance
    vf : ∀ { ℓ } { n } → functor { ℓ } (vec n)
    vf = record
      { _<$>_ = λ
          { _ []       → []
          ; f (x ∷ xs) → f x ∷ (f <$> xs)
          }
      }

    -- vf { n = zero } = record { _<$>_ = λ { _ [] → [] } }
    -- vf { n = succ n′ } = record { _<$>_ = λ { f (x ∷ xs) → f x ∷ (f <$> xs) } }

    va : ∀ { ℓ } { n } → applicative { ℓ } (vec n)
    va { n = n } = record
      { pure = replicate n
      ; _<*>_ = λ
          { []       []       → []
          ; (f ∷ fs) (x ∷ xs) → f x ∷ (fs <*> xs)
          }
      }

    -- va { ℓ } { n = zero } = record { pure = λ _ → []; _<*>_ = λ { [] [] → [] } }
    -- va { ℓ } { n = succ n′ } = record { pure = λ a → a ∷ replicate n′ a; _<*>_ = λ { (f ∷ fs) (x ∷ xs) → f x ∷ (fs <*> xs) } }

open Vec

module Function
  where
  nary : ∀ { ℓ } { n } → vec n (Set ℓ) → Set ℓ → Set ℓ
  nary [] r = r
  nary (x ∷ xs) r = x → nary xs r

open Function

module Exists
  where

  data Σ { κ ℓ } { a : Set κ } (f : a → Set ℓ) : Set (κ ⊔ ℓ)
    where
    ∃ : ∀ { x } → f x → Σ f

open Exists

module HList
  where

  data hlist { ℓ } : ∀ { n } → vec n (Set ℓ) → Set ℓ
    where
    ∎ : hlist []
    _,_ : ∀ { n } { x : Set ℓ } { xs : vec n (Set ℓ) } → x → hlist xs → hlist (x ∷ xs)

  infixr 2 _,_

  applyN : ∀ { n } { xs : vec n Set } { r } → nary xs r → hlist xs → r
  applyN {zero}   {[]}     v _        = v
  applyN {succ n} {x ∷ xs} f (v , vs) = applyN (f v) vs

  liftN :
    ∀ { n : nat } { xs : vec n Set } { r : Set } { f : Set → Set } ⦃ _ : applicative f ⦄ →
    nary xs r → hlist (replicate n f <*> xs) → f r
  liftN {zero}   {[]}     r _        = pure r
  liftN {succ n} {x ∷ xs} f (v , vs) = ?

open HList

module List
  where

  list : ∀ { ℓ } → Set ℓ → Set ℓ
  list a = Σ (λ n → vec n a)

module FreeApplicative
  where

  data free (f : Set → Set) (a : Set) : Set₁
    where
    mkFree : ∀ { n } { xs : vec n Set } → nary xs a → hlist (replicate n f <*> xs) → free f a

  _<‥*‥>_ : ∀ { n } { f } { xs } { a } → nary xs a → hlist (replicate n f <*> xs) → free f a
  _<‥*‥>_ = mkFree

  test : free (vec 3) bool
  test = and <‥*‥> (v1 , v2 , ∎)
    where
    and : bool → bool → bool
    and true x = x
    and _    _ = false

    v1 : vec 3 bool
    v1 = true ∷ false ∷ true ∷ []

    v2 : vec 3 bool
    v2 = false ∷ true ∷ true ∷ []

  interpret : ∀ { f : Set → Set } { a : Set } ⦃ _ : applicative f ⦄ → free f a → f a
  interpret (mkFree {n} {xs} f vs) = liftN {n = n} {xs = xs} f vs

open Applicative
