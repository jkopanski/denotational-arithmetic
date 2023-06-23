{-# OPTIONS --safe --without-K #-}

open import Level using (Level; Lift; 0ℓ)

module Felix.Number.Function (ℓ : Level) where

open import Data.Nat
  as Nat
open import Data.Integer
  as Int
open import Data.Rational
  as R
open import Felix.Instances.Function ℓ
  as F using (_⇾_)
open import Felix.Instances.Function.Lift 0ℓ ℓ
  using (lift₂)

open import Felix.Number
  using (Natural; Integer; Rational)

LNat : Set ℓ
LNat = Lift ℓ Nat.ℕ

LInt : Set ℓ
LInt = Lift ℓ Int.ℤ

LRational : Set ℓ
LRational = Lift ℓ R.ℚ

module natural-function-instances where instance
  natural : Natural (Set ℓ)
  natural = record { ℕ = LNat }

  open import Felix.Structures.Magma (Natural.ℕ natural)

  addition : Magma _⇾_
  addition = record { ∙ = lift₂ (Nat._+_) }

  multiplication : Magma _⇾_
  multiplication = record { ∙ = lift₂ Nat._*_ }

module integer-function-instances where instance
  integer : Integer (Set ℓ)
  integer = record { ℤ = LInt }

  open import Felix.Structures.Magma (Integer.ℤ integer)

  addition : Magma _⇾_
  addition = record { ∙ = lift₂ (Int._+_) }

  multiplication : Magma _⇾_
  multiplication = record { ∙ = lift₂ Int._*_ }

module rational-function-instances where instance
  rational : Rational (Set ℓ)
  rational = record { ℚ = LRational }

  open import Felix.Structures.Magma (Rational.ℚ rational)

  addition : Magma _⇾_
  addition = record { ∙ = lift₂ (R._+_) }

  multiplication : Magma _⇾_
  multiplication = record { ∙ = lift₂ R._*_ }
