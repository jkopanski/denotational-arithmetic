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
  using (Natural)

LNat : Set ℓ
LNat = Lift ℓ Nat.ℕ

module natural-function-instances where instance
  natural : Natural (Set ℓ)
  natural = record { ℕ = LNat }

  open import Felix.Bundles.Raw
    using (Magma)

  +-magma : Magma _⇾_
  +-magma = record { ⟨∙⟩ = lift₂ Nat._+_ }

  *-magma : Magma _⇾_
  *-magma = record { ⟨∙⟩ = lift₂ Nat._*_ }
