{-# OPTIONS --safe --without-K #-}

module Felix.Number where

record Natural {o} (O : Set o) : Set o where
  field ℕ : O
open Natural ⦃ … ⦄ public

record Integer {o} (O : Set o) : Set o where
  field ℤ : O
open Integer ⦃ … ⦄ public

record Rational {o} (O : Set o) : Set o where
  field ℚ : O
open Rational ⦃ … ⦄ public
