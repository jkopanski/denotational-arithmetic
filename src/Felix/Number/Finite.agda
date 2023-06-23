{-# OPTIONS --safe --without-K #-}

open import Level
  using (Level; Lift; lift; lower; 0ℓ)
  renaming (suc to lsuc)

module Felix.Number.Finite (ℓ : Level) where

open import Data.Product
  using (_,_)
open import Data.Nat
  as Nat
  using (_∸_; _≤_; _%_; suc)
open import Data.Nat.Properties
  using (_<?_; _≤?_; <⇒≤; 0<1+n)
open import Data.Nat.DivMod
  using (m%n<n)
open import Data.Fin
  as Fin
  using (Fin)
open import Data.Fin.Patterns
  using (0F; 1F)
open import Function
  using (_∘_; case_of_)
open import Relation.Nullary.Decidable
  using (yes; no)

-- 0ℓ for now
open import Felix.Instances.Function 0ℓ
  using (_⇾_; module →-raw-instances)
open import Felix.Homomorphism
  using (Homomorphismₒ; id-Hₒ; Equivalent; Fₒ)
open import Felix.Number
  using (Natural; ℕ)
open import Felix.Number.Function 0ℓ
  using (module natural-function-instances; LNat)
open import Felix.Number.Homomorphism
  using ( NaturalH; β; β⁻¹
        ; StrongNaturalH; β∘β⁻¹; β⁻¹∘β
        )

open import Felix.Subcategory.Object Nat.ℕ _⇾_ public

open import Relation.Binary.PropositionalEquality
  using (_≡_)

-- defined in Felix.Subcategory.Object
-- infix 0 _⇨_
-- record _⇨_ (m n : Nat.ℕ) : Set where
--   constructor mk𝔽
--   field
--     f : Fin m → Fin n

module finite-number-instances (max : Nat.ℕ) where
  open natural-function-instances
    renaming (natural to natℓ)

  private
    betaInv : Fin (suc max) → LNat
    betaInv = lift ∘ Fin.toℕ

    overflow : LNat → Fin (suc max)
    overflow (lift n)
      with n % suc max | m%n<n n (suc max)
    ...  | rem         | rem<smax  = Fin.fromℕ< rem<smax

    saturation : LNat → Fin (suc max)
    saturation (lift n)
      with n <? suc max
    ...  | yes n<smax = Fin.fromℕ< n<smax
    ...  | no  n≮smax = Fin.fromℕ max

  instance
    Hₒ : Homomorphismₒ Nat.ℕ Set
    Hₒ = record { Fₒ = Fin ∘ suc }

    natural : Natural Nat.ℕ
    natural = record { ℕ = max }

    overflowH : NaturalH Nat.ℕ _⇾_
    overflowH = record
      { β = overflow
      ; β⁻¹ = betaInv
      }

    saturationH : NaturalH Nat.ℕ _⇾_
    saturationH = record
      { β = saturation
      ; β⁻¹ = betaInv
      }
