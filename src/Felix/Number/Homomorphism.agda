{-# OPTIONS --safe --without-K #-}

module Felix.Number.Homomorphism where

open import Level
  using (Level; _⊔_)

open import Felix.Raw
  using (Category; id; _∘_)
open import Felix.Equiv
  using (Equivalent; _≈_)
open import Felix.Homomorphism
  using (Homomorphismₒ; Fₒ)
open import Felix.Number
  using ( Natural; ℕ
        ; Integer; ℤ
        ; Rational; ℚ
        )

private
  variable
    o ℓ o₁ ℓ₁ o₂ ℓ₂ : Level
    O₁ : Set o

record NaturalH
  (O₁ : Set o₁) ⦃ _ : Natural O₁ ⦄
  {O₂ : Set o₂} ⦃ _ : Natural O₂ ⦄
  (_⇨₂′_ : O₂ → O₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄
  : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β : ℕ ⇨₂ Fₒ ℕ
    β⁻¹ : Fₒ ℕ ⇨₂ ℕ

open NaturalH ⦃ … ⦄ public

record StrongNaturalH
  (O₁ : Set o₁) ⦃ _ : Natural O₁ ⦄
  {O₂ : Set o₂} ⦃ _ : Natural O₂ ⦄
  (_⇨₂′_ : O₂ → O₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄
  {q : Level} ⦃ _ : Equivalent q _⇨₂′_ ⦄
  ⦃ _ : Category _⇨₂′_ ⦄
  ⦃ naturalH : NaturalH O₁ _⇨₂′_ ⦄
  : Set (o₁ ⊔ o₂ ⊔ ℓ₂ ⊔ q) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β⁻¹∘β : β⁻¹ ∘ β ≈ id
    β∘β⁻¹ : β ∘ β⁻¹ ≈ id

open StrongNaturalH ⦃ … ⦄ public

record IntegerH
  (O₁ : Set o₁) ⦃ _ : Integer O₁ ⦄
  {O₂ : Set o₂} ⦃ _ : Integer O₂ ⦄
  (_⇨₂′_ : O₂ → O₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄
  : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β : ℤ ⇨₂ Fₒ ℤ
    β⁻¹ : Fₒ ℤ ⇨₂ ℤ

record RationalH
  (O₁ : Set o₁) ⦃ _ : Rational O₁ ⦄
  {O₂ : Set o₂} ⦃ _ : Rational O₂ ⦄
  (_⇨₂′_ : O₂ → O₂ → Set ℓ₂)
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄
  : Set (o₁ ⊔ o₂ ⊔ ℓ₂) where
  private infix 0 _⇨₂_; _⇨₂_ = _⇨₂′_
  field
    β : ℚ ⇨₂ Fₒ ℚ
    β⁻¹ : Fₒ ℚ ⇨₂ ℚ
