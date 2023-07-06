{-# OPTIONS --safe --without-K #-}

module Felix.Bundles.Raw where

open import Level
  using (_⊔_; Level)

open import Felix.Homomorphism
  using ( Equivalent; Homomorphismₒ; Homomorphism; ProductsH
        ; Fₒ; Fₘ; _≈_; μ
        )
open import Felix.Raw
  using ( Category; Cartesian; Products
        ; _∘_; _×_; _⊗_
        )

open import Felix.Number
  using (Natural; ℕ)
open import Felix.Number.Homomorphism
  using (NaturalH; β)

private
  variable
    o₁ ℓ₁ o₂ ℓ₂ : Level

record Magma
  {o} {O : Set o} ⦃ _ : Products O ⦄ ⦃ _ : Natural O ⦄
  {ℓ} (_⇨′_ : O → O → Set ℓ) : Set (o ⊔ ℓ) where
  private infix 0 _⇨_; _⇨_ = _⇨′_
  field
    ⟨∙⟩ : ℕ × ℕ ⇨ ℕ

open Magma ⦃ … ⦄ public

record MagmaH
  {O₁ : Set o₁} ⦃ _ : Products O₁ ⦄ ⦃ _ : Natural O₁ ⦄
  {O₂ : Set o₂} ⦃ _ : Products O₂ ⦄ ⦃ _ : Natural O₂ ⦄
  (_⇨₁_ : O₁ → O₁ → Set ℓ₁) ⦃ _ : Category _⇨₁_ ⦄ ⦃ _ : Cartesian _⇨₁_ ⦄
  (_⇨₂_ : O₂ → O₂ → Set ℓ₂) ⦃ _ : Category _⇨₂_ ⦄ ⦃ _ : Cartesian _⇨₂_ ⦄
  {q} ⦃ _ : Equivalent q _⇨₂_ ⦄
  ⦃ M₁ : Magma _⇨₁_ ⦄ ⦃ M₂ : Magma _⇨₂_ ⦄
  ⦃ Hₒ : Homomorphismₒ O₁ O₂ ⦄ ⦃ H : Homomorphism _⇨₁_ _⇨₂_ ⦄
  ⦃ nH : NaturalH O₁ _⇨₂_ ⦄
  ⦃ pH : ProductsH O₁ _⇨₂_ ⦄ : Set (o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ q)
  where
  field
    F-⟨∙⟩ : Fₘ ⟨∙⟩ ∘ μ ∘ (β ⊗ β) ≈ β ∘ ⟨∙⟩
