module Lambda.Language where

open import Data.List
open import Data.Nat

data λ-type : Set where
  _λ→_ : λ-type → λ-type → λ-type
infixr 0 _λ→_

λ-context = List λ-type

data _∈_ (τ : λ-type) : λ-context → Set where
  one  : ∀ {Γ} → τ ∈ (τ ∷ Γ)
  succ : ∀ {Γ τ'} → τ ∈ Γ → τ ∈ (τ' ∷ Γ)

two : ∀ {τ₁ Γ τ₂} → τ₁ ∈ (τ₂ ∷ τ₁ ∷ Γ)
two = succ one

three : ∀ {τ₁ Γ τ₂ τ₃} → τ₁ ∈ (τ₃ ∷ τ₂ ∷ τ₁ ∷ Γ)
three = succ two

four : ∀ {τ₁ Γ τ₂ τ₃ τ₄} → τ₁ ∈ (τ₄ ∷ τ₃ ∷ τ₂ ∷ τ₁ ∷ Γ)
four = succ three

data λ-program : λ-context → λ-type → Set where
  var : ∀ {Γ τ    } → τ ∈ Γ                                   → λ-program Γ τ
  lam : ∀ {Γ τ₁ τ₂} → λ-program (τ₁ ∷ Γ) τ₂                   → λ-program Γ (τ₁ λ→ τ₂)
  _$_ : ∀ {Γ τ₁ τ₂} → λ-program Γ (τ₁ λ→ τ₂) → λ-program Γ τ₁ → λ-program Γ τ₂
infixl 0 _$_
