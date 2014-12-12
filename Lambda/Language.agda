module Lambda.Language where

open import Data.List
open import Data.Nat

data λ-type : Set where
  λℕ   : λ-type
  _λ→_ : λ-type → λ-type → λ-type
infixr 0 _λ→_

λ-context = List λ-type

data _∈_ (τ : λ-type) : λ-context → Set where
  one  : ∀ {Γ} → τ ∈ (τ ∷ Γ)
  succ : ∀ {Γ τ'} → τ ∈ Γ → τ ∈ (τ' ∷ Γ)

data λ-program : λ-context → λ-type → Set where
  lit : ∀ {Γ      } → ℕ                                       → λ-program Γ λℕ
  var : ∀ {Γ τ    } → τ ∈ Γ                                   → λ-program Γ τ
  lam : ∀ {Γ τ₁ τ₂} → λ-program (τ₁ ∷ Γ) τ₂                   → λ-program Γ (τ₁ λ→ τ₂)
  app : ∀ {Γ τ₁ τ₂} → λ-program Γ (τ₁ λ→ τ₂) → λ-program Γ τ₁ → λ-program Γ τ₂

id : ∀ Γ τ → λ-program Γ (τ λ→ τ)
id Γ τ = lam (var one)

k : ∀ Γ τ₁ τ₂ → λ-program Γ (τ₁ λ→ τ₂ λ→ τ₁)
k Γ τ₁ τ₂ = lam (lam (var (succ one)))

s : ∀ Γ τ₁ τ₂ τ₃ → λ-program Γ ((τ₁ λ→ τ₂ λ→ τ₃) λ→ (τ₁ λ→ τ₂) λ→ τ₁ λ→ τ₃)
s Γ τ₁ τ₂ τ₃ = {!!}
