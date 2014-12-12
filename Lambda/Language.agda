module Lambda.Language where

open import Data.List
open import Data.Nat

data λ-type : Set where
  λℕ   : λ-type
  _λ→_ : λ-type → λ-type → λ-type

λ-context = List λ-type

data _∈_ (t : λ-type) : λ-context → Set where
  ∈-zero : ∀ {ts} → t ∈ (t ∷ ts)
  ∈-suc  : ∀ {ts t'} → t ∈ ts → t ∈ (t' ∷ ts)

data λ-program : λ-context → λ-type → Set where
  lit : ∀ Γ → ℕ → λ-program Γ λℕ
  var : ∀ Γ τ → τ ∈ Γ → λ-program Γ τ
  lam : ∀ Γ τ₁ τ₂ → λ-program (τ₁ ∷ Γ) τ₂ → λ-program Γ (τ₁ λ→ τ₂)
  app : ∀ Γ τ₁ τ₂ → λ-program Γ (τ₁ λ→ τ₂) → λ-program Γ τ₁ → λ-program Γ τ₂
