module Lambda.Language where

open import Data.Nat

data λ-kind : Set where
  ground : λ-kind
  function : λ-kind

data λ-type : λ-kind → Set where
  λℕ : λ-type ground
  _λ→_ : ∀ {k₁ k₂} → λ-type k₁ → λ-type k₂ → λ-type function

λ→agda : λ-type ground → Set
λ→agda λℕ = ℕ

data λ-program : Set where
  lit : ∀ {t} → λ→agda t → λ-program
