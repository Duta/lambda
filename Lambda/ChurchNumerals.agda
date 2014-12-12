module Lambda.ChurchNumerals where

open import Lambda.Language

Cℕ : λ-type → λ-type
Cℕ τ = (τ λ→ τ) λ→ τ λ→ τ

zero : ∀ {Γ τ} → λ-program Γ (Cℕ τ)
zero = lam (var one)

suc : ∀ {Γ τ} → λ-program Γ (Cℕ τ λ→ Cℕ τ)
suc = lam (lam (lam (var two $ (var three $ var two $ var one))))
