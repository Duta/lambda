module Lambda.ChurchNumerals where

open import Lambda.Language

-- Naturals

Cℕ : λ-type → λ-type
Cℕ τ = (τ λ→ τ) λ→ τ λ→ τ

zero : ∀ {Γ τ} → λ-program Γ (Cℕ τ)
zero = lam (var one)

suc : ∀ {Γ τ} → λ-program Γ (Cℕ τ λ→ Cℕ τ)
suc = lam (lam (lam (var two $ (var three $ var two $ var one))))

add : ∀ {Γ τ} → λ-program Γ (Cℕ τ λ→ Cℕ τ λ→ Cℕ τ)
add = lam (lam (lam (lam (var four $ var two $ (var three $ var two $ var one)))))

mul : ∀ {Γ τ} → λ-program Γ (Cℕ τ λ→ Cℕ τ λ→ Cℕ τ)
mul = lam (lam (lam (var three $ (var two $ var one))))

-- Booleans

true : ∀ {Γ τ₁ τ₂} → λ-program Γ (τ₁ λ→ τ₂ λ→ τ₁)
true = lam (lam (var two))

false : ∀ {Γ τ₁ τ₂} → λ-program Γ (τ₁ λ→ τ₂ λ→ τ₂)
false = lam (lam (var one))
