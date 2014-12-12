module Lambda.Combinators where

open import Lambda.Language

id : ∀ {Γ τ} → λ-program Γ (τ λ→ τ)
id = lam (var one)

k : ∀ {Γ τ₁ τ₂} → λ-program Γ (τ₁ λ→ τ₂ λ→ τ₁)
k = lam (lam (var two))

s : ∀ {Γ τ₁ τ₂ τ₃} → λ-program Γ ((τ₃ λ→ τ₂ λ→ τ₁) λ→ (τ₃ λ→ τ₂) λ→ τ₃ λ→ τ₁)
s = lam (lam (lam ((var three $ var one) $ (var two $ var one))))
