module Lambda.Combinators where

--open import Data.Product
open import Lambda.Language

id : ∀ {Γ τ} → λ-program Γ (τ λ→ τ)
id = lam (var one)

k : ∀ {Γ τ₁ τ₂} → λ-program Γ (τ₁ λ→ τ₂ λ→ τ₁)
k = lam (lam (var two))

s : ∀ {Γ τ₁ τ₂ τ₃} → λ-program Γ ((τ₃ λ→ τ₂ λ→ τ₁) λ→ (τ₃ λ→ τ₂) λ→ τ₃ λ→ τ₁)
s = lam (lam (lam ((var three $ var one) $ (var two $ var one))))
{- Definition of polynomial functors (and Fix) thanks to Ulf Norell & James Chapman
   http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf
data Functor : Set₁ where
  |Id|  :                     Functor
  |K|   : Set               → Functor
  _|+|_ : Functor → Functor → Functor
  _|×|_ : Functor → Functor → Functor

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

[_] : Functor → Set → Set
[ |Id|    ] X = X
[ |K| A   ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |×| G ] X = [ F ] X × [ G ] X

data Fix (f : Functor) : Set where
  Fix' : [ f ] (Fix f) → Fix f
-}
--y : ∀ {Γ τ} → λ-program Γ ((τ λ→ τ) λ→ τ)
--y = lam ((lam (var two $ (var one $ var one))) $ lam (var two $ (var one $ var one)))
