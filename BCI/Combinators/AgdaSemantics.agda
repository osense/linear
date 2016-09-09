module BCI.Combinators.AgdaSemantics where
open import Common
open import BCI.Combinators.Definition
open import Data.Nat using (ℕ)

-- Agda semantics for the BCI combinator calculus


⟦_⟧★ : ★ → Set
⟦ ι ⟧★       = ℕ
⟦ t₁ ⊳ t₂ ⟧★ = ⟦ t₁ ⟧★ → ⟦ t₂ ⟧★

⟦_⟧C : Cx → Set
⟦ ∅ ⟧C     = ⊤
⟦ c , t ⟧C = ⟦ c ⟧C × ⟦ π₂ t ⟧★

⟦_⟧ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧C → ⟦ α ⟧★
⟦ id head ⟧ c    = π₂ c
⟦ id (tail x) ⟧ c = ⟦ id x ⟧ (π₁ c)
⟦ app f x ⟧ c    = (⟦ f ⟧ c) (⟦ x ⟧ c)
⟦ B ⟧ c          = λ x y z → x (y z)
⟦ C ⟧ c          = λ x y z → x z y
⟦ I ⟧ c          = λ x → x
