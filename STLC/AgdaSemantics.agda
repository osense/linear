module STLC.AgdaSemantics where
open import Common
open import STLC.Definition
open import Data.Nat using (ℕ)

-- Conversion of λ terms to Agda.


-- Semantics of STLC types.
⟦_⟧★ : ★ → Set
⟦ ι ⟧★       = ℕ
⟦ t₁ ⊳ t₂ ⟧★ = ⟦ t₁ ⟧★ → ⟦ t₂ ⟧★

-- Semantics of contexts.
⟦_⟧C : Cx → Set
⟦ ∅ ⟧C     = ⊤
⟦ c , t ⟧C = ⟦ c ⟧C × ⟦ π₂ t ⟧★

-- Semantics of terms.
⟦_⟧ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧C → ⟦ α ⟧★
⟦ var head ⟧ c     = π₂ c
⟦ var (tail x) ⟧ c = ⟦ var x ⟧ (π₁ c)
⟦ ƛ x ↦ M ⟧ c      = λ a → ⟦ M ⟧ ⟨ c , a ⟩
⟦ f ⋅ x ⟧ c        = (⟦ f ⟧ c) (⟦ x ⟧ c)
