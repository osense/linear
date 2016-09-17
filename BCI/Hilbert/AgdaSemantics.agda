module BCI.Hilbert.AgdaSemantics where
open import Common
open import BCI.Hilbert.Definition



record Valuation : Set₁ where
  field
    _⊩ᵃ_   : Cx → Atom → Set
open Valuation {{…}} public

module _ {{V : Valuation}} where
  _⊩_ : Cx → Form → Set
  Γ ⊩ var x     = Γ ⊩ᵃ x
  Γ ⊩ (f₁ ⇒ f₂) = (Γ ⊩ f₁) → (Γ ⊩ f₂)
  infix 5 _⊩_

  _⊩★_ : Cx → Cx → Set
  Γ ⊩★ ∅        = ⊤
  Γ ⊩★ (Γ' , A) = (Γ ⊩★ Γ') × (Γ ⊩ A)
  infix 5 _⊩★_


_⊨_ : Cx → Form → Set₁
Γ ⊨ f = ∀ {{V : Valuation}} {Δ} → Δ ⊩★ Γ → Δ ⊩ f

lookupᵥ : ∀ {Γ A} → A ∈ Γ → Γ ⊨ A
lookupᵥ zero γ    = π₂ γ
lookupᵥ (suc i) γ = (lookupᵥ i) (π₁ γ)

sound : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
sound (ID i) γ     = lookupᵥ i γ
sound (MP f₁ f₂) γ = (sound f₁ γ) (sound f₂ γ)
sound AB γ         = λ x y z → x (y z)
sound AC γ         = λ x y z → x z y
sound AI γ         = λ x → x
