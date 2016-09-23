module IPC.Transl where
open import Common
open import IPC
open import STLC

-- Translations between structural IPC and STLC.


ItoS : ∀ {Γ α} → Γ ⊢ⁱ α → Γ ⊢ˢ α
ItoS assumpⁱ               = varˢ zero
ItoS (weakenⁱ t)           = weakenˢ (ItoS t) (skip stop)
ItoS (contractⁱ t)         = contractˢ (ItoS t)
ItoS (exchangeⁱ {Γ₁} t)    = exchange⧺ˢ {Γ₁} (ItoS t)
ItoS (dedⁱ t)              = ƛˢ (ItoS t)
ItoS (mpⁱ {Γ₁} {Γ₂} t₁ t₂) = (weakenˢ (ItoS t₁) (⧺-⊆₁ {L₂ = Γ₂})) ⋅ˢ (weakenˢ (ItoS t₂) (⧺-⊆₂ {L₁ = Γ₁}))


StoI : ∀ {Γ α} → Γ ⊢ˢ α → Γ ⊢ⁱ α
StoI (varˢ zero)    = mono⊢ⁱ assumpⁱ (keep ⊆-∅)
StoI (varˢ (suc x)) = weakenⁱ (StoI (varˢ x))
StoI (ƛˢ t)         = dedⁱ (StoI t)
StoI (t₁ ⋅ˢ t₂)     = contractCxⁱ (mpⁱ (StoI t₁) (StoI t₂))
