module BCI.Combinators.Definition where
open import Common
open import STLC using (★; ι; _⊳_; Cx) public

-- BCI "linear" typed combinator calculus.


data _⊢_ (Γ : Cx) : ★ → Set where
  id  : ∀ {α}     → α ∈ Γ → Γ ⊢ α
  app : ∀ {α β}   → Γ ⊢ α ⊳ β → Γ ⊢ α → Γ ⊢ β
  B   : ∀ {α β γ} → Γ ⊢ (β ⊳ γ) ⊳ (α ⊳ β) ⊳ (α ⊳ γ)
  C   : ∀ {α β γ} → Γ ⊢ (α ⊳ (β ⊳ γ)) ⊳ (β ⊳ (α ⊳ γ))
  I   : ∀ {α}     → Γ ⊢ α ⊳ α
infix 1 _⊢_

weaken⊢ : ∀ {Γ Δ α} → Γ ⊢ α → Γ ⊆ Δ → Δ ⊢ α
weaken⊢ (id x) γ      = id (mono∈ γ x)
weaken⊢ (app t₁ t₂) γ = app (weaken⊢ t₁ γ) (weaken⊢ t₂ γ)
weaken⊢ B _           = B
weaken⊢ C _           = C
weaken⊢ I _           = I

-- Closed terms.
Closed : ★ → Set
Closed t = ∅ ⊢ t
