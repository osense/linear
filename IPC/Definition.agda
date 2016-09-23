module IPC.Definition where
open import Common

-- Implicational fragment of IPC with explicit structural rules.


Cx : Set
Cx = List ★

data _⊢_ : Cx → ★ → Set where
  assump   : ∀ {α}         → [ α ] ⊢ α
  weaken   : ∀ {Γ γ α}     → Γ ⊢ α         → Γ , γ ⊢ α
  contract : ∀ {Γ γ α}     → Γ , γ , γ ⊢ α → Γ , γ ⊢ α
  exchange : ∀ {Γ₁ Γ₂ α}   → Γ₁ ⁏ Γ₂ ⊢ α   → Γ₂ ⁏ Γ₁ ⊢ α
  ded      : ∀ {Γ α β}     → Γ , α ⊢ β     → Γ ⊢ α ⊳ β
  mp       : ∀ {Γ₁ Γ₂ α β} → Γ₁ ⊢ α ⊳ β    → Γ₂ ⊢ α      → Γ₁ ⁏ Γ₂ ⊢ β
infix 5 _⊢_


weakenCx₁ : ∀ {Γ₁ Γ₂ α} → Γ₁ ⊢ α → Γ₁ ⁏ Γ₂ ⊢ α
weakenCx₁ {Γ₂ = ∅} t      = t
weakenCx₁ {Γ₂ = xs , x} t = weaken (weakenCx₁ {Γ₂ = xs} t)

weakenCx₂ : ∀ {Γ₁ Γ₂ α} → Γ₂ ⊢ α → Γ₁ ⁏ Γ₂ ⊢ α
weakenCx₂ {Γ₁} {Γ₂} = (exchange {Γ₂ = Γ₁}) ∘ (weakenCx₁ {Γ₂ = Γ₁})

assumpCx : ∀ {Γ α} → Γ , α ⊢ α
assumpCx = weakenCx₂ (assump)

-- Detachment theorem.
det : ∀ {Γ α β} → Γ ⊢ α ⊳ β → Γ , α ⊢ β
det {Γ} {α} {β} t = begin[ t ]
  Γ ⊢ α ⊳ β     ↝[ weaken {γ = α} ]
  Γ , α ⊢ α ⊳ β ↝[ (λ this → mp this assump) ]
  Γ , α , α ⊢ β ↝[ contract ]
  Γ , α ⊢ β ∎

-- Contraction for entire contexts.
contractCx : ∀ {Γ α} → Γ ⁏ Γ ⊢ α → Γ ⊢ α
contractCx {∅} t          = t
contractCx {xs , x} {α} t = begin[ t ]
  xs , x ⁏ xs , x ⊢ α ↝[ ded ]
  xs , x ⁏ xs ⊢ x ⊳ α ↝[ exchange {Γ₁ = xs , x} {Γ₂ = xs} ]
  xs ⁏ xs , x ⊢ x ⊳ α ↝[ det ]
  xs ⁏ xs , x , x ⊢ α ↝[ contract ]
  xs ⁏ xs , x ⊢ α     ↝[ ded ]
  xs ⁏ xs ⊢ x ⊳ α     ↝[ contractCx {Γ = xs} ]
  xs ⊢ x ⊳ α          ↝[ det ]
  xs , x ⊢ α ∎


-- Monotonicity of ⊢ with respect to context inclusion.
mono⊢ : ∀ {Γ Δ α} → Γ ⊢ α → Γ ⊆ Δ → Δ ⊢ α
mono⊢ t stop     = t
mono⊢ t (skip γ) = weaken (mono⊢ t γ)
mono⊢ t (keep γ) = det (mono⊢ (ded t) γ)


