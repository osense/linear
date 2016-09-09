module BCI.Combinators.Definition where
open import Common

-- BCI "linear" typed combinator calculus.


data ★ : Set where
  ι : ★
  _⊳_ : ★ → ★ → ★
infixr 10 _⊳_

-- Context as a list of named assumptions.
Cx : Set
Cx = List (Atom × ★)

data _⊢_ (Γ : Cx) : ★ → Set where
  id  : ∀ {α a}   → (a ﹕ α) ∈ Γ → Γ ⊢ α
  app : ∀ {α β}   → Γ ⊢ α ⊳ β → Γ ⊢ α → Γ ⊢ β
  B   : ∀ {α β γ} → Γ ⊢ (β ⊳ γ) ⊳ (α ⊳ β) ⊳ (α ⊳ γ)
  C   : ∀ {α β γ} → Γ ⊢ (α ⊳ (β ⊳ γ)) ⊳ (β ⊳ (α ⊳ γ))
  I   : ∀ {α}     → Γ ⊢ α ⊳ α
infix 1 _⊢_
