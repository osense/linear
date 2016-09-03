module STLC where
open import Common

-- Simply typed λ calculus.


data ★ : Set where
  ι : ★
  _⊳_ : ★ → ★ → ★
infixr 10 _⊳_

Cx : Set
Cx = List ★

data _⊢_ (Γ : Cx) : ★ → Set where
  var : ∀ {α}     → α ∈ Γ → Γ ⊢ α
  lam : ∀ {α β}   → Γ , α ⊢ β → Γ ⊢ α ⊳ β
  app : ∀ {α β}   → Γ ⊢ α ⊳ β → Γ ⊢ α → Γ ⊢ β
infix 1 _⊢_


module AgdaSemantics where
  open import Data.Nat using (ℕ)
  open import Data.Unit using (⊤)
  open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _⹁_)

  ⟦_⟧★ : ★ → Set
  ⟦ ι ⟧★       = ℕ
  ⟦ t₁ ⊳ t₂ ⟧★ = ⟦ t₁ ⟧★ → ⟦ t₂ ⟧★

  ⟦_⟧C : Cx → Set
  ⟦ • ⟧C     = ⊤
  ⟦ c , t ⟧C = ⟦ c ⟧C × ⟦ t ⟧★

  ⟦_⟧ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧C → ⟦ α ⟧★
  ⟦ var zero ⟧ c    = proj₂ c
  ⟦ var (suc x) ⟧ c = ⟦ var x ⟧ (proj₁ c)
  ⟦ lam t ⟧ c       = λ a → ⟦ t ⟧ (c ⹁ a)
  ⟦ app f x ⟧ c     = (⟦ f ⟧ c) (⟦ x ⟧ c)
