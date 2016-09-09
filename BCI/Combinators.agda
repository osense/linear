module BCI.Combinators where
open import Common

-- BCI "linear" typed combinator calculus.


data ★ : Set where
  ι : ★
  _⊳_ : ★ → ★ → ★
infixr 10 _⊳_

Cx : Set
Cx = List ★

data _⊢_ (Γ : Cx) : ★ → Set where
  id  : ∀ {α}     → α ∈ Γ → Γ ⊢ α
  app : ∀ {α β}   → Γ ⊢ α ⊳ β → Γ ⊢ α → Γ ⊢ β
  B   : ∀ {α β γ} → Γ ⊢ (β ⊳ γ) ⊳ (α ⊳ β) ⊳ (α ⊳ γ)
  C   : ∀ {α β γ} → Γ ⊢ (α ⊳ (β ⊳ γ)) ⊳ (β ⊳ (α ⊳ γ))
  I   : ∀ {α}     → Γ ⊢ α ⊳ α
infix 1 _⊢_


module AgdaSemantics where
  open import Data.Nat using (ℕ)
  open import Data.Unit using (⊤)
  open import Data.Product using (_×_; proj₁; proj₂)

  ⟦_⟧★ : ★ → Set
  ⟦ ι ⟧★       = ℕ
  ⟦ t₁ ⊳ t₂ ⟧★ = ⟦ t₁ ⟧★ → ⟦ t₂ ⟧★

  ⟦_⟧C : Cx → Set
  ⟦ ∅ ⟧C     = ⊤
  ⟦ c , t ⟧C = ⟦ c ⟧C × ⟦ t ⟧★

  ⟦_⟧ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧C → ⟦ α ⟧★
  ⟦ id head ⟧ c    = proj₂ c
  ⟦ id (tail x) ⟧ c = ⟦ id x ⟧ (proj₁ c)
  ⟦ app f x ⟧ c    = (⟦ f ⟧ c) (⟦ x ⟧ c)
  ⟦ B ⟧ c          = λ x y z → x (y z)
  ⟦ C ⟧ c          = λ x y z → x z y
  ⟦ I ⟧ c          = λ x → x
