module STLC where
open import Common

-- Simply typed λ calculus.


data ★ : Set where
  ι : ★
  _⊳_ : ★ → ★ → ★
infixr 15 _⊳_

data Term : Set where
  var  : Atom → Term
  ƛ_↦_ : Atom → Term → Term
  _⋅_  : Term → Term → Term
infix 7 ƛ_↦_
infix 6 _⋅_

_﹕_ : ∀ {A B : Set} → A → B → A × B
_﹕_ = ⟨_,_⟩
infix 5 _﹕_

Cx : Set
Cx = List (Term × ★)

data _∋_ : Cx → (Atom × ★) → Set where
  head : ∀ {Γ α a} → Γ , (var a ﹕ α) ∋ (a ﹕ α)
  tail : ∀ {Γ α β a b} → ¬(a ≡ b) → Γ ∋ (a ﹕ α) → Γ , (var b ﹕ β) ∋ (a ﹕ α)
infix 8 _∋_

data _⊢_ : Cx → (Term × ★) → Set where
  VAR : ∀ {Γ α x}       → Γ ∋ (x ﹕ α) → Γ ⊢ (var x ﹕ α)
  LAM : ∀ {Γ α β x M}   → Γ , (var x ﹕ α) ⊢ (M ﹕ β) → Γ ⊢ (ƛ x ↦ M ﹕ α ⊳ β)
  APP : ∀ {Γ α β f x y} → Γ ⊢ (f ﹕ α ⊳ β) → Γ ⊢ (x ﹕ α) → Γ ⊢ (y ﹕ β)
infix 1 _⊢_

-- Closed terms, or terms derivable from an empty context.
Closed : (Term × ★) → Set
Closed = _⊢_ ∅

-- Free variables in a term.
FV : ∀ {Γ A} → Γ ⊢ A → List Atom
FV (VAR {x = a} i) = [ a ]
FV (LAM {x = a} t) = (FV t) - a
FV (APP t₁ t₂)     = (FV t₁) ⧺ (FV t₂) -- The ⧺ really should be ∪, does this mean trouble?

-- λI terms, or terms where each assumption is used at least once.
λI : ∀ {Γ A} → Γ ⊢ A → Set
λI (VAR i)         = ⊤
λI (LAM {x = a} t) = (λI t) × (a ∈ (FV t))
λI (APP t₁ t₂)     = (λI t₁) × (λI t₂)

-- Affine terms, or terms where each assumption is used at most once.
Affine : ∀ {Γ A} → Γ ⊢ A → Set
Affine (VAR i) = ⊤
Affine (LAM t) = Affine t
Affine (APP t₁ t₂) = (Affine t₁) × (Affine t₂) × (Empty ((FV t₁) ∩ (FV t₂)))

-- Linear terms, or terms where each assumption is used exactly once.
Linear : ∀ {Γ A} → Γ ⊢ A → Set
Linear t = (λI t) × (Affine t)


-- A couple examples
I           : Closed ((ƛ v₀ ↦ (var v₀)) ﹕ (ι ⊳ ι))
I           = LAM (VAR head)
I-λI     : λI I
I-λI     = ⟨ • , zero ⟩
I-Affine : Affine I
I-Affine = •
I-Linear : Linear I
I-Linear = ⟨ I-λI , I-Affine ⟩

B : Closed ((ƛ v₀ ↦ (ƛ v₁ ↦ (ƛ v₂ ↦ (var v₀ ⋅ (var v₁ ⋅ var v₂))))) ﹕ (ι ⊳ ι) ⊳ (ι ⊳ ι) ⊳ ι ⊳ ι)
B = LAM (LAM (LAM (APP {x = var v₀} (VAR (tail (λ ()) (tail (λ ()) head))) (APP (VAR (tail (λ ()) head)) (VAR head)))))
B-λI : λI B
B-λI = ⟨ ⟨ ⟨ ⟨ • , ⟨ • , • ⟩ ⟩ , zero ⟩ , zero ⟩ , zero ⟩
B-Affine : Affine B
B-Affine = ⟨ • , ⟨ ⟨ • , ⟨ • , refl ⟩ ⟩ , refl ⟩ ⟩
B-Linear : Linear B
B-Linear = ⟨ B-λI , B-Affine ⟩


module AgdaSemantics where
  open import Data.Nat using (ℕ)

  ⟦_⟧★ : ★ → Set
  ⟦ ι ⟧★       = ℕ
  ⟦ t₁ ⊳ t₂ ⟧★ = ⟦ t₁ ⟧★ → ⟦ t₂ ⟧★

  ⟦_⟧C : Cx → Set
  ⟦ ∅ ⟧C             = ⊤
  ⟦ c , ⟨ a , α ⟩ ⟧C = ⟦ c ⟧C × ⟦ α ⟧★

  ⟦_⟧ : ∀ {Γ a α} → Γ ⊢ (a ﹕ α) → ⟦ Γ ⟧C → ⟦ α ⟧★
  ⟦ VAR head ⟧ c         = π₂ c
  ⟦ VAR (tail x₁ x₂) ⟧ c = ⟦ VAR x₂ ⟧ (π₁ c)
  ⟦ LAM t ⟧ c            = λ a → ⟦ t ⟧ ⟨ c , a ⟩
  ⟦ APP t₁ t₂ ⟧ c        = (⟦ t₁ ⟧ c) (⟦ t₂ ⟧ c)
