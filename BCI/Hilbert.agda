module BCI.Hilbert where
open import Common

-- A tree variant of a Hilbert-style proof system with "BCI" as axioms.


data Form : Set where
  var : Atom → Form
  _⇒_ : Form → Form → Form
infixr 10 _⇒_

Cx : Set
Cx = List Form

data _⊢_ : Cx → Form → Set where
  ID : ∀ {Γ A}     → A ∈ Γ
                     → Γ ⊢ A
  MP : ∀ {Γ A B}   → Γ ⊢ A ⇒ B → Γ ⊢ A
                     → Γ ⊢ B
  AB : ∀ {Γ A B C} → Γ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
  AC : ∀ {Γ A B C} → Γ ⊢ (A ⇒ (B ⇒ C)) ⇒ B ⇒ (A ⇒ C)
  AI : ∀ {Γ A}     → Γ ⊢ A ⇒ A
infix 5 _⊢_
-- Note: Adding deduction theorem as an axiom makes this system equivalent to SKI:
-- K : ∀ {A B} → ∅ ⊢ A ⇒ B ⇒ A
-- K = MP AC (DT AI)
-- It's harder to find a construction for S, however I managed to prove completeness
-- with the deduction theorem in a structure which is also complete for IPC.


-- Monotonicity of ⊢ with respect to context extension.
mono⊢ : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A → Γ' ⊢ A
mono⊢ γ (ID i)     = ID (mono∈ γ i)
mono⊢ γ (MP f₁ f₂) = MP (mono⊢ γ f₁) (mono⊢ γ f₂)
mono⊢ γ AB         = AB
mono⊢ γ AC         = AC
mono⊢ γ AI         = AI


module AgdaSemantics where

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

  lookup : ∀ {Γ A} → A ∈ Γ → Γ ⊨ A
  lookup zero γ    = π₂ γ
  lookup (suc i) γ = (lookup i) (π₁ γ)

  sound : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
  sound (ID i) γ = lookup i γ
  sound (MP f₁ f₂) γ = (sound f₁ γ) (sound f₂ γ)
  sound AB = λ _ x y z → x (y z)
  sound AC = λ _ x y z → x z y
  sound AI = λ _ x → x
