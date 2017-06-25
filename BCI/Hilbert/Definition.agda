module BCI.Hilbert.Definition where
open import Common

-- A tree variant of a Hilbert-style proof system with "BCI" as axioms.


data Form : Set where
  var : Atom → Form
  _⇒_ : Form → Form → Form
infixr 10 _⇒_

Cx : Set
Cx = List Form

data _⊢_ : Cx → Form → Set where
  ID : ∀ {A}           → [ A ] ⊢ A
  MP : ∀ {Γ₁ Γ₂ Δ A B} → Γ₁ ⊢ A ⇒ B → Γ₂ ⊢ A → Δ ≡ Γ₁ ⁏ Γ₂ → Δ ⊢ B
  EX : ∀ {Γ x y A}     → Γ , x , y ⊢ A → Γ , y , x ⊢ A
  AB : ∀ {A B C}       → ∅ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
  AC : ∀ {A B C}       → ∅ ⊢ (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C
  AI : ∀ {A}           → ∅ ⊢ A ⇒ A
infix 5 _⊢_


det : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ , A ⊢ B
det t = MP t ID refl

{-# TERMINATING #-} --Oops.
ded : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
ded ID = AI
ded {Γ} {A'} {B'} (MP {Γ₁} {∅} {_} {A} t₁ t₂ refl) = begin[ t₁ ]
  Γ , A' ⊢ A ⇒ B'     ↝[ ded ]
  Γ ⊢ A' ⇒ A ⇒ B'     ↝[ (λ this → MP AC this refl) ]
  ∅ ⁏ Γ ⊢ A ⇒ A' ⇒ B' ↝[ subst₂ _⊢_ (unit⧺₂ {L₂ = ∅}) refl ]
  Γ ⊢ A ⇒ A' ⇒ B'     ↝[ (λ this → MP this t₂ refl) ]
  Γ ⊢ A' ⇒ B' ∎
ded {B = B} (MP {Γ₁} {xs , A'} {_} {A} t₁ t₂ refl) = begin[ t₁ ]
  Γ₁ ⊢ A ⇒ B                   ↝[ (λ this → MP AB this refl) ]
  ∅ ⁏ Γ₁ ⊢ (A' ⇒ A) ⇒ (A' ⇒ B) ↝[ subst₂ _⊢_ (unit⧺₂ {L₂ = ∅}) refl ]
  Γ₁ ⊢ (A' ⇒ A) ⇒ (A' ⇒ B)     ↝[ (λ this → MP this (ded t₂) refl) ]
  Γ₁ ⁏ xs ⊢ (A' ⇒ B) ∎
ded {_} {A} {B} (EX {Γ} {x} {y} t) = begin[ t ]
  Γ , A , y ⊢ B     ↝[ ded ∘ ded ]
  Γ ⊢ A ⇒ y ⇒ B     ↝[ (λ this → MP AC this refl) ]
  ∅ ⁏ Γ ⊢ y ⇒ A ⇒ B ↝[ subst₂ _⊢_ (unit⧺₂ {L₂ = ∅}) refl ]
  Γ ⊢ y ⇒ A ⇒ B     ↝[ (λ this → MP this ID refl) ]
  Γ , y ⊢ A ⇒ B ∎
