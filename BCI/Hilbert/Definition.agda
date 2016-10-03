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
  ID : ∀ {A}         → [ A ] ⊢ A
  MP : ∀ {Γ₁ Γ₂ A B} → Γ₁ ⊢ A ⇒ B  → Γ₂ ⊢ A → Γ₁ ⁏ Γ₂ ⊢ B
  EX : ∀ {Γ₁ Γ₂ A}   → Γ₁ ⁏ Γ₂ ⊢ A → Γ₂ ⁏ Γ₁ ⊢ A
  AB : ∀ {A B C}     → ∅ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
  AC : ∀ {A B C}     → ∅ ⊢ (A ⇒ B ⇒ C) ⇒ B ⇒ A ⇒ C
  AI : ∀ {A}         → ∅ ⊢ A ⇒ A
infix 5 _⊢_


det : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ , A ⊢ B
det t = MP t ID

ded : ∀ {Γ Δ A B} → Γ ⊢ B → Γ ≡ Δ , A → Δ ⊢ A ⇒ B
ded ID refl                       = AI
ded (MP {Γ₂ = ∅} t₁ t₂) eq        = subst₂ _⊢_ unit⧺₁ refl (MP (MP AC (ded t₁ eq)) t₂)
ded (MP {Γ₁} {xs , A} t₁ t₂) refl = subst₂ _⊢_ (unit⧺₂ {L₁ = Γ₁} {xs}) refl (MP (MP AB t₁) (ded t₂ refl))
ded (EX {∅} t) refl               = subst₂ _⊢_ unit⧺₁ refl (ded t refl)
ded (EX {Γ₁ , A} {∅} t) refl      = subst₂ _⊢_ (sym unit⧺₁) refl (ded t refl)
ded (EX {Γ₁ , A} {Γ₂ , x} t) refl = {!!}
ded AB ()
ded AC ()
ded AI ()

