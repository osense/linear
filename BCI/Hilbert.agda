module BCI.Hilbert where
open import Common

-- A tree variant of a Hilbert-style proof system with "BCI" as axioms.


data Form : Set where
  var : Atom → Form
  _⇒_ : Form → Form → Form
infixr 10 _⇒_

Cx : Set
Cx = List Form

-- We don't have any structural rules, so we should include AI despite having ID
data _⊢_ : Cx → Form → Set where
  ID : ∀ {Γ A}       → Γ , A ⊢ A
  MP : ∀ {Γ₁ Γ₂ A B} → Γ₁ ⊢ A ⇒ B → Γ₂ ⊢ A
                     → Γ₁ ⧺ Γ₂ ⊢ B
  AB : ∀ {Γ A B C}   → Γ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
  AC : ∀ {Γ A B C}   → Γ ⊢ (A ⇒ (B ⇒ C)) ⇒ B ⇒ (A ⇒ C)
  AI : ∀ {Γ A}       → Γ ⊢ A ⇒ A
infix 5 _⊢_


-- Constructor injectivity a.k.a. inversion principles
var-inj : ∀ {A B} → var A ≡ var B → A ≡ B
var-inj refl = refl

⇒-inj₁ : ∀ {A A' B B'} → A ⇒ B ≡ A' ⇒ B' → A ≡ A'
⇒-inj₁ refl = refl

⇒-inj₂ : ∀ {A A' B B'} → A ⇒ B ≡ A' ⇒ B' → B ≡ B'
⇒-inj₂ refl = refl

-- Decidable equality of formulas.
_≟_ : ∀ (A A' : Form) → Dec (A ≡ A')
var x₁ ≟ var x₂ with x₁ ≟ₐ x₂
var x₁ ≟ var .x₁ | yes refl = yes refl
var x₁ ≟ var x₂ | no ¬p = no (λ x → ¬p (var-inj x))
var x ≟ (b ⇒ b₁) = no λ ()
(a ⇒ a₁) ≟ var x = no λ ()
(a ⇒ a₁) ≟ (b ⇒ b₁) with a ≟ b | a₁ ≟ b₁
(a ⇒ a₁) ≟ (.a ⇒ .a₁) | yes refl | yes refl = yes refl
(a ⇒ a₁) ≟ (b ⇒ b₁) | no ¬p | _ = no (λ x → ¬p (⇒-inj₁ x))
(a ⇒ a₁) ≟ (b ⇒ b₁) | _ | no ¬p = no (λ x → ¬p (⇒-inj₂ x))
