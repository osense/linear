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
  ID : ∀ {Γ A}     → A ∈ Γ → Γ ⊢ A
  MP : ∀ {Γ A B}   → Γ ⊢ A ⇒ B → Γ ⊢ A
                   → Γ ⊢ B
  AB : ∀ {Γ A B C} → Γ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
  AC : ∀ {Γ A B C} → Γ ⊢ (A ⇒ (B ⇒ C)) ⇒ B ⇒ (A ⇒ C)
  AI : ∀ {Γ A}     → Γ ⊢ A ⇒ A
infix 5 _⊢_


-- Monotonicity of ⊢ with respect to context extension.
mono⊢ : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A → Γ' ⊢ A
mono⊢ γ (ID i) = ID (mono∈ γ i)
mono⊢ γ (MP f₁ f₂) = MP (mono⊢ γ f₁) (mono⊢ γ f₂)
mono⊢ γ AB = AB
mono⊢ γ AC = AC
mono⊢ γ AI = AI

-- Constructor injectivity a.k.a. inversion principles
var-inv : ∀ {A B} → var A ≡ var B → A ≡ B
var-inv refl = refl

⇒-inv₁ : ∀ {A A' B B'} → A ⇒ B ≡ A' ⇒ B' → A ≡ A'
⇒-inv₁ refl = refl

⇒-inv₂ : ∀ {A A' B B'} → A ⇒ B ≡ A' ⇒ B' → B ≡ B'
⇒-inv₂ refl = refl

-- Decidable equality of formulas.
instance _≟_ : ∀ (A A' : Form) → Dec (A ≡ A')
var x₁ ≟ var x₂ with x₁ ≟ₐ x₂
var x₁ ≟ var .x₁ | yes refl = yes refl
var x₁ ≟ var x₂ | no ¬p = no (λ x → ¬p (var-inv x))
var x ≟ (b ⇒ b₁) = no λ ()
(a ⇒ a₁) ≟ var x = no λ ()
(a ⇒ a₁) ≟ (b ⇒ b₁) with a ≟ b | a₁ ≟ b₁
(a ⇒ a₁) ≟ (.a ⇒ .a₁) | yes refl | yes refl = yes refl
(a ⇒ a₁) ≟ (b ⇒ b₁) | no ¬p | _ = no (λ x → ¬p (⇒-inv₁ x))
(a ⇒ a₁) ≟ (b ⇒ b₁) | _ | no ¬p = no (λ x → ¬p (⇒-inv₂ x))
