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
