module BCI.HilbertSKI where
open import Common

-- A tree variant of a Hilbert-style proof system with "BCI" as axioms
-- and also the deduction theorem, which makes it seemingly equivalent
-- to SKI.
-- Really only included because of documentational purposes.


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
  DT : ∀ {Γ A B}   → Γ , A ⊢ B
                     → Γ ⊢ A ⇒ B
  AB : ∀ {Γ A B C} → Γ ⊢ (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)
  AC : ∀ {Γ A B C} → Γ ⊢ (A ⇒ (B ⇒ C)) ⇒ B ⇒ (A ⇒ C)
  AI : ∀ {Γ A}     → Γ ⊢ A ⇒ A
infix 5 _⊢_


-- Monotonicity of ⊢ with respect to context extension.
mono⊢ : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊢ A → Γ' ⊢ A
mono⊢ γ (ID i)     = ID (mono∈ γ i)
mono⊢ γ (MP f₁ f₂) = MP (mono⊢ γ f₁) (mono⊢ γ f₂)
mono⊢ γ (DT p)     = DT (mono⊢ (addₗ γ) p)
mono⊢ γ AB         = AB
mono⊢ γ AC         = AC
mono⊢ γ AI         = AI

_⊢★_ : ∀ (Γ Δ : Cx) → Set
Γ ⊢★ ∅ = ⊤
Γ ⊢★ (Δ , x) = Γ ⊢★ Δ × Γ ⊢ x
infix 5 _⊢★_

weaken⊢★ : ∀ {Γ Δ A} → Γ ⊢★ Δ → Γ , A ⊢★ Δ
weaken⊢★ {Δ = ∅} • = •
weaken⊢★ {Δ = Δ , x} p = ⟨ weaken⊢★ (π₁ p) , mono⊢ (addᵣ self) (π₂ p) ⟩

refl⊢★ : ∀ {Γ} → Γ ⊢★ Γ
refl⊢★ {∅} = •
refl⊢★ {Γ , x} = ⟨ weaken⊢★ (refl⊢★ {Γ}) , ID zero ⟩

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
var x₁ ≟ var .x₁ | yes refl                 = yes refl
var x₁ ≟ var x₂ | no ¬p                     = no (λ x → ¬p (var-inv x))
var x ≟ (b ⇒ b₁)                            = no λ ()
(a ⇒ a₁) ≟ var x                            = no λ ()
(a ⇒ a₁) ≟ (b ⇒ b₁) with a ≟ b | a₁ ≟ b₁
(a ⇒ a₁) ≟ (.a ⇒ .a₁) | yes refl | yes refl = yes refl
(a ⇒ a₁) ≟ (b ⇒ b₁) | no ¬p | _             = no (λ x → ¬p (⇒-inv₁ x))
(a ⇒ a₁) ≟ (b ⇒ b₁) | _ | no ¬p             = no (λ x → ¬p (⇒-inv₂ x))


module AgdaSemantics where

  record Model : Set₁ where
    field
      _⊩ᵃ_   : Cx → Atom → Set
      mono⊩ᵃ : ∀ {Γ Γ' a} → Γ ⊆ Γ' → Γ ⊩ᵃ a → Γ' ⊩ᵃ a
  open Model {{…}} public

  module _ {{V : Model}} where
    _⊩_ : Cx → Form → Set
    Γ ⊩ var x     = Γ ⊩ᵃ x
    Γ ⊩ (f₁ ⇒ f₂) = ∀ {Γ'} → Γ ⊆ Γ' → (Γ' ⊩ f₁) → (Γ' ⊩ f₂)
    infix 5 _⊩_

    _⊩★_ : Cx → Cx → Set
    Γ ⊩★ ∅        = ⊤
    Γ ⊩★ (Γ' , A) = (Γ ⊩★ Γ') × (Γ ⊩ A)
    infix 5 _⊩★_

    -- Weakening of ⊩
    weaken⊩ : ∀ {Γ A B} → Γ ⊩ B → Γ , A ⊩ B
    weaken⊩ {B = var x} p     = mono⊩ᵃ (addᵣ self) p
    weaken⊩ {B = f₁ ⇒ f₂} p e = λ f → p (addᵣ-inv e) f

    -- Weakening of ⊩★
    weaken⊩★ : ∀ {Γ Δ A} → Γ ⊩★ Δ → Γ , A ⊩★ Δ
    weaken⊩★ {Δ     = ∅} p         = p
    weaken⊩★ {Γ} {Δ = Δ , x} {A} p = ⟨ weaken⊩★ (π₁ p) , weaken⊩ {Γ} {A} {x} (π₂ p) ⟩

    -- Monotonicity of ⊩ with respect to ⊆
    mono⊩ : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊩ A → Γ' ⊩ A
    mono⊩ {A = var x} e p = mono⊩ᵃ e p
    mono⊩ {A = A ⇒ A₁} e p = λ e' p' → p (trans⊆ e e') p'

    -- Monotonicity of ⊩★ with respect to ⊆
    mono⊩★ : ∀ {Γ Γ' Δ} → Γ ⊆ Γ' → Γ ⊩★ Δ → Γ' ⊩★ Δ
    mono⊩★ {Δ = ∅} e p = p
    mono⊩★ {Δ = Δ , x} e p = ⟨ mono⊩★ e (π₁ p) , mono⊩ {A = x} e (π₂ p) ⟩


  _⊨_ : Cx → Form → Set₁
  Γ ⊨ f = ∀ {{V : Model}} {Δ} → Δ ⊩★ Γ → Δ ⊩ f

  lookup : ∀ {Γ A} → A ∈ Γ → Γ ⊨ A
  lookup zero γ    = π₂ γ
  lookup (suc i) γ = (lookup i) (π₁ γ)

  sound : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
  sound (ID i) γ = lookup i γ
  sound (MP f₁ f₂) γ = (sound f₁ γ self) (sound f₂ γ)
  sound (DT p) γ e = λ f → sound p ⟨ mono⊩★ e γ , f ⟩
  sound AB = λ _ px x py y pz z → x (trans⊆ py pz) (y pz z)
  sound (AC {B = B}) = λ _ px x py y pz z → x (trans⊆ py pz) z self (mono⊩ {A = B} pz y)
  sound AI = λ _ _ z → z


  instance Canon : Model
  Canon = record
    {_⊩ᵃ_ = λ Γ a → Γ ⊢ (var a)
    ;mono⊩ᵃ = λ e p → mono⊢ e p}

  -- Soundness and completeness in the canonical model.
  mutual
    sound' : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A
    sound' {A = var x} p     = p
    sound' {A = f₁ ⇒ f₂} p e = λ a → sound' (MP (mono⊢ e p) (complete' a))

    complete' : ∀ {Γ A} → Γ ⊩ A → Γ ⊢ A
    complete' {A     = var x} e   = e
    complete' {Γ} {A = f₁ ⇒ f₂} e = DT (complete' (e (addᵣ self) (sound' (ID (zero {x = f₁} {xs = Γ})))))

    sound★' : ∀ {Γ Δ} → Γ ⊢★ Δ → Γ ⊩★ Δ
    sound★' {Δ = ∅} p = p
    sound★' {Δ = Δ , x} p = ⟨ sound★' (π₁ p) , sound' (π₂ p) ⟩

  refl⊩★ : ∀ {Γ} → Γ ⊩★ Γ
  refl⊩★ = sound★' (refl⊢★)

  complete : ∀ {Γ A} → Γ ⊨ A → Γ ⊢ A
  complete p = complete' (p refl⊩★)

  -- Normalization by evaluation. Doesn't really work, what with the deduction theorem
  -- being an axiom and all.
  nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
  nbe = complete ∘ sound
