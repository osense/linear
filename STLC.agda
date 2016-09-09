module STLC where
open import Common

-- Simply typed λ calculus.


data ★ : Set where
  ι : ★
  _⊳_ : ★ → ★ → ★
infixr 10 _⊳_

-- Context as a list of named assumptions.
Cx : Set
Cx = List (Atom × ★)

_﹕_ : {A B : Set} → A → B → A × B
a ﹕ b = ⟨ a , b ⟩

data _⊢_ (Γ : Cx) : ★ → Set where
  var : ∀ {a α}  → (a ﹕ α) ∈ Γ → Γ ⊢ α
  ƛ_↦_ : ∀ {α β} → (a : Atom)   → Γ , (a ﹕ α) ⊢ β → Γ ⊢ α ⊳ β
  _⋅_ : ∀ {α β}  → Γ ⊢ α ⊳ β    → Γ ⊢ α            → Γ ⊢ β
infix 1 _⊢_
infix 5 ƛ_↦_
infixl 6 _⋅_

-- Free variables in a term.
FV : ∀ {Γ A} → Γ ⊢ A → List Atom
FV (var {a = a} x) = [ a ]
FV (ƛ a ↦ M)       = (FV M) - a
FV (M ⋅ N)         = (FV M) ∪ (FV N)

-- λI terms, or terms where each assumption is used at least once.
λI : ∀ {Γ A} → Γ ⊢ A → Set
λI (var x) = ⊤
λI (ƛ a ↦ M) = (λI M) × (a ∈ (FV M))
λI (M ⋅ N) = (λI M) × (λI N)

-- Affine terms, or terms where each assumption is used at most once.
Affine : ∀ {Γ A} → Γ ⊢ A → Set
Affine (var x) = ⊤
Affine (ƛ a ↦ M) = Affine M
Affine (M ⋅ N) = (Affine M) × (Affine N) × (Empty ((FV M) ∩ (FV N)))

-- Linear terms, or terms where each assumption is used exactly once.
Linear : ∀ {Γ A} → Γ ⊢ A → Set
Linear t = (λI t) × (Affine t)


-- A few well-known examples of linear terms.
I : ∅ ⊢ ι ⊳ ι
I = ƛ v₀ ↦ var head
I-λI : λI I
I-λI = ⟨ • , head ⟩
I-Affine : Affine I
I-Affine = •
I-Linear : Linear I
I-Linear = ⟨ I-λI , I-Affine ⟩

B : ∅ ⊢ (ι ⊳ ι) ⊳ (ι ⊳ ι) ⊳ ι ⊳ ι
B = ƛ v₀ ↦ (ƛ v₁ ↦ (ƛ v₂ ↦ (var (tail (tail head)) ⋅ (var (tail head) ⋅ var head))))
B-λI : λI B
B-λI = ⟨ ⟨ ⟨ ⟨ • , ⟨ • , • ⟩ ⟩ , head ⟩ , head ⟩ , head ⟩
B-Affine : Affine B
B-Affine = ⟨ • , ⟨ ⟨ • , ⟨ • , refl ⟩ ⟩ , refl ⟩ ⟩
B-Linear : Linear B
B-Linear = ⟨ B-λI , B-Affine ⟩

C : ∅ ⊢ (ι ⊳ ι ⊳ ι) ⊳ ι ⊳ ι ⊳ ι
C = ƛ v₀ ↦ (ƛ v₁ ↦ (ƛ v₂ ↦ var (tail (tail head)) ⋅ var (tail head) ⋅ var head))
C-λI : λI C
C-λI = ⟨ ⟨ ⟨ ⟨ ⟨ • , • ⟩ , • ⟩ , head ⟩ , head ⟩ , head ⟩
C-Affine : Affine C
C-Affine = ⟨ ⟨ • , ⟨ • , refl ⟩ ⟩ , ⟨ • , refl ⟩ ⟩
C-Linear : Linear C
C-Linear = ⟨ C-λI , C-Affine ⟩


module AgdaSemantics where
  open import Data.Nat using (ℕ)

  ⟦_⟧★ : ★ → Set
  ⟦ ι ⟧★       = ℕ
  ⟦ t₁ ⊳ t₂ ⟧★ = ⟦ t₁ ⟧★ → ⟦ t₂ ⟧★

  ⟦_⟧C : Cx → Set
  ⟦ ∅ ⟧C     = ⊤
  ⟦ c , t ⟧C = ⟦ c ⟧C × ⟦ π₂ t ⟧★

  ⟦_⟧ : ∀ {Γ α} → Γ ⊢ α → ⟦ Γ ⟧C → ⟦ α ⟧★
  ⟦ var head ⟧ c    = π₂ c
  ⟦ var (tail x) ⟧ c = ⟦ var x ⟧ (π₁ c)
  ⟦ ƛ x ↦ M ⟧ c       = λ a → ⟦ M ⟧ ⟨ c , a ⟩
  ⟦ f ⋅ x ⟧ c     = (⟦ f ⟧ c) (⟦ x ⟧ c)
