module STLC.Definition where
open import Common

-- Simply typed λ calculus.


data ★ : Set where
  ι : ★
  _⊳_ : ★ → ★ → ★
infixr 10 _⊳_

-- Context as a list of named assumptions.
Cx : Set
Cx = List (Atom × ★)

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
λI (var x)   = ⊤
λI (ƛ a ↦ M) = (λI M) × (a ∈ (FV M))
λI (M ⋅ N)   = (λI M) × (λI N)

-- Affine terms, or terms where each assumption is used at most once.
Affine : ∀ {Γ A} → Γ ⊢ A → Set
Affine (var x)   = ⊤
Affine (ƛ a ↦ M) = Affine M
Affine (M ⋅ N)   = (Affine M) × (Affine N) × (Empty ((FV M) ∩ (FV N)))

-- Linear terms, or terms where each assumption is used exactly once.
Linear : ∀ {Γ A} → Γ ⊢ A → Set
Linear t = (λI t) × (Affine t)

-- Closed terms, defined as terms derivable from every context.
Closed : ★ → Set
Closed a = ∀ {Γ} → Γ ⊢ a


-- A few well-known examples of linear terms, with meta polymorphism,
-- which is annoyingly unresolvable by Agda.
I        : ∀ {Γ α} → Γ ⊢ (α ⊳ α)
I        = ƛ v₀ ↦ var head
I-λI     : ∀ {Γ α} → λI (I {Γ} {α})
I-λI     = ⟨ • , head ⟩
I-Affine : ∀ {Γ α} → Affine (I {Γ} {α})
I-Affine = •
I-Linear : ∀ {Γ α} → Linear (I {Γ} {α})
I-Linear {Γ} {α} = ⟨ I-λI {Γ} {α} , I-Affine {Γ} {α} ⟩

B        : ∀ {Γ α β γ} → Γ ⊢ ((β ⊳ γ) ⊳ (α ⊳ β) ⊳ α ⊳ γ)
B        = ƛ v₀ ↦ (ƛ v₁ ↦ (ƛ v₂ ↦ (var (tail (tail head)) ⋅ (var (tail head) ⋅ var head))))
B-λI     : ∀ {Γ α β γ} → λI (B {Γ} {α} {β} {γ})
B-λI     = ⟨ ⟨ ⟨ ⟨ • , ⟨ • , • ⟩ ⟩ , head ⟩ , head ⟩ , head ⟩
B-Affine : ∀ {Γ α β γ} → Affine (B {Γ} {α} {β} {γ})
B-Affine = ⟨ • , ⟨ ⟨ • , ⟨ • , refl ⟩ ⟩ , refl ⟩ ⟩
B-Linear : ∀ {Γ α β γ} → Linear (B {Γ} {α} {β} {γ})
B-Linear {Γ} {α} {β} {γ} = ⟨ B-λI {Γ} {α} {β} {γ} , B-Affine {Γ} {α} {β} {γ} ⟩

C        : ∀ {Γ α β γ} → Γ ⊢ ((α ⊳ β ⊳ γ) ⊳ β ⊳ α ⊳ γ)
C        = ƛ v₀ ↦ (ƛ v₁ ↦ (ƛ v₂ ↦ var (tail (tail head)) ⋅ var head ⋅ var (tail head)))
C-λI     : ∀ {Γ α β γ} → λI (C {Γ} {α} {β} {γ})
C-λI     = ⟨ ⟨ ⟨ ⟨ ⟨ • , • ⟩ , • ⟩ , tail head ⟩ , head ⟩ , head ⟩
C-Affine : ∀ {Γ α β γ} → Affine (C {Γ} {α} {β} {γ})
C-Affine = ⟨ ⟨ • , ⟨ • , refl ⟩ ⟩ , ⟨ • , refl ⟩ ⟩
C-Linear : ∀ {Γ α β γ} → Linear (C {Γ} {α} {β} {γ})
C-Linear {Γ} {α} {β} {γ} = ⟨ C-λI {Γ} {α} {β} {γ} , C-Affine {Γ} {α} {β} {γ} ⟩
