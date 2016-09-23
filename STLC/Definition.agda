module STLC.Definition where
open import Common

-- Simply typed λ calculus.


-- Context as a list of assumptions.
Cx : Set
Cx = List ★

data _⊢_ (Γ : Cx) : ★ → Set where
  var : ∀ {α}   → α ∈ Γ     → Γ ⊢ α
  ƛ_  : ∀ {α β} → Γ , α ⊢ β → Γ ⊢ α ⊳ β
  _⋅_ : ∀ {α β} → Γ ⊢ α ⊳ β → Γ ⊢ α → Γ ⊢ β
infix 1 _⊢_
infixr 5 ƛ_
infixl 6 _⋅_


cong⊢ : ∀ {Γ Δ α} → Γ ⊢ α → Γ ≡ Δ → Δ ⊢ α
cong⊢ M refl = M

-- Implicit structural rules.
weaken : ∀ {Γ Δ α} → Γ ⊢ α → Γ ⊆ Δ → Δ ⊢ α
weaken (var x) γ = var (mono∈ γ x)
weaken (ƛ M) γ   = ƛ (weaken M (keep γ))
weaken (M ⋅ N) γ = (weaken M γ) ⋅ (weaken N γ)

contract : ∀ {Γ x α} → Γ , x , x ⊢ α → Γ , x ⊢ α
contract M = (ƛ M) ⋅ var zero

exchange : ∀ {Γ x y α} → Γ , x , y ⊢ α → Γ , y , x ⊢ α
exchange M = (weaken (ƛ ƛ M) (skip (skip stop))) ⋅ (var zero) ⋅ (var (suc zero))


-- Detachment theorem.
det : ∀ {Γ α β} → Γ ⊢ α ⊳ β → Γ , α ⊢ β
det M = (weaken M (skip stop)) ⋅ var zero


-- Exchange with ⧺.
exchange⧺1 : ∀ {Γ x α} → Γ , x ⊢ α → [ x ] ⧺ Γ ⊢ α
exchange⧺1 {∅} M     = M
exchange⧺1 {Γ , x} M = det (exchange⧺1 (ƛ (exchange M)))

-- TODO: Something about this?
exchange⧺ : ∀ {Γ₁ Γ₂ α} → Γ₁ ⧺ Γ₂ ⊢ α → Γ₂ ⧺ Γ₁ ⊢ α
exchange⧺ {Γ₂ = ∅} M           = cong⊢ M (sym (unit⧺ₗ))
exchange⧺ {Γ₁} {Γ₂ = xs , x} M = cong⊢ (exchange⧺ {Γ₁ = [ x ] ⧺ Γ₁} {Γ₂ = xs}
                                         (cong⊢
                                           (exchange⧺1 M)
                                           (assoc⧺ {L₁ = [ x ]} {Γ₁} {xs})))
                                       (trans (assoc⧺ {L₁ = xs} {[ x ]} {Γ₁}) refl)


-- Free variables in a term, with duplicates.
FV : ∀ {Γ A} → Γ ⊢ A → List (Fin (len Γ))
FV (var x) = [ ∈-to-Fin x ]
FV (ƛ M)   = pop (FV M)
FV (M ⋅ N) = FV M ⧺ FV N

-- λI terms, or terms where each assumption is used at least once.
λI : ∀ {Γ A} → Γ ⊢ A → Set
λI (var x) = ⊤
λI (ƛ M)   = (λI M) × (zeroᶠ ∈ (FV M))
λI (M ⋅ N) = (λI M) × (λI N)

-- Affine terms, or terms where each assumption is used at most once.
Affine : ∀ {Γ A} → Γ ⊢ A → Set
Affine (var x) = ⊤
Affine (ƛ M)   = Affine M
Affine (M ⋅ N) = (Affine M) × (Affine N) × Empty ((FV M) ∩ (FV N))

-- Linear terms, or terms where each assumption is used exactly once.
Linear : ∀ {Γ A} → Γ ⊢ A → Set
Linear t = (λI t) × (Affine t)

-- Closed terms, or terms derivable from empty context.
Closed : ★ → Set
Closed a = ∅ ⊢ a

Closed-FV : ∀ {A} → (t : Closed A) → Empty (FV t)
Closed-FV (var ())
Closed-FV (ƛ M)   = pop-Fin1-empties (FV M)
Closed-FV (M ⋅ N) = ⧺-Empty (Closed-FV M) (Closed-FV N)


-- A few well-known examples of linear terms, with meta polymorphism,
-- which is annoyingly unresolvable by Agda.
I        : ∀ {Γ α} → Γ ⊢ (α ⊳ α)
I        = ƛ var zero
I-λI     : ∀ {Γ α} → λI (I {Γ} {α})
I-λI     = ⟨ • , zero ⟩
I-Affine : ∀ {Γ α} → Affine (I {Γ} {α})
I-Affine = •
I-Linear : ∀ {Γ α} → Linear (I {Γ} {α})
I-Linear {Γ} {α} = ⟨ I-λI {Γ} {α} , I-Affine {Γ} {α} ⟩

B        : ∀ {Γ α β γ} → Γ ⊢ ((β ⊳ γ) ⊳ (α ⊳ β) ⊳ α ⊳ γ)
B        = ƛ ƛ ƛ (var (suc (suc zero)) ⋅ (var (suc zero) ⋅ var zero))
B-λI     : ∀ {Γ α β γ} → λI (B {Γ} {α} {β} {γ})
B-λI     = ⟨ ⟨ ⟨ ⟨ • , ⟨ • , • ⟩ ⟩ , zero ⟩ , zero ⟩ , zero ⟩
B-Affine : ∀ {Γ α β γ} → Affine (B {Γ} {α} {β} {γ})
B-Affine = ⟨ • , ⟨ ⟨ • , ⟨ • , refl ⟩ ⟩ , refl ⟩ ⟩
B-Linear : ∀ {Γ α β γ} → Linear (B {Γ} {α} {β} {γ})
B-Linear {Γ} {α} {β} {γ} = ⟨ B-λI {Γ} {α} {β} {γ} , B-Affine {Γ} {α} {β} {γ} ⟩

C        : ∀ {Γ α β γ} → Γ ⊢ ((α ⊳ β ⊳ γ) ⊳ β ⊳ α ⊳ γ)
C        = ƛ ƛ ƛ var (suc (suc zero)) ⋅ var zero ⋅ var (suc zero)
C-λI     : ∀ {Γ α β γ} → λI (C {Γ} {α} {β} {γ})
C-λI     = ⟨ ⟨ ⟨ ⟨ ⟨ • , • ⟩ , • ⟩ , suc zero ⟩ , zero ⟩ , zero ⟩
C-Affine : ∀ {Γ α β γ} → Affine (C {Γ} {α} {β} {γ})
C-Affine = ⟨ ⟨ • , ⟨ • , refl ⟩ ⟩ , ⟨ • , refl ⟩ ⟩
C-Linear : ∀ {Γ α β γ} → Linear (C {Γ} {α} {β} {γ})
C-Linear {Γ} {α} {β} {γ} = ⟨ C-λI {Γ} {α} {β} {γ} , C-Affine {Γ} {α} {β} {γ} ⟩
