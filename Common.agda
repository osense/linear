module Common where
open import Function                              using (_$_) renaming (_∘′_ to _∘_) public
open import Category.Monad public
open import Data.Empty                            using (⊥) public
open import Data.Unit                             using (⊤) renaming (tt to •) public
open import Data.Fin                              using (Fin) renaming (zero to zeroᶠ; suc to sucᶠ) public
open import Data.Product                          using (_×_) renaming (_,_ to ⟨_,_⟩; proj₁ to π₁; proj₂ to π₂) public
open import Data.Bool                             using (Bool; true; false; if_then_else_; not) renaming (_∧_ to _and_; _∨_ to _or_) public
open import Data.Maybe                            using (Maybe; just; nothing) renaming (monad to Mmonad) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂) public
open import Relation.Nullary                      using (Dec; yes; no; ¬_) public


-- Types reused by multiple systems.
data ★ : Set where
  ι   : ★
  _⊳_ : ★ → ★ → ★
infixr 8 _⊳_


-- Equality instances.
record Eq (t : Set) : Set where
  field
    _==_ : t → t → Bool
  _/=_ : t → t → Bool
  a /= b = not (a == b)
open Eq {{…}} public


-- Atoms, used as variable identifiers.
open import Data.Nat using (ℕ) renaming (zero to zeroⁿ; suc to sucⁿ)

Atom : Set
Atom = ℕ

v₀ v₁ v₂ : Atom
v₀ = 0
v₁ = 1
v₂ = 2

_==ₙ_ : ℕ → ℕ → Bool
zeroⁿ  ==ₙ zeroⁿ  = true
zeroⁿ  ==ₙ sucⁿ b = false
sucⁿ a ==ₙ zeroⁿ  = false
sucⁿ a ==ₙ sucⁿ b = a ==ₙ b

instance Eqₐ : Eq Atom
Eqₐ = record {_==_ = _==ₙ_}

-- Finite sets; these can be used as de Bruijn indices.
_==ᶠ_ : ∀ {n} → Fin n → Fin n → Bool
zeroᶠ  ==ᶠ zeroᶠ  = true
zeroᶠ  ==ᶠ sucᶠ b = false
sucᶠ a ==ᶠ zeroᶠ  = false
sucᶠ a ==ᶠ sucᶠ b = a ==ᶠ b

instance Eqᶠ : ∀ {n} → Eq (Fin n)
Eqᶠ = record {_==_ = _==ᶠ_ }


-- Lists, used as contexts.
data List (A : Set) : Set where
  ∅   : List A
  _,_ : List A → A → List A
infixl 10 _,_

[_] : ∀ {A} → A → List A
[ x ] = ∅ , x

isEmpty : ∀ {A} → List A → Bool
isEmpty ∅       = true
isEmpty (l , x) = false

Empty : ∀ {A} → List A → Set
Empty l = (isEmpty l) ≡ true

len : ∀ {A} → (List A) → ℕ
len ∅        = ℕ.zero
len (xs , x) = ℕ.suc (len xs)

-- Decrement every de Bruijn index in a list, erasing zero.
pop : ∀ {s} → List (Fin (sucⁿ s)) → List (Fin s)
pop ∅ = ∅
pop (xs , x) with x
pop (xs , x) | zeroᶠ  = pop xs
pop (xs , x) | sucᶠ f = pop xs , f

pop-Fin1-empties : (l : List (Fin 1)) → Empty (pop l)
pop-Fin1-empties ∅ = refl
pop-Fin1-empties (xs , x) with x
pop-Fin1-empties (xs , x) | zeroᶠ = pop-Fin1-empties xs
pop-Fin1-empties (xs , x) | sucᶠ ()


-- List inclusion, or de Bruijn indices.
data _∈_ {A} : A → List A → Set where
  zero : ∀ {x xs} → x ∈ xs , x
  suc  : ∀ {x y xs} → x ∈ xs → x ∈ xs , y
infix 8 _∈_

∈-to-Fin : ∀ {A} {L : List A} {x : A} → x ∈ L → Fin (len L)
∈-to-Fin zero    = zeroᶠ
∈-to-Fin (suc p) = sucᶠ (∈-to-Fin p)


-- Context extension.
data _⊆_ {A} : List A → List A → Set where
  stop : ∀ {Γ} → Γ ⊆ Γ
  skip : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊆ Γ' , A
  keep : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ , A ⊆ Γ' , A
infix 8 _⊆_


-- Some helpful lemmas.
cong⊆₁ : ∀ {A} {L₁ L₁' L₂ : List A} → L₁ ⊆ L₂ → L₁ ≡ L₁' → L₁' ⊆ L₂
cong⊆₁ p refl = p

⊆-∅ : ∀ {A} {L : List A} → ∅ ⊆ L
⊆-∅ {L = ∅}      = stop
⊆-∅ {L = xs , x} = skip ⊆-∅

mono∈ : ∀ {A} {Γ Γ' : List A} {x : A} → Γ ⊆ Γ' → x ∈ Γ → x ∈ Γ'
mono∈ stop i           = i
mono∈ (skip e) i       = suc (mono∈ e i)
mono∈ (keep e) zero    = zero
mono∈ (keep e) (suc i) = suc (mono∈ e i)

trans⊆ : ∀ {A} {Γ Γ' Γ'' : List A} → Γ ⊆ Γ' → Γ' ⊆ Γ'' → Γ ⊆ Γ''
trans⊆ e₁ stop             = e₁
trans⊆ e₁ (skip e₂)        = skip (trans⊆ e₁ e₂)
trans⊆ stop (keep e₂)      = keep e₂
trans⊆ (skip e₁) (keep e₂) = skip (trans⊆ e₁ e₂)
trans⊆ (keep e₁) (keep e₂) = keep (trans⊆ e₁ e₂)


-- List concatenation.
_⧺_ : ∀ {A} → List A → List A → List A
Γ ⧺ ∅     = Γ
Γ ⧺ Δ , A = (Γ ⧺ Δ) , A
infixl 9 _⧺_ _⁏_

_⁏_ : ∀ {A} → List A → List A → List A
_⁏_ = _⧺_

assoc⧺ : ∀ {A} {L₁ L₂ L₃ : List A} → L₁ ⧺ (L₂ ⧺ L₃) ≡ (L₁ ⧺ L₂) ⧺ L₃
assoc⧺ {L₃ = ∅} = refl
assoc⧺ {L₃ = xs , x} = cong₂ _,_ (assoc⧺ {L₃ = xs}) refl

unit⧺ₗ : ∀ {A} {L : List A} → ∅ ⧺ L ≡ L
unit⧺ₗ {L = ∅} = refl
unit⧺ₗ {L = xs , x} = cong₂ _,_ (unit⧺ₗ {L = xs}) refl

⧺-⊆₁ : ∀ {A} {L₁ L₂ : List A} → L₁ ⊆ (L₁ ⧺ L₂)
⧺-⊆₁ {L₂ = ∅} = stop
⧺-⊆₁ {L₂ = xs , x} = skip (⧺-⊆₁ {L₂ = xs})

⧺-⊆₂ : ∀ {A} {L₁ L₂ : List A} → L₂ ⊆ (L₁ ⧺ L₂)
⧺-⊆₂ {L₂ = ∅} = ⊆-∅
⧺-⊆₂ {L₂ = xs , x} = keep ⧺-⊆₂

⧺-Empty : ∀ {A} {L₁ L₂ : List A} → Empty L₁ → Empty L₂ → Empty (L₁ ⧺ L₂)
⧺-Empty {L₂ = ∅} p₁ p₂ = p₁
⧺-Empty {L₂ = L₂ , x} p₁ ()


-- Looking up an element in a list
lookup : ∀ {A} {{== : Eq A}} → A → List A → Bool
lookup a ∅        = false
lookup a (xs , x) = if a == x then true else lookup a xs

-- Set-theoretic list intersection.
_∩_ : ∀ {A} {{== : Eq A}} → List A → List A → List A
∅ ∩ l₂        = ∅
(l₁ , x) ∩ l₂ = if (lookup x l₂) then (l₁ ∩ l₂) , x
                                 else (l₁ ∩ l₂)

Empty∩₁ : ∀ {A} {{== : Eq A}} {L₁ L₂ : List A} → Empty L₁ → Empty (L₁ ∩ L₂)
Empty∩₁ {L₁ = ∅} p = refl
Empty∩₁ {L₁ = L₁ , x} ()


-- I am tempted to call this "Functional term reasoning".
-- TODO: Figure out if Relation.Binary.PreorderReasoning can be implemented with this.
-- One observation is that PreorderReasoning lets me type in values (that Agda doesn't need to see),
-- whereas this lets me punch in types of the values I am operating on.
-- However this is unlikely to make a difference, as it should be easy to lift values
-- to their respective types.
infix 1 begin[_]_
infixr 2 _↝[_]_ _↝[]_
infix 3 _∎

begin[_]_ : {A B : Set} → A → (A → B) → B
begin[ x ] f = f x

_↝[_]_ : {a b c : Set} → Set → (a → b) → (b → c) → (a → c)
_ ↝[ f ] g = g ∘ f

_↝[]_ : {a b : Set} → Set → (a → b) → (a → b)
_ ↝[] g = g

_∎ : {a : Set} → Set → (a → a)
_ ∎ = λ x → x
