module Common where
open import Function                              using (_$_) renaming (_∘′_ to _∘_) public
open import Category.Monad public
open import Data.Empty                            using (⊥) public
open import Data.Unit                             using (⊤) renaming (tt to •) public
open import Data.Fin                              using (Fin) renaming (zero to zeroᶠ; suc to sucᶠ) public
open import Data.Product                          using (_×_) renaming (_,_ to ⟨_,_⟩; proj₁ to π₁; proj₂ to π₂) public
open import Data.Bool                             using (Bool; true; false; if_then_else_; not) renaming (_∧_ to _and_; _∨_ to _or_) public
open import Data.Maybe                            using (Maybe; just; nothing) renaming (monad to Mmonad) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂) public
open import Relation.Nullary                      using (Dec; yes; no; ¬_) public

-- Basic equipment.
open import Data.Nat using (ℕ) renaming (zero to zeroⁿ; suc to sucⁿ)


record Eq (t : Set) : Set where
  field _==_ : t → t → Bool
  _/=_ : t → t → Bool
  a /= b = not (a == b)
open Eq {{…}} public

instance
  MaybeMonad : ∀ {l} → RawMonad {l} Maybe
  MaybeMonad = Mmonad
open RawMonad {{…}} public


_﹕_ : {A B : Set} → A → B → A × B
a ﹕ b = ⟨ a , b ⟩


-- Atoms, used as variable identifiers.
Atom : Set
Atom = ℕ

v₀ v₁ v₂ : Atom
v₀ = 0
v₁ = 1
v₂ = 2

_==ₙ_ : ℕ → ℕ → Bool
ℕ.zero ==ₙ ℕ.zero = true
ℕ.zero ==ₙ ℕ.suc b = false
ℕ.suc a ==ₙ ℕ.zero = false
ℕ.suc a ==ₙ ℕ.suc b = a ==ₙ b

_==ᶠ_ : ∀ {n} → Fin n → Fin n → Bool
zeroᶠ ==ᶠ zeroᶠ = true
zeroᶠ ==ᶠ sucᶠ b = false
sucᶠ a ==ᶠ zeroᶠ = false
sucᶠ a ==ᶠ sucᶠ b = a ==ᶠ b

instance Eqₐ : Eq Atom
Eqₐ = record {_==_ = _==ₙ_}

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

map : ∀ {A B} → (A → B) → List A → List B
map f ∅        = ∅
map f (xs , x) = map f xs , f x

filter : ∀ {A} → (A → Bool) → List A → List A
filter f ∅        = ∅
filter f (xs , x) = if f x then (filter f xs , x) else (filter f xs)

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f acc ∅        = acc
foldr f acc (xs , x) = foldr f (f x acc) xs

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
∈-to-Fin zero = zeroᶠ
∈-to-Fin (suc p) = sucᶠ (∈-to-Fin p)

-- Context extension.
data _⊆_ {A} : List A → List A → Set where
  stop : ∀ {Γ} → Γ ⊆ Γ
  skip : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊆ Γ' , A
  keep : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ , A ⊆ Γ' , A
infix 8 _⊆_

-- Constructor injectivity, a.k.a. inversion principles, for context extension.
skip-inv : ∀ {A} {Γ Γ' : List A} {x : A} → Γ , x ⊆ Γ' → Γ ⊆ Γ'
skip-inv stop = skip stop
skip-inv (skip e) = skip (skip-inv e)
skip-inv (keep e) = skip e

keep-inv : ∀ {A} {Γ Γ' : List A} {x : A} → Γ , x ⊆ Γ' , x → Γ ⊆ Γ'
keep-inv stop = stop
keep-inv (skip e) = skip-inv e
keep-inv (keep e) = e


-- Some helpful lemmas.
mono∈ : ∀ {A} {Γ Γ' : List A} {x : A} → Γ ⊆ Γ' → x ∈ Γ → x ∈ Γ'
mono∈ stop i = i
mono∈ (skip e) i = suc (mono∈ e i)
mono∈ (keep e) zero = zero
mono∈ (keep e) (suc i) = suc (mono∈ e i)

trans⊆ : ∀ {A} {Γ Γ' Γ'' : List A} → Γ ⊆ Γ' → Γ' ⊆ Γ'' → Γ ⊆ Γ''
trans⊆ e₁ stop = e₁
trans⊆ e₁ (skip e₂) = skip (trans⊆ e₁ e₂)
trans⊆ stop (keep e₂) = keep e₂
trans⊆ (skip e₁) (keep e₂) = skip (trans⊆ e₁ e₂)
trans⊆ (keep e₁) (keep e₂) = keep (trans⊆ e₁ e₂)


-- List concatenation.
_⧺_ : ∀ {A} → List A → List A → List A
Γ ⧺ ∅     = Γ
Γ ⧺ Δ , A = (Γ ⧺ Δ) , A
infixl 9 _⧺_

⧺-∅-unitₗ : ∀ {A} {l : List A} → ∅ ⧺ l ≡ l
⧺-∅-unitₗ {l = ∅} = refl
⧺-∅-unitₗ {l = l , x} = cong₂ _,_ (⧺-∅-unitₗ {l = l}) refl

⧺-Empty : ∀ {A} {L₁ L₂ : List A} → Empty L₁ → Empty L₂ → Empty (L₁ ⧺ L₂)
⧺-Empty {L₂ = ∅} p₁ p₂ = p₁
⧺-Empty {L₂ = L₂ , x} p₁ ()

⊆-⧺-weaken₁ : ∀ {A} {Γ Γ₁ Γ₂ : List A} → Γ₁ ⧺ Γ₂ ⊆ Γ → Γ₁ ⊆ Γ
⊆-⧺-weaken₁ {Γ₂ = ∅} e = e
⊆-⧺-weaken₁ {Γ₂ = Γ₂ , x} e = ⊆-⧺-weaken₁ {Γ₂ = Γ₂} (skip-inv e)


-- Subtracting a value from a list, once only.
_-_ : ∀ {A} {{== : Eq A}} → List A → A → List A
∅ - x = ∅
(l , x') - x = if x == x' then l else (l - x) , x'

-- Generalization of _-_ that subtracts multiple values.
_-★_ : ∀ {A} {{== : Eq A}} → List A → List A → List A
l₁ -★ ∅ = l₁
l₁ -★ (l₂ , x) = (l₁ - x) -★ l₂

-- Set-theoretic list union.
_∪_ : ∀ {A} {{== : Eq A}} → List A → List A → List A
l₁ ∪ l₂ = l₁ ⧺ (l₂ -★ l₁)


-- Looking up an element in a list
lookup : ∀ {A} {{== : Eq A}} → A → List A → Bool
lookup a ∅ = false
lookup a (xs , x) = if a == x then true else lookup a xs

-- Set-theoretic list intersection.
_∩_ : ∀ {A} {{== : Eq A}} → List A → List A → List A
∅ ∩ l₂ = ∅
(l₁ , x) ∩ l₂ = if (lookup x l₂) then (l₁ ∩ l₂) , x
                                 else (l₁ ∩ l₂)

Empty∩₁ : ∀ {A} {{== : Eq A}} {L₁ L₂ : List A} → Empty L₁ → Empty (L₁ ∩ L₂)
Empty∩₁ {L₁ = ∅} p = refl
Empty∩₁ {L₁ = L₁ , x} ()
