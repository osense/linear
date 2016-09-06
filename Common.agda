module Common where
open import Data.Empty using (⊥) public
open import Data.Unit using (⊤) renaming (tt to •) public
open import Function using () renaming (_∘′_ to _∘_) public
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩; proj₁ to π₁; proj₂ to π₂) public
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ₙ_)
open import Data.Bool using (Bool; true; false; if_then_else_; not) renaming (_∧_ to _and_; _∨_ to _or_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂) public
open import Relation.Nullary using (Dec; yes; no) public

-- Basic equipment.


abstract
  Atom : Set
  Atom = ℕ

  v₀ v₁ v₂ : Atom
  v₀ = 0
  v₁ = 1
  v₂ = 2

  _≟ₐ_ : (a b : Atom) → Dec (a ≡ b)
  a ≟ₐ b = a ≟ₙ b


data List (A : Set) : Set where
  ∅   : List A
  _,_ : List A → A → List A
infixl 10 _,_

data _∈_ {A} : A → List A → Set where
  zero : ∀ {x xs} → x ∈ xs , x
  suc  : ∀ {x y xs} → x ∈ xs → x ∈ xs , y
infix 8 _∈_

-- Context extension.
data _⊆_ {A} : List A → List A → Set where
  self : ∀ {Γ} → Γ ⊆ Γ
  addᵣ : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ ⊆ Γ' , A
  addₗ : ∀ {Γ Γ' A} → Γ ⊆ Γ' → Γ , A ⊆ Γ' , A
infix 8 _⊆_

-- Injectivity a.k.a. inversion principles
addᵣ-inv : ∀ {A} {Γ Γ' : List A} {x : A} → Γ , x ⊆ Γ' → Γ ⊆ Γ'
addᵣ-inv self = addᵣ self
addᵣ-inv (addᵣ e) = addᵣ (addᵣ-inv e)
addᵣ-inv (addₗ e) = addᵣ e

addₗ-inv : ∀ {A} {Γ Γ' : List A} {x : A} → Γ , x ⊆ Γ' , x → Γ ⊆ Γ'
addₗ-inv self = self
addₗ-inv (addᵣ e) = addᵣ-inv e
addₗ-inv (addₗ e) = e

mono∈ : ∀ {A} {Γ Γ' : List A} {x : A} → Γ ⊆ Γ' → x ∈ Γ → x ∈ Γ'
mono∈ self i = i
mono∈ (addᵣ e) i = suc (mono∈ e i)
mono∈ (addₗ e) zero = zero
mono∈ (addₗ e) (suc i) = suc (mono∈ e i)

trans⊆ : ∀ {A} {Γ Γ' Γ'' : List A} → Γ ⊆ Γ' → Γ' ⊆ Γ'' → Γ ⊆ Γ''
trans⊆ e₁ self = e₁
trans⊆ e₁ (addᵣ e₂) = addᵣ (trans⊆ e₁ e₂)
trans⊆ self (addₗ e₂) = addₗ e₂
trans⊆ (addᵣ e₁) (addₗ e₂) = addᵣ (trans⊆ e₁ e₂)
trans⊆ (addₗ e₁) (addₗ e₂) = addₗ (trans⊆ e₁ e₂)

_⧺_ : ∀ {A} → List A → List A → List A
Γ ⧺ ∅     = Γ
Γ ⧺ Δ , A = (Γ ⧺ Δ) , A
infixl 9 _⧺_

⧺-∅-unitₗ : ∀ {A} {l : List A} → ∅ ⧺ l ≡ l
⧺-∅-unitₗ {l = ∅} = refl
⧺-∅-unitₗ {l = l , x} = cong₂ _,_ (⧺-∅-unitₗ {l = l}) refl

⊆-⧺-weaken₁ : ∀ {A} {Γ Γ₁ Γ₂ : List A} → Γ₁ ⧺ Γ₂ ⊆ Γ → Γ₁ ⊆ Γ
⊆-⧺-weaken₁ {Γ₂ = ∅} e = e
⊆-⧺-weaken₁ {Γ₂ = Γ₂ , x} e = ⊆-⧺-weaken₁ {Γ₂ = Γ₂} (addᵣ-inv e)
