module Common where
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ₙ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong) public
open import Relation.Nullary using (Dec; yes; no) public

-- Basic equipment


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
  •   : List A
  _,_ : List A → A → List A
infixl 10 _,_

data _∈_ {A} : A → List A → Set where
  zero : ∀ {x xs} → x ∈ xs , x
  suc  : ∀ {x y xs} → x ∈ xs → x ∈ xs , y
infix 8 _∈_

_⧺_ : ∀ {A} → List A → List A → List A
Γ ⧺ •     = Γ
Γ ⧺ Δ , A = (Γ ⧺ Δ) , A
infixl 9 _⧺_
