module BCI.Combinators.ClosedToSTLC where
open import Common
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
import BCI.Combinators as B
import BCI.Combinators.AgdaSemantics as B
import STLC as S
import STLC.AgdaSemantics as S

-- Translation from closed terms of the BCI combinator calculus to closed
-- terms of λ calculus.


trans : ∀ {A} → B.Closed A → S.Closed A
trans (B.id ())
trans (B.app f x) = (trans f) S.⋅ (trans x)
trans B.B         = S.B
trans B.C         = S.C
trans B.I         = S.I

-- The translation creates linear terms.
λI : ∀ {A} → (t : B.Closed A) → S.λI (trans t)
λI (B.id ())
λI (B.app f x)        = ⟨ λI f , λI x ⟩
λI (B.B {α} {β} {γ} ) = S.B-λI {∅} {α} {β} {γ}
λI (B.C {α} {β} {γ} ) = S.C-λI {∅} {α} {β} {γ}
λI (B.I {α})          = S.I-λI {∅} {α}

Affine : ∀ {A} → (t : B.Closed A) → S.Affine (trans t)
Affine (B.id ())
Affine (B.app f x)        = ⟨ Affine f , ⟨ Affine x , Empty∩₁ (S.Closed-FV (trans f)) ⟩ ⟩
Affine (B.B {α} {β} {γ} ) = S.B-Affine {∅} {α} {β} {γ}
Affine (B.C {α} {β} {γ} ) = S.C-Affine {∅} {α} {β} {γ}
Affine (B.I {α})          = S.I-Affine {∅} {α}

Linear : ∀ {A} → (t : B.Closed A) → S.Linear (trans t)
Linear t = ⟨ λI t , Affine t ⟩

-- The translation preserves Agda semantics.
sound : ∀ {A} → (t : B.Closed A) → B.⟦ t ⟧∅ ≡ S.⟦ trans t ⟧∅
sound (B.id ())
sound (B.app f x) = cong₂ _$_ (sound f) (sound x)
sound B.B         = refl
sound B.C         = refl
sound B.I         = refl
