module STLC where

open import STLC.Definition renaming
  (Cx to Cxˢ
  ;_⊢_ to _⊢ˢ_
  ;var to varˢ
  ;ƛ_ to ƛˢ_
  ;_⋅_ to _⋅ˢ_
  ;cong⊢ to cong⊢ˢ
  ;weaken to weakenˢ
  ;contract to contractˢ
  ;exchange to exchangeˢ
  ;exchange⧺ to exchange⧺ˢ
  ;det to detˢ) public
