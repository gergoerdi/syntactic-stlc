module Tm.Properties where

open import Tm
open import Ren.Properties Ty public
open import Relation.Binary.PropositionalEquality

ren-refl : ∀ {Γ t} (e : Tm Γ t) → ren reflᵣ e ≡ e
ren-refl (var v)                  rewrite renᵛ-refl v = refl
ren-refl (lam t e)                rewrite ren-refl e = refl
ren-refl (f · e)                  rewrite ren-refl f | ren-refl e = refl
ren-refl true                     = refl
ren-refl false                    = refl
ren-refl (if b then thn else els) rewrite ren-refl b | ren-refl thn | ren-refl els = refl

ren-⊇⊇ : ∀ {Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : Tm Δ t) →
  ren Γ⊇Θ (ren Θ⊇Δ e) ≡ ren (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
ren-⊇⊇ Γ⊇Θ Θ⊇Δ (var v)                  rewrite renᵛ-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
ren-⊇⊇ Γ⊇Θ Θ⊇Δ (lam t e)                rewrite ren-⊇⊇ (keep Γ⊇Θ) (keep Θ⊇Δ) e = refl
ren-⊇⊇ Γ⊇Θ Θ⊇Δ (f · e)                  rewrite ren-⊇⊇ Γ⊇Θ Θ⊇Δ f | ren-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl
ren-⊇⊇ Γ⊇Θ Θ⊇Δ true                     = refl
ren-⊇⊇ Γ⊇Θ Θ⊇Δ false                    = refl
ren-⊇⊇ Γ⊇Θ Θ⊇Δ (if b then thn else els) rewrite ren-⊇⊇ Γ⊇Θ Θ⊇Δ b | ren-⊇⊇ Γ⊇Θ Θ⊇Δ thn | ren-⊇⊇ Γ⊇Θ Θ⊇Δ els = refl
