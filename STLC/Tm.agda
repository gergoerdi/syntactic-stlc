module Tm where

data Ty : Set where
  ∙   : Ty
  _▷_ : Ty → Ty → Ty
  Bool : Ty

open import Ren Ty public
open import Relation.Binary.PropositionalEquality

infixl 23 _·_
data Tm (Γ : Ctx) : Ty → Set where
  var : ∀ {t}   (v : Var t Γ)                   → Tm Γ t
  lam : ∀ t {u} (e : Tm (Γ , t) u)              → Tm Γ (t ▷ u)
  _·_ : ∀ {u t} (f : Tm Γ (u ▷ t)) (e : Tm Γ u) → Tm Γ t

  true false : Tm Γ Bool
  if_then_else_ : ∀ {t} (b : Tm Γ Bool) (thn : Tm Γ t) (els : Tm Γ t) → Tm Γ t

ren : ∀ {Γ Δ t} → Δ ⊇ Γ → Tm Γ t → Tm Δ t
ren Δ⊇Γ (var x)                  = var (renᵛ Δ⊇Γ x)
ren Δ⊇Γ (lam t e)                = lam t (ren (keep Δ⊇Γ) e)
ren Δ⊇Γ (f · e)                  = ren Δ⊇Γ f · ren Δ⊇Γ e
ren Δ⊇Γ true                     = true
ren Δ⊇Γ false                    = false
ren Δ⊇Γ (if b then thn else els) = if (ren Δ⊇Γ b) then ren Δ⊇Γ thn else ren Δ⊇Γ els

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
