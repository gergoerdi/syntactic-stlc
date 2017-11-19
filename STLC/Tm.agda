module Tm where

open import Ty
open import Ctx Ty public
open import Ren Ty public

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
