module Ren {a : _} (A : Set a) where

open import Ctx A public
open import Relation.Binary.PropositionalEquality

infix 3 _⊇_
data _⊇_ : Ctx → Ctx → Set where
  done : ∅ ⊇ ∅
  drop : ∀ {t Γ Δ} → Γ ⊇ Δ → Γ , t ⊇ Δ
  keep : ∀ {t Γ Δ} → Γ ⊇ Δ → Γ , t ⊇ Δ , t

reflᵣ : ∀ {Γ} → Γ ⊇ Γ
reflᵣ {∅} = done
reflᵣ {Γ , _} = keep reflᵣ

wk : ∀ {t Γ} → (Γ , t) ⊇ Γ
wk = drop reflᵣ

_⊇⊇_ : ∀ {Γ Θ Δ} → Γ ⊇ Θ → Θ ⊇ Δ → Γ ⊇ Δ
done       ⊇⊇       Θ⊇Δ  = Θ⊇Δ
(drop Γ⊇Θ) ⊇⊇       Θ⊇Δ  = drop (Γ⊇Θ ⊇⊇ Θ⊇Δ)
(keep Γ⊇Θ) ⊇⊇ (drop Θ⊇Δ) = drop (Γ⊇Θ ⊇⊇ Θ⊇Δ)
(keep Γ⊇Θ) ⊇⊇ (keep Θ⊇Δ) = keep (Γ⊇Θ ⊇⊇ Θ⊇Δ)

renᵛ : ∀ {Γ Δ t} → Δ ⊇ Γ → Var t Γ → Var t Δ
renᵛ done       v      = v
renᵛ (drop Δ⊇Γ) v      = vs (renᵛ Δ⊇Γ v)
renᵛ (keep Δ⊇Γ) vz     = vz
renᵛ (keep Δ⊇Γ) (vs v) = vs (renᵛ Δ⊇Γ v)

refl-⊇⊇_ : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) →
  reflᵣ ⊇⊇ Γ⊇Δ ≡ Γ⊇Δ
refl-⊇⊇ done     = refl
refl-⊇⊇ drop Γ⊇Δ rewrite refl-⊇⊇ Γ⊇Δ = refl
refl-⊇⊇ keep Γ⊇Δ rewrite refl-⊇⊇ Γ⊇Δ = refl

_⊇⊇-refl : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) →
  Γ⊇Δ ⊇⊇ reflᵣ ≡ Γ⊇Δ
done     ⊇⊇-refl = refl
drop Γ⊇Δ ⊇⊇-refl rewrite Γ⊇Δ ⊇⊇-refl = refl
keep Γ⊇Δ ⊇⊇-refl rewrite Γ⊇Δ ⊇⊇-refl = refl

⊇-assoc : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (Δ⊇Θ : Δ ⊇ Θ) (Θ⊇Ξ : Θ ⊇ Ξ) →
  (Γ⊇Δ ⊇⊇ Δ⊇Θ) ⊇⊇ Θ⊇Ξ ≡ Γ⊇Δ ⊇⊇ (Δ⊇Θ ⊇⊇ Θ⊇Ξ)
⊇-assoc done             Δ⊇Θ        Θ⊇Ξ  = refl
⊇-assoc (drop Γ⊇Δ)       Δ⊇Θ        Θ⊇Ξ  rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl
⊇-assoc (keep Γ⊇Δ) (drop Δ⊇Θ)       Θ⊇Ξ  rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl
⊇-assoc (keep Γ⊇Δ) (keep Δ⊇Θ) (drop Θ⊇Ξ) rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl
⊇-assoc (keep Γ⊇Δ) (keep Δ⊇Θ) (keep Θ⊇Ξ) rewrite ⊇-assoc Γ⊇Δ Δ⊇Θ Θ⊇Ξ = refl

renᵛ-refl : ∀ {Γ t} (v : Var t Γ) → renᵛ reflᵣ v ≡ v
renᵛ-refl vz     = refl
renᵛ-refl (vs v) rewrite renᵛ-refl v = refl

renᵛ-⊇⊇ : ∀ {Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (v : Var t Δ) →
  renᵛ Γ⊇Θ (renᵛ Θ⊇Δ v) ≡ renᵛ (Γ⊇Θ ⊇⊇ Θ⊇Δ) v
renᵛ-⊇⊇ done             Θ⊇Δ  v      = refl
renᵛ-⊇⊇ (drop Γ⊇Θ)       Θ⊇Δ  v      rewrite renᵛ-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
renᵛ-⊇⊇ (keep Γ⊇Θ) (drop Θ⊇Δ) v      rewrite renᵛ-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
renᵛ-⊇⊇ (keep Γ⊇Θ) (keep Θ⊇Δ) vz     = refl
renᵛ-⊇⊇ (keep Γ⊇Θ) (keep Θ⊇Δ) (vs v) rewrite renᵛ-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
