module Sub where

open import Relation.Binary.PropositionalEquality hiding (subst)
open import Tm

infixr 4 _,_
infix 3 _⊢⋆_
data _⊢⋆_ (Γ : Ctx) : Ctx → Set where
  ∅ : Γ ⊢⋆ ∅
  _,_ : ∀ {t Δ} → (σ : Γ ⊢⋆ Δ) → (e : Tm Γ t) → Γ ⊢⋆ Δ , t

infixr 20 _⊇⊢⋆_
_⊇⊢⋆_ : ∀ {Γ Δ Θ} → Θ ⊇ Γ → Γ ⊢⋆ Δ → Θ ⊢⋆ Δ
Θ⊇Γ ⊇⊢⋆ ∅       = ∅
Θ⊇Γ ⊇⊢⋆ (σ , e) = Θ⊇Γ ⊇⊢⋆ σ , ren Θ⊇Γ e

infixl 20 _⊢⋆⊇_
_⊢⋆⊇_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Δ → Δ ⊇ Θ → Γ ⊢⋆ Θ
σ       ⊢⋆⊇ done       = σ
(σ , e) ⊢⋆⊇ (drop Δ⊇Θ) = σ ⊢⋆⊇ Δ⊇Θ
(σ , e) ⊢⋆⊇ (keep Δ⊇Θ) = σ ⊢⋆⊇ Δ⊇Θ , e

wkₛ : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ
wkₛ σ = wk ⊇⊢⋆ σ

shift : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ , t
shift {t} σ = wk ⊇⊢⋆ σ , var vz

subᵛ : ∀ {Γ Δ t} → Γ ⊢⋆ Δ → Var t Δ → Tm Γ t
subᵛ (σ , e) vz     = e
subᵛ (σ , e) (vs v) = subᵛ σ v

sub : ∀ {Γ Δ t} → Γ ⊢⋆ Δ → Tm Δ t → Tm Γ t
sub σ (var x)                  = subᵛ σ x
sub σ (lam t e)                = lam t (sub (shift σ) e)
sub σ (f · e)                  = sub σ f · sub σ e
sub σ true                     = true
sub σ false                    = false
sub σ (if b then thn else els) = if sub σ b then sub σ thn else sub σ els

ren⇒sub : ∀ {Γ Δ} → Γ ⊇ Δ → Γ ⊢⋆ Δ
ren⇒sub done       = ∅
ren⇒sub (drop Γ⊇Δ) = wk ⊇⊢⋆ (ren⇒sub Γ⊇Δ)
ren⇒sub (keep Γ⊇Δ) = shift (ren⇒sub Γ⊇Δ)

reflₛ : ∀ {Γ} → Γ ⊢⋆ Γ
reflₛ {∅}     = ∅
reflₛ {Γ , t} = shift reflₛ

_⊢⊢⋆_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Θ → Θ ⊢⋆ Δ → Γ ⊢⋆ Δ
σ ⊢⊢⋆ ∅ = ∅
σ ⊢⊢⋆ (ρ , e) = (σ ⊢⊢⋆ ρ) , sub σ e

assocᵣᵣₛ : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (Δ⊇Θ : Δ ⊇ Θ) (σ : Θ ⊢⋆ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (Δ⊇Θ ⊇⊢⋆ σ) ≡ (Γ⊇Δ ⊇⊇ Δ⊇Θ) ⊇⊢⋆ σ
assocᵣᵣₛ Γ⊇Δ Δ⊇Θ ∅ = refl
assocᵣᵣₛ Γ⊇Δ Δ⊇Θ (σ , e) rewrite assocᵣᵣₛ Γ⊇Δ Δ⊇Θ σ | ren-⊇⊇ Γ⊇Δ Δ⊇Θ e = refl

assocᵣₛᵣ : ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (Θ⊇Ξ : Θ ⊇ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (σ ⊢⋆⊇ Θ⊇Ξ) ≡  (Γ⊇Δ ⊇⊢⋆ σ) ⊢⋆⊇ Θ⊇Ξ
assocᵣₛᵣ Γ⊇Δ σ       done       = refl
assocᵣₛᵣ Γ⊇Δ (σ , e) (drop Θ⊇Ξ) rewrite assocᵣₛᵣ Γ⊇Δ σ Θ⊇Ξ = refl
assocᵣₛᵣ Γ⊇Δ (σ , e) (keep Θ⊇Ξ) rewrite assocᵣₛᵣ Γ⊇Δ σ Θ⊇Ξ = refl

refl-⊇⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) →
  reflᵣ ⊇⊢⋆ σ ≡ σ
refl-⊇⊢⋆ ∅       = refl
refl-⊇⊢⋆ (σ , e) rewrite refl-⊇⊢⋆ σ | ren-refl e = refl

_⊢⋆⊇-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⋆⊇ reflᵣ ≡ σ
∅       ⊢⋆⊇-refl = refl
(σ , e) ⊢⋆⊇-refl rewrite σ ⊢⋆⊇-refl = refl

refl-⊢⋆⊇_ : ∀ {Γ Δ} (Γ⊇Δ : Γ ⊇ Δ) →
  reflₛ ⊢⋆⊇ Γ⊇Δ ≡ ren⇒sub Γ⊇Δ
refl-⊢⋆⊇ done           = refl
refl-⊢⋆⊇ (drop {t} Γ⊇Δ) rewrite sym (assocᵣₛᵣ (wk {t}) reflₛ Γ⊇Δ) | refl-⊢⋆⊇ Γ⊇Δ = refl
refl-⊢⋆⊇ (keep {t} Γ⊇Δ) rewrite sym (assocᵣₛᵣ (wk {t}) reflₛ Γ⊇Δ) | refl-⊢⋆⊇ Γ⊇Δ = refl

subᵛ-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (v : Var t Θ) →
  subᵛ (σ ⊢⋆⊇ Δ⊇Θ) v ≡ subᵛ σ (renᵛ Δ⊇Θ v)
subᵛ-⊢⋆⊇ σ       done v            = refl
subᵛ-⊢⋆⊇ (σ , e) (drop Δ⊇Θ) v      rewrite subᵛ-⊢⋆⊇ σ Δ⊇Θ v = refl
subᵛ-⊢⋆⊇ (σ , e) (keep Δ⊇Θ) vz     = refl
subᵛ-⊢⋆⊇ (σ , e) (keep Δ⊇Θ) (vs v) rewrite subᵛ-⊢⋆⊇ σ Δ⊇Θ v = refl

sub-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : Tm Θ t) →
  sub (σ ⊢⋆⊇ Δ⊇Θ) e ≡ sub σ (ren Δ⊇Θ e)
sub-⊢⋆⊇ σ Δ⊇Θ (var v)                  = subᵛ-⊢⋆⊇ σ Δ⊇Θ v
sub-⊢⋆⊇ σ Δ⊇Θ (lam t e)                rewrite assocᵣₛᵣ (wk {t}) σ Δ⊇Θ | sub-⊢⋆⊇ (shift σ) (keep Δ⊇Θ) e = refl
sub-⊢⋆⊇ σ Δ⊇Θ (f · e)                  rewrite sub-⊢⋆⊇ σ Δ⊇Θ f | sub-⊢⋆⊇ σ Δ⊇Θ e = refl
sub-⊢⋆⊇ σ Δ⊇Θ true                     = refl
sub-⊢⋆⊇ σ Δ⊇Θ false                    = refl
sub-⊢⋆⊇ σ Δ⊇Θ (if b then thn else els) rewrite sub-⊢⋆⊇ σ Δ⊇Θ b | sub-⊢⋆⊇ σ Δ⊇Θ thn | sub-⊢⋆⊇ σ Δ⊇Θ els = refl

sub-⊇⊢⋆ᵛ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (v : Var t Θ) →
  subᵛ (Γ⊇Δ ⊇⊢⋆ σ) v ≡ ren Γ⊇Δ (subᵛ σ v)
sub-⊇⊢⋆ᵛ Γ⊇Δ (σ , _) vz     = refl
sub-⊇⊢⋆ᵛ Γ⊇Δ (σ , _) (vs v) = sub-⊇⊢⋆ᵛ Γ⊇Δ σ v

sub-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : Tm Θ t) →
  sub (Γ⊇Δ ⊇⊢⋆ σ) e ≡ ren Γ⊇Δ (sub σ e)
sub-⊇⊢⋆ Γ⊇Δ σ (var v)                  = sub-⊇⊢⋆ᵛ Γ⊇Δ σ v
sub-⊇⊢⋆ Γ⊇Δ σ (f · e)                  rewrite sub-⊇⊢⋆ Γ⊇Δ σ f | sub-⊇⊢⋆ Γ⊇Δ σ e = refl
sub-⊇⊢⋆ Γ⊇Δ σ true                     = refl
sub-⊇⊢⋆ Γ⊇Δ σ false                    = refl
sub-⊇⊢⋆ Γ⊇Δ σ (if b then thn else els) rewrite sub-⊇⊢⋆ Γ⊇Δ σ b | sub-⊇⊢⋆ Γ⊇Δ σ thn | sub-⊇⊢⋆ Γ⊇Δ σ els = refl
sub-⊇⊢⋆ Γ⊇Δ σ (lam t e)                rewrite
  assocᵣᵣₛ (wk {t}) Γ⊇Δ σ | refl-⊇⊇ Γ⊇Δ | sym (Γ⊇Δ ⊇⊇-refl) |
  assocᵣᵣₛ (keep Γ⊇Δ) (wk {t}) σ | sym (assocᵣᵣₛ (keep Γ⊇Δ) (wk {t}) σ) |
  Γ⊇Δ ⊇⊇-refl | sub-⊇⊢⋆ (keep Γ⊇Δ) (shift σ) e
  = refl

assocₛᵣₛ : ∀ {Γ Δ Θ Ξ} (ρ : Θ ⊢⋆ Ξ) (Δ⊇Θ : Δ ⊇ Θ) (σ : Γ ⊢⋆ Δ) →
  σ ⊢⊢⋆ (Δ⊇Θ ⊇⊢⋆ ρ) ≡ (σ ⊢⋆⊇ Δ⊇Θ) ⊢⊢⋆ ρ
assocₛᵣₛ ∅       Δ⊇Θ σ = refl
assocₛᵣₛ (ρ , e) Δ⊇Θ σ rewrite assocₛᵣₛ ρ Δ⊇Θ σ | sym (sub-⊢⋆⊇ σ Δ⊇Θ e) = refl

assocᵣₛₛ :  ∀ {Γ Δ Θ Ξ} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Ξ) →
  Γ⊇Δ ⊇⊢⋆ (σ ⊢⊢⋆ ρ) ≡ (Γ⊇Δ ⊇⊢⋆ σ) ⊢⊢⋆ ρ
assocᵣₛₛ Γ⊇Δ σ ∅       = refl
assocᵣₛₛ Γ⊇Δ σ (ρ , e) rewrite assocᵣₛₛ Γ⊇Δ σ ρ | sym (sub-⊇⊢⋆ Γ⊇Δ σ e) = refl

subᵛ-refl : ∀ {Γ t} (v : Var t Γ) → subᵛ reflₛ v ≡ var v
subᵛ-refl vz         = refl
subᵛ-refl (vs {u} v) rewrite sub-⊇⊢⋆ᵛ (wk {u}) reflₛ v | subᵛ-refl v | renᵛ-refl v = refl

sub-refl : ∀ {Γ t} (e : Tm Γ t) → sub reflₛ e ≡ e
sub-refl (var v)                 = subᵛ-refl v
sub-refl (lam t e)               rewrite sub-refl e = refl
sub-refl (f · e)                 rewrite sub-refl f | sub-refl e = refl
sub-refl true                     = refl
sub-refl false                    = refl
sub-refl (if b then thn else els) rewrite sub-refl b | sub-refl thn | sub-refl els = refl

subᵛ-⊢⊢⋆  : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (v : Var t Δ) →
  subᵛ (σ ⊢⊢⋆ ρ) v ≡ sub σ (subᵛ ρ v)
subᵛ-⊢⊢⋆ σ (ρ , _) vz     = refl
subᵛ-⊢⊢⋆ σ (ρ , _) (vs v) = subᵛ-⊢⊢⋆ σ ρ v

sub-⊢⊢⋆ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : Tm Δ t) →
  sub (σ ⊢⊢⋆ ρ) e ≡ sub σ (sub ρ e)
sub-⊢⊢⋆ σ ρ (var v)                  = subᵛ-⊢⊢⋆ σ ρ v
sub-⊢⊢⋆ σ ρ (f · e)                  rewrite sub-⊢⊢⋆ σ ρ f | sub-⊢⊢⋆ σ ρ e = refl
sub-⊢⊢⋆ σ ρ true                     = refl
sub-⊢⊢⋆ σ ρ false                    = refl
sub-⊢⊢⋆ σ ρ (if b then thn else els) rewrite sub-⊢⊢⋆ σ ρ b | sub-⊢⊢⋆ σ ρ thn | sub-⊢⊢⋆ σ ρ els = refl
sub-⊢⊢⋆ σ ρ (lam t e)                rewrite
  assocᵣₛₛ (wk {t}) σ ρ | sym (cong (_⊢⊢⋆ ρ) ((wk {t} ⊇⊢⋆ σ) ⊢⋆⊇-refl)) |
  sym (assocₛᵣₛ ρ (wk {t}) (shift σ)) | sub-⊢⊢⋆ (shift σ) (shift ρ) e
  = refl

-- -- Is this version clearer?
-- sub-⊢⊢⋆ σ ρ (lam t e) = cong (lam t) $
--     cong (λ x → sub (x , var vz) e)
--         (assocᵣₛₛ (wk {t}) σ ρ
--       ⟨ trans ⟩
--         cong (_⊢⊢⋆ ρ) (sym ((wk {t} ⊇⊢⋆ σ) ⊢⋆⊇-refl))
--       ⟨ trans ⟩
--         sym (assocₛᵣₛ ρ (wk {t}) (shift σ)))
--   ⟨ trans ⟩
--     sub-⊢⊢⋆ (shift σ) (shift ρ) e
--   where
--     open import Function using (_⟨_⟩_; _$_)

refl-⊢⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → reflₛ ⊢⊢⋆ σ ≡ σ
refl-⊢⊢⋆ ∅       = refl
refl-⊢⊢⋆ (σ , e) rewrite refl-⊢⊢⋆ σ | sub-refl e = refl

_⊢⊢⋆-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⊢⋆ reflₛ ≡ σ
∅       ⊢⊢⋆-refl = refl
(σ , e) ⊢⊢⋆-refl rewrite assocₛᵣₛ reflₛ wk (σ , e) | σ ⊢⋆⊇-refl | σ ⊢⊢⋆-refl = refl
