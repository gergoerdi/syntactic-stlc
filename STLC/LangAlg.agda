open import Data.List
import LangAlg.Code
import LangAlg.Base

module LangAlg {Ty : Set} (cs : let open LangAlg.Code Ty in List Code) where

open import Data.Vec

open LangAlg.Base (fromList cs) public
open import Ren Ty
open import Data.List.All

mutual
  ren : ∀ {Γ Δ t} → Γ ⊇ Δ → Tm Δ t → Tm Γ t
  ren Γ⊇Δ (var v)   = var (renᵛ Γ⊇Δ v)
  ren Γ⊇Δ (con i e) = con i (renᶜ Γ⊇Δ e)

  renᶜ : ∀ {c Γ Δ t} → Γ ⊇ Δ → ⟦ c ⟧ᶜ Δ t → ⟦ c ⟧ᶜ Γ t
  renᶜ Γ⊇Δ (bind t e) = bind t (ren (keep Γ⊇Δ) e)
  renᶜ Γ⊇Δ (node es)  = node (renˡ Γ⊇Δ es)
  renᶜ Γ⊇Δ (some t e) = some t (renᶜ Γ⊇Δ e)

  renˡ : ∀ {Γ Δ ts} → Γ ⊇ Δ → All (Tm Δ) ts → All (Tm Γ) ts
  renˡ Γ⊇Δ []       = []
  renˡ Γ⊇Δ (e ∷ es) = ren Γ⊇Δ e ∷ renˡ Γ⊇Δ es

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

subᵛ : ∀ {Γ Δ t} → Γ ⊢⋆ Δ → Var t Δ → Tm Γ t
subᵛ (σ , e) vz     = e
subᵛ (σ , e) (vs v) = subᵛ σ v

shift : ∀ {t Γ Δ} → Γ ⊢⋆ Δ → Γ , t ⊢⋆ Δ , t
shift {t} σ = wk ⊇⊢⋆ σ , var vz

ren⇒sub : ∀ {Γ Δ} → Γ ⊇ Δ → Γ ⊢⋆ Δ
ren⇒sub done       = ∅
ren⇒sub (drop Γ⊇Δ) = wk ⊇⊢⋆ (ren⇒sub Γ⊇Δ)
ren⇒sub (keep Γ⊇Δ) = shift (ren⇒sub Γ⊇Δ)

reflₛ : ∀ {Γ} → Γ ⊢⋆ Γ
reflₛ {∅}     = ∅
reflₛ {Γ , t} = shift reflₛ

mutual
  sub : ∀ {Γ Δ t} → Γ ⊢⋆ Δ → Tm Δ t → Tm Γ t
  sub σ (var v)   = subᵛ σ v
  sub σ (con i e) = con i (subᶜ σ  e)

  subᶜ : ∀ {c Γ Δ t} → Γ ⊢⋆ Δ → ⟦ c ⟧ᶜ Δ t → ⟦ c ⟧ᶜ Γ t
  subᶜ σ (bind t e) = bind t (sub (shift σ) e)
  subᶜ σ (node es)  = node (subˡ σ es)
  subᶜ σ (some t e) = some t (subᶜ σ e)

  subˡ : ∀ {Γ Δ ts} → Γ ⊢⋆ Δ → All (Tm Δ) ts → All (Tm Γ) ts
  subˡ σ [] = []
  subˡ σ (e ∷ es) = sub σ e ∷ subˡ σ es

_⊢⊢⋆_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Θ → Θ ⊢⋆ Δ → Γ ⊢⋆ Δ
σ ⊢⊢⋆ ∅ = ∅
σ ⊢⊢⋆ (ρ , e) = (σ ⊢⊢⋆ ρ) , sub σ e

open import Relation.Binary.PropositionalEquality
open import Ren.Properties Ty

mutual
  ren-refl : ∀ {Γ t} → (e : Tm Γ t) → ren reflᵣ e ≡ e
  ren-refl (var v)   rewrite renᵛ-refl v = refl
  ren-refl (con i e) rewrite renᶜ-refl e = refl

  renᶜ-refl : ∀ {c Γ t} → (e : ⟦ c ⟧ᶜ Γ t) → renᶜ reflᵣ e ≡ e
  renᶜ-refl (bind t e) rewrite ren-refl e = refl
  renᶜ-refl (some t e) rewrite renᶜ-refl e = refl
  renᶜ-refl (node es)  rewrite renˡ-refl es = refl

  renˡ-refl : ∀ {Γ ts} → (es : All (Tm Γ) ts) → renˡ reflᵣ es ≡ es
  renˡ-refl []       = refl
  renˡ-refl (e ∷ es) = cong₂ _∷_ (ren-refl e) (renˡ-refl es)

mutual
  ren-⊇⊇ : ∀ {Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : Tm Δ t) →
    ren Γ⊇Θ (ren Θ⊇Δ e) ≡ ren (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  ren-⊇⊇ Γ⊇Θ Θ⊇Δ (var v)   rewrite renᵛ-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
  ren-⊇⊇ Γ⊇Θ Θ⊇Δ (con i e) rewrite renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl

  renᶜ-⊇⊇ : ∀ {c Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : ⟦ c ⟧ᶜ Δ t) →
    renᶜ Γ⊇Θ (renᶜ Θ⊇Δ e) ≡ renᶜ (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (bind t e) rewrite ren-⊇⊇ (keep Γ⊇Θ) (keep Θ⊇Δ) e = refl
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (some t e) rewrite renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (node ts)  rewrite renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ ts = refl

  renˡ-⊇⊇ : ∀ {Γ Θ Δ ts} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (es : All (Tm Δ) ts) →
    renˡ Γ⊇Θ (renˡ Θ⊇Δ es) ≡ renˡ (Γ⊇Θ ⊇⊇ Θ⊇Δ) es
  renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ [] = refl
  renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ (e ∷ es) = cong₂ _∷_ (ren-⊇⊇ _ _ e) (renˡ-⊇⊇ _ _ es)

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

mutual
  sub-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : Tm Θ t) →
    sub (σ ⊢⋆⊇ Δ⊇Θ) e ≡ sub σ (ren Δ⊇Θ e)
  sub-⊢⋆⊇ σ Δ⊇Θ (var v)   rewrite subᵛ-⊢⋆⊇ σ Δ⊇Θ v = refl
  sub-⊢⋆⊇ σ Δ⊇Θ (con i e) rewrite subᶜ-⊢⋆⊇ σ Δ⊇Θ e = refl

  subᶜ-⊢⋆⊇ : ∀ {c Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : ⟦ c ⟧ᶜ Θ t) →
    subᶜ (σ ⊢⋆⊇ Δ⊇Θ) e ≡ subᶜ σ (renᶜ Δ⊇Θ e)
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (bind t e) rewrite assocᵣₛᵣ (wk {t}) σ Δ⊇Θ | sub-⊢⋆⊇ (shift σ) (keep Δ⊇Θ) e = refl
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (some u e) rewrite subᶜ-⊢⋆⊇ σ Δ⊇Θ e = refl
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (node es)  rewrite subˡ-⊢⋆⊇ σ Δ⊇Θ es = refl

  subˡ-⊢⋆⊇ : ∀ {Γ Δ Θ ts} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (es : All (Tm Θ) ts) →
    subˡ (σ ⊢⋆⊇ Δ⊇Θ) es ≡ subˡ σ (renˡ Δ⊇Θ es)
  subˡ-⊢⋆⊇ σ Δ⊇Θ []       = refl
  subˡ-⊢⋆⊇ σ Δ⊇Θ (e ∷ es) = cong₂ _∷_ (sub-⊢⋆⊇ _ _ e) (subˡ-⊢⋆⊇ _ _ es)

subᵛ-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (v : Var t Θ) →
  subᵛ (Γ⊇Δ ⊇⊢⋆ σ) v ≡ ren Γ⊇Δ (subᵛ σ v)
subᵛ-⊇⊢⋆ Γ⊇Δ (σ , _) vz     = refl
subᵛ-⊇⊢⋆ Γ⊇Δ (σ , _) (vs v) = subᵛ-⊇⊢⋆ Γ⊇Δ σ v

mutual
  sub-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : Tm Θ t) →
    sub (Γ⊇Δ ⊇⊢⋆ σ) e ≡ ren Γ⊇Δ (sub σ e)
  sub-⊇⊢⋆ σ Δ⊇Θ (var v)   rewrite subᵛ-⊇⊢⋆ σ Δ⊇Θ v = refl
  sub-⊇⊢⋆ σ Δ⊇Θ (con i e) rewrite subᶜ-⊇⊢⋆ σ Δ⊇Θ e = refl

  subᶜ-⊇⊢⋆ : ∀ {c Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : ⟦ c ⟧ᶜ Θ t) →
    subᶜ (Γ⊇Δ ⊇⊢⋆ σ) e ≡ renᶜ Γ⊇Δ (subᶜ σ e)
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (bind t e) rewrite
    assocᵣᵣₛ (wk {t}) Γ⊇Δ σ | refl-⊇⊇ Γ⊇Δ | sym (Γ⊇Δ ⊇⊇-refl) |
    assocᵣᵣₛ (keep Γ⊇Δ) (wk {t}) σ | sym (assocᵣᵣₛ (keep Γ⊇Δ) (wk {t}) σ) |
    Γ⊇Δ ⊇⊇-refl | sub-⊇⊢⋆ (keep Γ⊇Δ) (shift σ) e
    = refl
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (some t e) rewrite subᶜ-⊇⊢⋆ Γ⊇Δ σ e = refl
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (node es)  rewrite subˡ-⊇⊢⋆ Γ⊇Δ σ es = refl

  subˡ-⊇⊢⋆ : ∀ {Γ Δ Θ ts} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (es : All (Tm Θ) ts) →
    subˡ (Γ⊇Δ ⊇⊢⋆ σ) es ≡ renˡ Γ⊇Δ (subˡ σ es)
  subˡ-⊇⊢⋆ Γ⊇Δ σ []       = refl
  subˡ-⊇⊢⋆ Γ⊇Δ σ (e ∷ es) = cong₂ _∷_ (sub-⊇⊢⋆ _ _ e) (subˡ-⊇⊢⋆ _ _ es)

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
subᵛ-refl (vs {u} v) rewrite subᵛ-⊇⊢⋆ (wk {u}) reflₛ v | subᵛ-refl v | renᵛ-refl v = refl

mutual
  sub-refl : ∀ {Γ t} (e : Tm Γ t) → sub reflₛ e ≡ e
  sub-refl (var v)   rewrite subᵛ-refl v = refl
  sub-refl (con i e) rewrite subᶜ-refl e = refl

  subᶜ-refl : ∀ {c Γ t} (e : ⟦ c ⟧ᶜ Γ t) → subᶜ reflₛ e ≡ e
  subᶜ-refl (bind t e) rewrite sub-refl e = refl
  subᶜ-refl (some u e) rewrite subᶜ-refl e = refl
  subᶜ-refl (node es)  rewrite subˡ-refl es = refl

  subˡ-refl : ∀ {Γ ts} (es : All (Tm Γ) ts) → subˡ reflₛ es ≡ es
  subˡ-refl []      = refl
  subˡ-refl (_ ∷ _) = cong₂ _∷_ (sub-refl _) (subˡ-refl _)

subᵛ-⊢⊢⋆  : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (v : Var t Δ) →
  subᵛ (σ ⊢⊢⋆ ρ) v ≡ sub σ (subᵛ ρ v)
subᵛ-⊢⊢⋆ σ (ρ , _) vz     = refl
subᵛ-⊢⊢⋆ σ (ρ , _) (vs v) = subᵛ-⊢⊢⋆ σ ρ v

mutual
  sub-⊢⊢⋆ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : Tm Δ t) →
    sub (σ ⊢⊢⋆ ρ) e ≡ sub σ (sub ρ e)
  sub-⊢⊢⋆ σ ρ (var v)   rewrite subᵛ-⊢⊢⋆ σ ρ v = refl
  sub-⊢⊢⋆ σ ρ (con i e) rewrite subᶜ-⊢⊢⋆ σ ρ e = refl

  subᶜ-⊢⊢⋆ : ∀ {c Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : ⟦ c ⟧ᶜ Δ t) →
    subᶜ (σ ⊢⊢⋆ ρ) e ≡ subᶜ σ (subᶜ ρ e)
  subᶜ-⊢⊢⋆ σ ρ (bind t e) rewrite
    assocᵣₛₛ (wk {t}) σ ρ | sym (cong (_⊢⊢⋆ ρ) ((wk {t} ⊇⊢⋆ σ) ⊢⋆⊇-refl)) |
    sym (assocₛᵣₛ ρ (wk {t}) (shift σ)) | sub-⊢⊢⋆ (shift σ) (shift ρ) e
    = refl
  subᶜ-⊢⊢⋆ σ ρ (some t e) rewrite subᶜ-⊢⊢⋆ σ ρ e = refl
  subᶜ-⊢⊢⋆ σ ρ (node es)  rewrite subˡ-⊢⊢⋆ σ ρ es = refl

  -- -- Is this version clearer?
  -- subᶜ-⊢⊢⋆ σ ρ (bind t e) = cong (bind t) $
  --     cong (λ x → sub₀ (x , var vz) e)
  --         (assocᵣₛₛ (wk {t}) σ ρ
  --       ⟨ trans ⟩
  --         cong (_⊢⊢⋆ ρ) (sym ((wk {t} ⊇⊢⋆ σ) ⊢⋆⊇-refl))
  --       ⟨ trans ⟩
  --         sym (assocₛᵣₛ ρ (wk {t}) (shift σ)))
  --   ⟨ trans ⟩
  --     sub₀-⊢⊢⋆ (shift σ) (shift ρ) e
  --   where
  --     open import Function using (_⟨_⟩_; _$_)

  subˡ-⊢⊢⋆ : ∀ {Γ Δ Θ ts} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (es : All (Tm Δ) ts) →
    subˡ (σ ⊢⊢⋆ ρ) es ≡ subˡ σ (subˡ ρ es)
  subˡ-⊢⊢⋆ σ ρ []       = refl
  subˡ-⊢⊢⋆ σ ρ (e ∷ es) rewrite sub-⊢⊢⋆ σ ρ e | subˡ-⊢⊢⋆ σ ρ es = refl

refl-⊢⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → reflₛ ⊢⊢⋆ σ ≡ σ
refl-⊢⊢⋆ ∅       = refl
refl-⊢⊢⋆ (σ , e) rewrite refl-⊢⊢⋆ σ | sub-refl e = refl

_⊢⊢⋆-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⊢⋆ reflₛ ≡ σ
∅       ⊢⊢⋆-refl = refl
(σ , e) ⊢⊢⋆-refl rewrite assocₛᵣₛ reflₛ wk (σ , e) | σ ⊢⋆⊇-refl | σ ⊢⊢⋆-refl = refl
