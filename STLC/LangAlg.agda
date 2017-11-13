open import Data.List
import LangAlg.Base

module LangAlg {Ty : Set} (cs : let open LangAlg.Base Ty in List Code) where

open LangAlg.Base Ty public
open import Ren Ty
open import Data.List.All

Tm : Ctx → Ty → Set
Tm = ⟦ cs ⟧

mutual
  ren₀ : ∀ {cs′ Γ Δ t} → Γ ⊇ Δ → ⟦ cs′ ⟧₀ cs Δ t → ⟦ cs′ ⟧₀ cs Γ t
  ren₀ Γ⊇Δ (var v) = var (renᵛ Γ⊇Δ v)
  ren₀ Γ⊇Δ (here e)  = here (renᶜ Γ⊇Δ  e)
  ren₀ Γ⊇Δ (there e) = there (ren₀ Γ⊇Δ e)

  renᶜ : ∀ {c Γ Δ t} → Γ ⊇ Δ → ⟦ c ⟧ᶜ cs Δ t → ⟦ c ⟧ᶜ cs Γ t
  renᶜ {bind wt} Γ⊇Δ (bind t e) = bind t (ren₀ (keep Γ⊇Δ) e)
  renᶜ {node ts wt} {Γ} {Δ} {t} Γ⊇Δ (node es) = node (renˡ Γ⊇Δ es)
  renᶜ {some k} Γ⊇Δ (some t e) = some t (renᶜ Γ⊇Δ e)

  renˡ : ∀ {cs′ Γ Δ ts} → Γ ⊇ Δ → All (⟦ cs′ ⟧₀ cs Δ) ts → All (⟦ cs′ ⟧₀ cs Γ) ts
  renˡ Γ⊇Δ [] = []
  renˡ Γ⊇Δ (e ∷ es) = ren₀ Γ⊇Δ e ∷ renˡ Γ⊇Δ es

ren : ∀ {Γ Δ t} → Γ ⊇ Δ → Tm Δ t → Tm Γ t
ren = ren₀

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
  subᶜ : ∀ {c Γ Δ t} → Γ ⊢⋆ Δ → ⟦ c ⟧ᶜ cs Δ t → ⟦ c ⟧ᶜ cs Γ t

  sub₀ : ∀ {cs′ Γ Δ t} → Γ ⊢⋆ Δ → ⟦ cs′ ⟧₀ cs Δ t → ⟦ cs′ ⟧₀ cs Γ t
  sub₀ σ (var v) = subᵛ σ v
  sub₀ σ (here e)  = here (subᶜ σ  e)
  sub₀ σ (there e) = there (sub₀ σ e)

  subᶜ {bind wt} σ (bind t e) = bind t (sub₀ (shift σ) e)
  subᶜ {node ts wt} {Γ} {Δ} {t} σ (node es) = node (subˡ σ es)
  subᶜ {some k} σ (some t e) = some t (subᶜ σ e)

  subˡ : ∀ {cs′ Γ Δ ts} → Γ ⊢⋆ Δ → All (⟦ cs′ ⟧₀ cs Δ) ts → All (⟦ cs′ ⟧₀ cs Γ) ts
  subˡ σ [] = []
  subˡ σ (e ∷ es) = sub₀ σ e ∷ subˡ σ es

sub : ∀ {Γ Δ t} → Γ ⊢⋆ Δ → Tm Δ t → Tm Γ t
sub = sub₀

_⊢⊢⋆_ : ∀ {Γ Δ Θ} → Γ ⊢⋆ Θ → Θ ⊢⋆ Δ → Γ ⊢⋆ Δ
σ ⊢⊢⋆ ∅ = ∅
σ ⊢⊢⋆ (ρ , e) = (σ ⊢⊢⋆ ρ) , sub σ e

open import Relation.Binary.PropositionalEquality
open import Ren.Properties Ty

mutual
  ren₀-refl : ∀ {cs′ Γ t} → (e : ⟦ cs′ ⟧₀ cs Γ t) → ren₀ reflᵣ e ≡ e
  ren₀-refl (var v)   rewrite renᵛ-refl v = refl
  ren₀-refl (here e)  rewrite renᶜ-refl e = refl
  ren₀-refl (there e) rewrite ren₀-refl e = refl

  renᶜ-refl : ∀ {c Γ t} → (e : ⟦ c ⟧ᶜ cs Γ t) → renᶜ reflᵣ e ≡ e
  renᶜ-refl (bind t e) rewrite ren₀-refl e = refl
  renᶜ-refl (some t e) rewrite renᶜ-refl e = refl
  renᶜ-refl (node es)  rewrite renˡ-refl es = refl

  renˡ-refl : ∀ {cs′ Γ ts} → (es : All (⟦ cs′ ⟧₀ cs Γ) ts) → renˡ reflᵣ es ≡ es
  renˡ-refl []       = refl
  renˡ-refl (e ∷ es) = cong₂ _∷_ (ren₀-refl e) (renˡ-refl es)

ren-refl : ∀ {Γ t} (e : Tm Γ t) → ren reflᵣ e ≡ e
ren-refl = ren₀-refl

mutual
  ren₀-⊇⊇ : ∀ {cs′ Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : ⟦ cs′ ⟧₀ cs Δ t) →
    ren₀ Γ⊇Θ (ren₀ Θ⊇Δ e) ≡ ren₀ (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  ren₀-⊇⊇ Γ⊇Θ Θ⊇Δ (var v)   rewrite renᵛ-⊇⊇ Γ⊇Θ Θ⊇Δ v = refl
  ren₀-⊇⊇ Γ⊇Θ Θ⊇Δ (here e)  rewrite renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl
  ren₀-⊇⊇ Γ⊇Θ Θ⊇Δ (there e) rewrite ren₀-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl

  renᶜ-⊇⊇ : ∀ {c Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : ⟦ c ⟧ᶜ cs Δ t) →
    renᶜ Γ⊇Θ (renᶜ Θ⊇Δ e) ≡ renᶜ (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (bind t e) rewrite ren₀-⊇⊇ (keep Γ⊇Θ) (keep Θ⊇Δ) e = refl
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (some t e) rewrite renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ e = refl
  renᶜ-⊇⊇ Γ⊇Θ Θ⊇Δ (node ts)  rewrite renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ ts = refl

  renˡ-⊇⊇ : ∀ {cs′ Γ Θ Δ ts} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (es : All (⟦ cs′ ⟧₀ cs Δ) ts) →
    renˡ Γ⊇Θ (renˡ Θ⊇Δ es) ≡ renˡ (Γ⊇Θ ⊇⊇ Θ⊇Δ) es
  renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ [] = refl
  renˡ-⊇⊇ Γ⊇Θ Θ⊇Δ (e ∷ es) = cong₂ _∷_ (ren₀-⊇⊇ _ _ e) (renˡ-⊇⊇ _ _ es)

ren-⊇⊇ : ∀ {Γ Θ Δ t} (Γ⊇Θ : Γ ⊇ Θ) (Θ⊇Δ : Θ ⊇ Δ) (e : Tm Δ t) →
  ren Γ⊇Θ (ren Θ⊇Δ e) ≡ ren (Γ⊇Θ ⊇⊇ Θ⊇Δ) e
ren-⊇⊇ = ren₀-⊇⊇

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
  sub₀-⊢⋆⊇ : ∀ {cs′ Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : ⟦ cs′ ⟧₀ cs Θ t) →
    sub₀ (σ ⊢⋆⊇ Δ⊇Θ) e ≡ sub₀ σ (ren₀ Δ⊇Θ e)
  sub₀-⊢⋆⊇ σ Δ⊇Θ (var v)   rewrite subᵛ-⊢⋆⊇ σ Δ⊇Θ v = refl
  sub₀-⊢⋆⊇ σ Δ⊇Θ (here e)  rewrite subᶜ-⊢⋆⊇ σ Δ⊇Θ e = refl
  sub₀-⊢⋆⊇ σ Δ⊇Θ (there e) rewrite sub₀-⊢⋆⊇ σ Δ⊇Θ e = refl

  subᶜ-⊢⋆⊇ : ∀ {c Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : ⟦ c ⟧ᶜ cs Θ t) →
    subᶜ (σ ⊢⋆⊇ Δ⊇Θ) e ≡ subᶜ σ (renᶜ Δ⊇Θ e)
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (bind t e) rewrite assocᵣₛᵣ (wk {t}) σ Δ⊇Θ | sub₀-⊢⋆⊇ (shift σ) (keep Δ⊇Θ) e = refl
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (some u e) rewrite subᶜ-⊢⋆⊇ σ Δ⊇Θ e = refl
  subᶜ-⊢⋆⊇ σ Δ⊇Θ (node es)  rewrite subˡ-⊢⋆⊇ σ Δ⊇Θ es = refl

  subˡ-⊢⋆⊇ : ∀ {cs′ Γ Δ Θ ts} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (es : All (⟦ cs′ ⟧₀ cs Θ) ts) →
    subˡ (σ ⊢⋆⊇ Δ⊇Θ) es ≡ subˡ σ (renˡ Δ⊇Θ es)
  subˡ-⊢⋆⊇ σ Δ⊇Θ []       = refl
  subˡ-⊢⋆⊇ σ Δ⊇Θ (e ∷ es) = cong₂ _∷_ (sub₀-⊢⋆⊇ _ _ e) (subˡ-⊢⋆⊇ _ _ es)

sub-⊢⋆⊇ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Δ) (Δ⊇Θ : Δ ⊇ Θ) (e : Tm Θ t) →
  sub (σ ⊢⋆⊇ Δ⊇Θ) e ≡ sub σ (ren Δ⊇Θ e)
sub-⊢⋆⊇ = sub₀-⊢⋆⊇

subᵛ-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (v : Var t Θ) →
  subᵛ (Γ⊇Δ ⊇⊢⋆ σ) v ≡ ren Γ⊇Δ (subᵛ σ v)
subᵛ-⊇⊢⋆ Γ⊇Δ (σ , _) vz     = refl
subᵛ-⊇⊢⋆ Γ⊇Δ (σ , _) (vs v) = subᵛ-⊇⊢⋆ Γ⊇Δ σ v

mutual
  sub₀-⊇⊢⋆ : ∀ {cs′ Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : ⟦ cs′ ⟧₀ cs Θ t) →
    sub₀ (Γ⊇Δ ⊇⊢⋆ σ) e ≡ ren₀ Γ⊇Δ (sub₀ σ e)
  sub₀-⊇⊢⋆ σ Δ⊇Θ (var v)   rewrite subᵛ-⊇⊢⋆ σ Δ⊇Θ v = refl
  sub₀-⊇⊢⋆ σ Δ⊇Θ (here e)  rewrite subᶜ-⊇⊢⋆ σ Δ⊇Θ e = refl
  sub₀-⊇⊢⋆ σ Δ⊇Θ (there e) rewrite sub₀-⊇⊢⋆ σ Δ⊇Θ e = refl

  subᶜ-⊇⊢⋆ : ∀ {c Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : ⟦ c ⟧ᶜ cs Θ t) →
    subᶜ (Γ⊇Δ ⊇⊢⋆ σ) e ≡ renᶜ Γ⊇Δ (subᶜ σ e)
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (bind t e) rewrite
    assocᵣᵣₛ (wk {t}) Γ⊇Δ σ | refl-⊇⊇ Γ⊇Δ | sym (Γ⊇Δ ⊇⊇-refl) |
    assocᵣᵣₛ (keep Γ⊇Δ) (wk {t}) σ | sym (assocᵣᵣₛ (keep Γ⊇Δ) (wk {t}) σ) |
    Γ⊇Δ ⊇⊇-refl | sub₀-⊇⊢⋆ (keep Γ⊇Δ) (shift σ) e
    = refl
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (some t e) rewrite subᶜ-⊇⊢⋆ Γ⊇Δ σ e = refl
  subᶜ-⊇⊢⋆ Γ⊇Δ σ (node es)  rewrite subˡ-⊇⊢⋆ Γ⊇Δ σ es = refl

  subˡ-⊇⊢⋆ : ∀ {cs′ Γ Δ Θ ts} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (es : All (⟦ cs′ ⟧₀ cs Θ) ts) →
    subˡ (Γ⊇Δ ⊇⊢⋆ σ) es ≡ renˡ Γ⊇Δ (subˡ σ es)
  subˡ-⊇⊢⋆ Γ⊇Δ σ []       = refl
  subˡ-⊇⊢⋆ Γ⊇Δ σ (e ∷ es) = cong₂ _∷_ (sub₀-⊇⊢⋆ _ _ e) (subˡ-⊇⊢⋆ _ _ es)

sub-⊇⊢⋆ : ∀ {Γ Δ Θ t} (Γ⊇Δ : Γ ⊇ Δ) (σ : Δ ⊢⋆ Θ) (e : Tm Θ t) →
  sub (Γ⊇Δ ⊇⊢⋆ σ) e ≡ ren Γ⊇Δ (sub σ e)
sub-⊇⊢⋆ = sub₀-⊇⊢⋆

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
  sub₀-refl : ∀ {cs′ Γ t} (e : ⟦ cs′ ⟧₀ cs Γ t) → sub₀ reflₛ e ≡ e
  sub₀-refl (var v)   rewrite subᵛ-refl v = refl
  sub₀-refl (here e)  rewrite subᶜ-refl e = refl
  sub₀-refl (there e) rewrite sub₀-refl e = refl

  subᶜ-refl : ∀ {c Γ t} (e : ⟦ c ⟧ᶜ cs Γ t) → subᶜ reflₛ e ≡ e
  subᶜ-refl (bind t e) rewrite sub₀-refl e = refl
  subᶜ-refl (some u e) rewrite subᶜ-refl e = refl
  subᶜ-refl (node es)  rewrite subˡ-refl es = refl

  subˡ-refl : ∀ {cs′ Γ ts} (es : All (⟦ cs′ ⟧₀ cs Γ) ts) → subˡ reflₛ es ≡ es
  subˡ-refl []      = refl
  subˡ-refl (_ ∷ _) = cong₂ _∷_ (sub₀-refl _) (subˡ-refl _)

sub-refl : ∀ {Γ t} (e : Tm Γ t) → sub reflₛ e ≡ e
sub-refl = sub₀-refl

subᵛ-⊢⊢⋆  : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (v : Var t Δ) →
  subᵛ (σ ⊢⊢⋆ ρ) v ≡ sub σ (subᵛ ρ v)
subᵛ-⊢⊢⋆ σ (ρ , _) vz     = refl
subᵛ-⊢⊢⋆ σ (ρ , _) (vs v) = subᵛ-⊢⊢⋆ σ ρ v

mutual
  sub₀-⊢⊢⋆ : ∀ {cs′ Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : ⟦ cs′ ⟧₀ cs Δ t) →
    sub₀ (σ ⊢⊢⋆ ρ) e ≡ sub₀ σ (sub₀ ρ e)
  sub₀-⊢⊢⋆ σ ρ (var v)   rewrite subᵛ-⊢⊢⋆ σ ρ v = refl
  sub₀-⊢⊢⋆ σ ρ (here e)  rewrite subᶜ-⊢⊢⋆ σ ρ e = refl
  sub₀-⊢⊢⋆ σ ρ (there e) rewrite sub₀-⊢⊢⋆ σ ρ e = refl

  subᶜ-⊢⊢⋆ : ∀ {c Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : ⟦ c ⟧ᶜ cs Δ t) →
    subᶜ (σ ⊢⊢⋆ ρ) e ≡ subᶜ σ (subᶜ ρ e)
  subᶜ-⊢⊢⋆ σ ρ (bind t e) rewrite
    assocᵣₛₛ (wk {t}) σ ρ | sym (cong (_⊢⊢⋆ ρ) ((wk {t} ⊇⊢⋆ σ) ⊢⋆⊇-refl)) |
    sym (assocₛᵣₛ ρ (wk {t}) (shift σ)) | sub₀-⊢⊢⋆ (shift σ) (shift ρ) e
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

  subˡ-⊢⊢⋆ : ∀ {cs′ Γ Δ Θ ts} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (es : All (⟦ cs′ ⟧₀ cs Δ) ts) →
    subˡ (σ ⊢⊢⋆ ρ) es ≡ subˡ σ (subˡ ρ es)
  subˡ-⊢⊢⋆ σ ρ []       = refl
  subˡ-⊢⊢⋆ σ ρ (e ∷ es) rewrite sub₀-⊢⊢⋆ σ ρ e | subˡ-⊢⊢⋆ σ ρ es = refl

sub-⊢⊢⋆ : ∀ {Γ Δ Θ t} (σ : Γ ⊢⋆ Θ) (ρ : Θ ⊢⋆ Δ) (e : Tm Δ t) →
  sub (σ ⊢⊢⋆ ρ) e ≡ sub σ (sub ρ e)
sub-⊢⊢⋆ = sub₀-⊢⊢⋆

refl-⊢⊢⋆_ : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → reflₛ ⊢⊢⋆ σ ≡ σ
refl-⊢⊢⋆ ∅       = refl
refl-⊢⊢⋆ (σ , e) rewrite refl-⊢⊢⋆ σ | sub-refl e = refl

_⊢⊢⋆-refl : ∀ {Γ Δ} (σ : Γ ⊢⋆ Δ) → σ ⊢⊢⋆ reflₛ ≡ σ
∅       ⊢⊢⋆-refl = refl
(σ , e) ⊢⊢⋆-refl rewrite assocₛᵣₛ reflₛ wk (σ , e) | σ ⊢⋆⊇-refl | σ ⊢⊢⋆-refl = refl
