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
