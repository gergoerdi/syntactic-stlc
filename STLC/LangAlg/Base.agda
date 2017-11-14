import LangAlg.Code
open import Data.Vec

module LangAlg.Base {n} {Ty : Set} (codes : Vec (LangAlg.Code.Code Ty) n) where

open import Data.List.All hiding (lookup)
open LangAlg.Code Ty
open import Ctx Ty public
open import Data.Fin

mutual
  data Tm (Γ : Ctx) : Ty → Set where
    var : ∀ {t} → Var t Γ → Tm Γ t
    con : ∀ {t} (i : Fin n) → ⟦ lookup i codes ⟧ᶜ Γ t → Tm Γ t

  data ⟦_⟧ᶜ : Code → Ctx → Ty → Set where
    bind : ∀ {Γ t₀ wt} t {u} →  Tm  (Γ , t) u  → {{_ : wt t u t₀}} → ⟦ bind wt ⟧ᶜ Γ t₀
    some : ∀ {c Γ t} u → ⟦ c u ⟧ᶜ Γ t → ⟦ some c ⟧ᶜ Γ t
    node : ∀ {Γ t ts wt} →  All (Tm Γ) ts → {{_ : wt t}} → ⟦ node ts wt ⟧ᶜ Γ t
