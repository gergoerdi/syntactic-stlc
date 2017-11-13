module LangAlg.Base (Ty : Set) where

open import Data.List
open import Data.List.All

open import Ctx Ty public
open import Function using (_∘_)

data Code : Set₁ where
  bind : (Ty → Ty → Ty → Set) → Code
  some : (Ty → Code) → Code
  node : List Ty → (Ty → Set) → Code

mutual
  data ⟦_⟧ᶜ : Code → List Code → Ctx → Ty → Set where
    bind : ∀ {cs Γ t₀ wt} t {u} → ⟦ cs ⟧₀ cs (Γ , t) u → {{_ : wt t u t₀}} → ⟦ bind wt ⟧ᶜ cs Γ t₀
    some : ∀ {cs Γ t c} u → ⟦ c u ⟧ᶜ cs Γ t → ⟦ some c ⟧ᶜ cs Γ t
    node : ∀ {cs Γ t ts wt} → All (⟦ cs ⟧₀ cs Γ) ts → {{_ : wt t}} → ⟦ node ts wt ⟧ᶜ cs Γ t

  data ⟦_⟧₀ : List Code → List Code → Ctx → Ty → Set where
    var : ∀ {cs Γ t} → Var t Γ → ⟦ cs ⟧₀ cs Γ t
    here : ∀ {c cs cs₀ Γ t} → ⟦ c ⟧ᶜ cs₀ Γ t → ⟦ c ∷ cs ⟧₀ cs₀ Γ t
    there : ∀ {c cs cs₀ Γ t} → ⟦ cs ⟧₀ cs₀ Γ t → ⟦ c ∷ cs ⟧₀ cs₀ Γ t

⟦_⟧ : List Code → Ctx → Ty → Set
⟦ cs ⟧ = ⟦ cs ⟧₀ cs

open import Data.Fin
open import Data.Vec renaming (lookup to vlookup) using (fromList)

con : ∀ {cs cs₀ Γ t} → (i : Fin (length cs)) → ⟦ vlookup i (fromList cs) ⟧ᶜ cs₀ Γ t → ⟦ cs ⟧₀ cs₀ Γ t
con {[]} ()
con {c ∷ cs} zero    = here
con {c ∷ cs} (suc i) = there ∘ con i

