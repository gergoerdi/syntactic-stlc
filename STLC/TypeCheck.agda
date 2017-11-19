module TypeCheck where

open import Ty
open import Raw
open import Tm

open import Data.Maybe
open import Function
open import Data.String
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Level renaming (zero to lzero)
open import Category.Monad

▷-injₗ : ∀ {t t′ u u′} → (t ▷ t′) ≡ (u ▷ u′) → t ≡ u
▷-injₗ refl = refl

▷-injᵣ : ∀ {t t′ u u′} → (t ▷ t′) ≡ (u ▷ u′) → t′ ≡ u′
▷-injᵣ refl = refl

_≟ₜ_ : Decidable (_≡_ {A = Ty})
∙        ≟ₜ ∙          = yes refl
∙        ≟ₜ (_ ▷ _)    = no (λ ())
∙        ≟ₜ Bool       = no (λ ())
(_ ▷ _)  ≟ₜ ∙          = no (λ ())
(t ▷ t′) ≟ₜ (u ▷ u′)   with t ≟ₜ u | t′ ≟ₜ u′
(t ▷ t′) ≟ₜ (.t ▷ .t′) | yes refl | yes refl = yes refl
(t ▷ t′) ≟ₜ (u ▷ u′)   | _ | no ¬p = no (¬p ∘ ▷-injᵣ)
(t ▷ t′) ≟ₜ (u ▷ u′)   | no ¬p | _ = no (¬p ∘ ▷-injₗ)
(_ ▷ _)  ≟ₜ Bool       = no (λ ())
Bool     ≟ₜ ∙          = no (λ ())
Bool     ≟ₜ (u ▷ u₁)   = no (λ ())
Bool     ≟ₜ Bool       = yes refl

data Scope : Ctx → Set where
  ∅ : Scope ∅
  _,_ : ∀ {t Γ} → Scope Γ → Name → Scope (Γ , t)

lookup : ∀ {Γ} → Name → Scope Γ → Maybe (∃ λ t → Var t Γ)
lookup n ∅        = nothing
lookup n (Σ , n′) with n ≟ n′
lookup n (Σ , .n) | yes refl = just (, vz)
lookup n (Σ , n′) | no ¬p = nothing

open RawMonad (Data.Maybe.monad {lzero})

typeCheck : ∀ {Γ} → Scope Γ → Expr → Maybe (∃ (Tm Γ))
typeCheck ν (var n) =  Data.Product.map _ var <$> lookup n ν
typeCheck ν (lam (n ∶ t) e) = Data.Product.map _ (lam t) <$> typeCheck (ν , n) e
typeCheck ν (f · e) =
  typeCheck ν e        >>= λ { (u , e′) →
  typeCheck ν f        >>= λ { (u′ ▷ t , f′) →
  decToMaybe (u ≟ₜ u′) >>= λ { refl →
  pure (, (f′ · e′)) };
  _ → nothing }}
typeCheck ν true = pure (, true)
typeCheck ν false = pure (, false)
typeCheck ν (if b then thn else els) =
  typeCheck ν b           >>= λ { (t₀ , b′) →
  decToMaybe (t₀ ≟ₜ Bool) >>= λ { refl →
  typeCheck ν thn         >>= λ { (t , thn′) →
  typeCheck ν els         >>= λ { (t′ , els′) →
  decToMaybe (t ≟ₜ t′)    >>= λ { refl →
  pure (, (if b′ then thn′ else els′))}}}}}

ex₁ : Tm ∅ (∙ ▷ ∙)
ex₁ = proj₂ (from-just (typeCheck ∅ (lam ("x" ∶ ∙) (var "x"))))
