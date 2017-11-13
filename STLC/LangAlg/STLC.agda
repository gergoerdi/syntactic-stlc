module LangAlg.STLC where

open import Data.List
open import Data.List.All
open import Data.Unit

infixr 20 _▷_
data Ty : Set where
  ∙   : Ty
  _▷_ : Ty → Ty → Ty
  Bool : Ty
  _[×]_ : Ty → Ty → Ty

open import Data.Vec
import LangAlg Ty as LA
open LA
open import Function using (_$_; _∘′_)
open import Relation.Binary.PropositionalEquality

STLC : List Code
STLC =
  bind (λ t u → t ▷ u ≡_) ∷
  some (λ u → some (λ t → node ((u ▷ t) ∷ u ∷ []) (t ≡_))) ∷
  node [] (Bool ≡_) ∷
  node [] (Bool ≡_) ∷
  some (λ t → node (Bool ∷ t ∷ t ∷ []) (t ≡_)) ∷
  some (λ t → some (λ u → node (t ∷ u ∷ []) (t [×] u ≡_))) ∷
  some (λ t → some (λ u → node (t [×] u ∷ []) (t ≡_))) ∷
  some (λ t → some (λ u → node (t [×] u ∷ []) (u ≡_))) ∷
  []

open LA.Sub STLC
open import Data.Fin using (#_)

-- Tm : Ctx → Ty → Set
-- Tm = ⟦ STLC ⟧

[var] : ∀ {t Γ} → Var t Γ → Tm Γ t
[var] v = var v

[lam] : ∀ {u Γ} t → Tm (Γ , t) u → Tm Γ (t ▷ u)
[lam] t e = con (# 0) $ bind t e

_[·]_ : ∀ {u t Γ} → Tm Γ (u ▷ t) → Tm Γ u → Tm Γ t
_[·]_ {u} {t} f e = con (# 1) $ some u (some t (node (f ∷ e ∷ [])))

[true] : ∀ {Γ} → Tm Γ Bool
[true] = con (# 2) $ node []

[false] : ∀ {Γ} → Tm Γ Bool
[false] = con (# 3) $ node []

[if]_[then]_[else]_ : ∀ {t Γ} → Tm Γ Bool → Tm Γ t → Tm Γ t → Tm Γ t
[if]_[then]_[else]_ {t} b thn els = con (# 4) $ some t (node (b ∷ thn ∷ els ∷ []))

_[,]_ : ∀ {t u Γ} → Tm Γ t → Tm Γ u → Tm Γ (t [×] u)
_[,]_ {t} {u} e₁ e₂ = con (# 5) $ some t (some u (node (e₁ ∷ e₂ ∷ [])))

[fst] :  ∀ {t u Γ} → Tm Γ (t [×] u) → Tm Γ t
[fst] {t} {u} e = con (# 6) $ some t (some u (node (e ∷ [])))

[snd] :  ∀ {t u Γ} → Tm Γ (t [×] u) → Tm Γ u
[snd] {t} {u} e = con (# 7) $ some t (some u (node (e ∷ [])))

ID : ∀ {Γ} t → Tm Γ (t ▷ t)
ID t = [lam] t $ [var] vz

CONST : ∀ {Γ} t u → Tm Γ (t ▷ u ▷ t)
CONST t u = [lam] t $ [lam] u $ [var] (vs vz)

CONST‿ID : ∀ {Γ} t u → Tm Γ (u ▷ (t ▷ t))
CONST‿ID t u = CONST (t ▷ t) u [·] ID t

ASSOC : ∀ {Γ} t u s → Tm Γ ((t [×] (u [×] s)) ▷ ((t [×] u) [×] s))
ASSOC t u s = [lam] _ $ ([fst] ([var] vz) [,] [fst] ([snd] ([var] vz))) [,] [snd] ([snd] ([var] vz))

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Relation.Binary
open import Data.Star
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Function.Equivalence hiding (sym)
open import Function.Equality using (_⟨$⟩_)

data Value : {Γ : Ctx} → {t : Ty} → Tm Γ t → Set where
  lam   : ∀ {Γ t} → ∀ u (e : Tm _ t) → Value {Γ} ([lam] u e)
  true  : ∀ {Γ} → Value {Γ} [true]
  false : ∀ {Γ} → Value {Γ} [false]

data _==>_ {Γ} : ∀ {t} → Rel (Tm Γ t) lzero where
  app-lam : ∀ {t u} (f : Tm _ t) {v : Tm _ u} → Value v → ([lam] u f [·] v) ==> sub (reflₛ , v) f
  appˡ : ∀ {t u} {f f′ : Tm Γ (u ▷ t)} → f ==> f′ → (e : Tm Γ u) → (f [·] e) ==> (f′ [·] e)
  appʳ : ∀ {t u} {f} → Value {Γ} {u ▷ t} f → ∀ {e e′ : Tm Γ u} → e ==> e′ → (f [·] e) ==> (f [·] e′)
  if-cond : ∀ {t} {b b′ : Tm Γ _} → b ==> b′ → (thn els : Tm Γ t) → ([if] b [then] thn [else] els) ==> ([if] b′ [then] thn [else] els)
  if-true : ∀ {t} (thn els : Tm _ t) → ([if] [true] [then] thn [else] els) ==> thn
  if-false : ∀ {t} (thn els : Tm _ t) → ([if] [false] [then] thn [else] els) ==> els

_==>*_ : ∀ {Γ t} → Rel (Tm Γ t) _
_==>*_ = Star _==>_

NF : ∀ {a b} {A : Set a} → Rel A b → A → Set _
NF next x = ∄ (next x)

value⇒normal : ∀ {Γ t e} → Value {Γ} {t} e → NF _==>_ e
value⇒normal (lam t e) (_ , ())
value⇒normal true (_ , ())
value⇒normal false (_ , ())

Deterministic : ∀ {a b} {A : Set a} → Rel A b → Set _
Deterministic _∼_ = ∀ {x y y′} → x ∼ y → x ∼ y′ → y ≡ y′

deterministic : ∀ {Γ t} → Deterministic (_==>_ {Γ} {t})
deterministic (app-lam f _) (app-lam ._ _) = refl
deterministic (app-lam f v) (appˡ () _)
deterministic (app-lam f v) (appʳ f′ e) = ⊥-elim (value⇒normal v (, e))
deterministic (appˡ () e) (app-lam f v)
deterministic (appˡ f e) (appˡ f′ ._) rewrite deterministic f f′ = refl
deterministic (appˡ f e) (appʳ f′ _) = ⊥-elim (value⇒normal f′ (, f))
deterministic (appʳ f e) (app-lam f′ v) = ⊥-elim (value⇒normal v (, e))
deterministic (appʳ f e) (appˡ f′ _) = ⊥-elim (value⇒normal f (, f′))
deterministic (appʳ f e) (appʳ f′ e′) rewrite deterministic e e′ = refl
deterministic (if-true thn els) (if-true _ _) = refl
deterministic (if-false thn els) (if-false _ _) = refl
deterministic (if-cond b thn els) (if-cond b′ _ _) rewrite deterministic b b′ = refl
deterministic (if-cond () thn els) (if-true _ _)
deterministic (if-cond () thn els) (if-false _ _)
deterministic (if-true thn els) (if-cond () _ _)
deterministic (if-false thn els) (if-cond () _ _)

Halts : ∀ {Γ t} → Tm Γ t → Set
Halts e = ∃ λ e′ → e ==>* e′ × Value e′

value⇒halts : ∀ {Γ t e} → Value {Γ} {t} e → Halts e
value⇒halts {e = e} v = e , ε , v
