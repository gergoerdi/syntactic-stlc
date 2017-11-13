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
open import LangAlg.Base Ty
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

open import LangAlg STLC
open import Ren Ty
open import Data.Fin using (#_)

-- Tm : Ctx → Ty → Set
-- Tm = ⟦ STLC ⟧

[var] : ∀ {t Γ} → Var t Γ → Tm Γ t
[var] = var

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

-- -- This would not be strictly positive!
-- data Saturated : ∀ {Γ t} → Tm Γ t → Set where
--   fun : ∀ {t u} {f : Tm ∅ (t ▷ u)} → Halts f → (∀ {e} → Saturated e → Saturated (f · e)) → Saturated f

mutual
  Saturated : ∀ {t} → Tm ∅ t → Set
  Saturated e = Halts e × Saturated′ _ e

  Saturated′ : ∀ t → Tm ∅ t → Set
  Saturated′ ∙ _ = ⊥
  Saturated′ (t ▷ u) f = ∀ {e} → Saturated e → Saturated (f [·] e)
  Saturated′ Bool _ = ⊤
  Saturated′ (t [×] u) e = ⊥ -- TODO

saturated⇒halts : ∀ {t e} → Saturated {t} e → Halts e
saturated⇒halts = proj₁

step‿preserves‿halting : ∀ {Γ t} {e e′ : Tm Γ t} → e ==> e′ → Halts e ⇔ Halts e′
step‿preserves‿halting {e = e} {e′ = e′} step = equivalence fwd bwd
  where
    fwd : Halts e → Halts e′
    fwd (e″ , ε , v) = ⊥-elim (value⇒normal v (, step ))
    fwd (e″ , s ◅ steps , v) rewrite deterministic step s = e″ , steps , v

    bwd : Halts e′ → Halts e
    bwd (e″ , steps , v) = e″ , step ◅ steps , v

step‿preserves‿saturated : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e ⇔ Saturated e′
step‿preserves‿saturated step = equivalence (fwd step) (bwd step)
  where
    fwd : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e → Saturated e′
    fwd {∙}       step (halts , ())
    fwd {u ▷ t}   step (halts , sat) = Equivalence.to (step‿preserves‿halting step) ⟨$⟩ halts , λ e → fwd (appˡ step _) (sat e)
    fwd {Bool}    step (halts , _) = Equivalence.to (step‿preserves‿halting step) ⟨$⟩ halts , _
    fwd {t [×] u} step (halts , ()) -- TODO

    bwd : ∀ {t} {e e′ : Tm _ t} → e ==> e′ → Saturated e′ → Saturated e
    bwd {∙}       step (halts , ())
    bwd {u ▷ t}   step (halts , sat) = Equivalence.from (step‿preserves‿halting step) ⟨$⟩ halts , λ e → bwd (appˡ step _) (sat e)
    bwd {Bool}    step (halts , _) =  Equivalence.from (step‿preserves‿halting step) ⟨$⟩ halts , _
    bwd {t [×] u} step (halts , ()) -- TODO

step*‿preserves‿saturated : ∀ {t} {e e′ : Tm _ t} → e ==>* e′ → Saturated e ⇔ Saturated e′
step*‿preserves‿saturated ε = id
step*‿preserves‿saturated (step ◅ steps) = step*‿preserves‿saturated steps ∘ step‿preserves‿saturated step

data Instantiation : ∀ {Γ} → ∅ ⊢⋆ Γ → Set where
  ∅ : Instantiation ∅
  _,_ : ∀ {Γ t σ} → Instantiation {Γ} σ → ∀ {e} → Value {_} {t} e × Saturated e → Instantiation (σ , e)

saturateᵛ : ∀ {Γ σ} → Instantiation σ → ∀ {t} (x : Var t Γ) → Saturated (subᵛ σ x)
saturateᵛ (_ , (_ , sat)) vz = sat
saturateᵛ (env , _) (vs x) = saturateᵛ env x

app-lam* : ∀ {Γ t} {e e′ : Tm Γ t} → e ==>* e′ → Value e′ → ∀ {u} (f : Tm _ u) → ([lam] t f [·] e) ==>* sub (reflₛ , e′) f
app-lam* steps v f = gmap _ (appʳ (lam _ _)) steps  ◅◅ app-lam f v ◅ ε

if-cond* : ∀ {Γ t} {b b′ : Tm Γ _} → b ==>* b′ → ∀ (thn els : Tm Γ t) →
  ([if] b [then] thn [else] els) ==>* ([if] b′ [then] thn [else] els)
if-cond* steps thn els = gmap _ (λ step → if-cond step thn els) steps

-- What is a good name for this?
-- It basically states that you can push in outer arguments before the innermost one.
-- Should this be called some kind of constant propagation?
innermost‿last : ∀ {Γ u} (σ : ∅ ⊢⋆ Γ) (e′ : Tm ∅ u) →
  (∅ , e′) ⊢⊢⋆ (wk ⊇⊢⋆ σ) ≡ σ
innermost‿last ∅       e′ = refl
innermost‿last (σ , e) e′ rewrite innermost‿last σ e′ | sym (sub-⊢⋆⊇ (∅ , e′) wk e) | sub-refl e = refl

-- saturate : ∀ {Γ σ} → Instantiation σ → ∀ {t} → (e : Tm Γ t) → Saturated (sub σ e)
-- saturate         env          (var v)                  = saturateᵛ env v
-- saturate         env          (f · e)                  with saturate env f | saturate env e
-- saturate         env          (f · e) | _ , sat-f | sat-e = sat-f sat-e
-- saturate         env          true                     = (true , ε , true) , _
-- saturate         env          false                    = (false , ε , false) , _
-- saturate         env          (if b then thn else els) with saturate env b
-- saturate {Γ} {σ} env (if b then thn else els) | (_ , b-steps , true) , _ =
--   Equivalence.from (step*‿preserves‿saturated (if-cond* b-steps _ _ ◅◅ (if-true _ _ ◅ ε))) ⟨$⟩ saturate env thn
-- saturate         env (if b then thn else els) | (_ , b-steps , false) , _ =
--   Equivalence.from (step*‿preserves‿saturated (if-cond* b-steps _ _ ◅◅ (if-false _ _ ◅ ε))) ⟨$⟩ saturate env els
-- saturate {Γ} {σ} env {.u ▷ t} (lam u f) = value⇒halts (lam u (sub (shift σ) f)) , sat-f
--   where
--     f′ = sub (shift σ) f

--     sat-f : ∀ {e : Tm _ u} → Saturated e → Saturated (lam u f′ · e)
--     sat-f {e} sat-e@((e′ , steps , v) , _) = Equivalence.from (step*‿preserves‿saturated f‿e==>f←σe) ⟨$⟩ sat
--       where
--         f←σe = sub (σ , e′) f
--         f′‿e = lam u f′ · e

--         sat-e′ : Saturated e′
--         sat-e′ = Equivalence.to (step*‿preserves‿saturated steps) ⟨$⟩ sat-e

--         sat : Saturated f←σe
--         sat = saturate (env , (v , sat-e′)) f

--         f‿e==>f←σe : f′‿e ==>* f←σe
--         f‿e==>f←σe = subst (λ f₀ → _ ==>* f₀) lemma (app-lam* steps v (sub (shift σ) f))
--           where
--             lemma : sub (∅ , e′) (sub (shift σ) f) ≡ sub (σ , e′) f
--             lemma rewrite sym (sub-⊢⊢⋆ (∅ , e′) (shift σ) f) | innermost‿last σ e′ = refl

-- normalization : ∀ {t} → (e : Tm ∅ t) → Halts e
-- normalization e rewrite sym (sub-refl e) = saturated⇒halts (saturate ∅ e)
