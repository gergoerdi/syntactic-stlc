module Raw where

open import Ty
open import Data.String

Name : Set
Name = String

infix 22 _∶_
data Formal : Set where
  _∶_ : Name → Ty → Formal

infixl 23 _·_
data Expr : Set where
  var : (v : Name) → Expr
  lam : (_ : Formal) (e : Expr) → Expr
  _·_ : (f : Expr) (e : Expr) → Expr

  true false : Expr
  if_then_else_ : (b : Expr) (thn : Expr) (els : Expr) → Expr
