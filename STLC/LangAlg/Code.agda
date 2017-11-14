module LangAlg.Code (Ty : Set) where

open import Data.List

data Code : Set₁ where
  bind : (Ty → Ty → Ty → Set) → Code
  some : (Ty → Code) → Code
  node : List Ty → (Ty → Set) → Code
