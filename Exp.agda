module Exp where

----------------------------------------------------------------------

open import Function
open import Data.Nat
open import Data.Fin hiding ( lift ) renaming ( Fin to Var; zero to here; suc to there )
open import Relation.Nullary.Decidable using ( True )
open import Data.Vec

open import Prelude

----------------------------------------------------------------------

data Exp (γ : ℕ) : Set where
  `Type : Exp γ
  `Π : (A : Exp γ) (B : Bind Exp γ) → Exp γ
  `λ : (b : Bind Exp γ) → Exp γ
  `var : (i : Var γ) → Exp γ
  _`∙_ : (f : Exp γ) (a : Exp γ) → Exp γ

----------------------------------------------------------------------

postulate sub : ∀{γ} → Exp γ → Bind Exp γ → Exp γ

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
norm : ∀{γ} → Exp γ → Exp γ

normᴮ : ∀{γ} → Bind Exp γ → Bind Exp γ
normᴮ `∣ b ∣ = `∣ norm b ∣

_∙_ : ∀{γ} → Exp γ → Exp γ → Exp γ
`λ b ∙ a = norm (sub a b)
f ∙ a = f `∙ a

norm `Type = `Type
norm (`Π A B) = `Π (norm A) (normᴮ B)
norm (`λ b) = `λ (normᴮ b)
norm (`var i) = `var i
norm (f `∙ a) = norm f ∙ norm a

----------------------------------------------------------------------
