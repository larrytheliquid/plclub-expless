module Exp where

----------------------------------------------------------------------

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Type

----------------------------------------------------------------------

data Exp (Γ : Ctx) : Type → Set where
  `true `false : Exp Γ `Bool
  `λ : ∀{A B} (b : Exp (Γ , A) B) → Exp Γ (A `→ B)
  `var : ∀{A} (i : Var Γ A) → Exp Γ A
  _`∙_ : ∀{A B} (f : Exp Γ (A `→ B)) (a : Exp Γ A) → Exp Γ B
  `if_`then_`else_ : ∀{C} (b : Exp Γ `Bool) (ct cf : Exp Γ C) → Exp Γ C

----------------------------------------------------------------------

postulate
  sub : ∀{Γ A B} → Exp Γ A → Exp (Γ , A) B → Exp Γ B

if_then_else_ : ∀{Γ C} → Exp Γ `Bool → Exp Γ C → Exp Γ C → Exp Γ C
if `true then ct else cf = ct
if `false then ct else cf = cf
if b then ct else cf = `if b `then ct `else cf

{-# NO_TERMINATION_CHECK #-}
norm : ∀{Γ A} → Exp Γ A → Exp Γ A

_∙_ : ∀{Γ A B} → Exp Γ (A `→ B) → Exp Γ A → Exp Γ B
`λ b ∙ a = norm (sub a b)
f ∙ a = f `∙ a

norm `true = `true
norm `false = `false
norm (`λ b) = `λ (norm b)
norm (`var i) = `var i
norm (f `∙ a) = norm f ∙ norm a
norm (`if b `then ct `else cf) = if norm b then norm ct else norm cf

----------------------------------------------------------------------
