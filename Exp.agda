module Exp where

----------------------------------------------------------------------

open import Function
open import Type

----------------------------------------------------------------------

data Exp (Γ : Ctx) : Type → Set where
  `true `false : Exp Γ `Bool
  `λ : ∀{A B} (b : Exp (Γ , A) B) → Exp Γ (A `→ B)
  `var : ∀{A} (i : Var Γ A) → Exp Γ A
  _`∙_ : ∀{A B} (f : Exp Γ (A `→ B)) (a : Exp Γ A) → Exp Γ B
  `¬_ : (b : Exp Γ `Bool) → Exp Γ `Bool
  _`∧_ : (b : Exp Γ `Bool) (b' : Exp Γ `Bool) → Exp Γ `Bool

----------------------------------------------------------------------

postulate
  sub : ∀{Γ A B} → Exp Γ A → Exp (Γ , A) B → Exp Γ B

¬_ : ∀{Γ} → Exp Γ `Bool → Exp Γ `Bool
¬ `true = `false
¬ `false = `true
¬ b = `¬ b

_∧_ : ∀{Γ} → Exp Γ `Bool → Exp Γ `Bool → Exp Γ `Bool
`true ∧ b' = b'
`false ∧ b' = `false
b ∧ b' = b `∧ b'

----------------------------------------------------------------------

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
norm (`¬ b) = ¬ norm b
norm (b `∧ b') = norm b ∧ norm b'

----------------------------------------------------------------------
