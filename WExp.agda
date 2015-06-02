module WExp where

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
whnf : ∀{Γ A} → Exp Γ A → Exp Γ A

_∙_ : ∀{Γ A B} → Exp Γ (A `→ B) → Exp Γ A → Exp Γ B
`λ b ∙ a = whnf (sub a b)
f ∙ a = f `∙ a

whnf `true = `true
whnf `false = `false
whnf (`λ b) = `λ b
whnf (`var i) = `var i
whnf (f `∙ a) = whnf f ∙ whnf a
whnf (`¬ b) = ¬ whnf b
whnf (b `∧ b') = whnf b ∧ whnf b'

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
force : ∀{Γ A} → Exp Γ A → Exp Γ A -- WHNF as input
force `true = `true
force `false = `false
force (`λ b) = `λ (force (whnf b))
force (`var i) = `var i
force (f `∙ a) = force f `∙ force a
force (`¬ b) = `¬ force b
force (b `∧ b') = force b `∧ force b'

----------------------------------------------------------------------

norm : ∀{Γ A} → Exp Γ A → Exp Γ A
norm = force ∘ whnf

----------------------------------------------------------------------
