module WExp where

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
whnf (`if b `then ct `else cf) = if whnf b then whnf ct else whnf cf

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
force : ∀{Γ A} → Exp Γ A → Exp Γ A -- WHNF as input
force `true = `true
force `false = `false
force (`λ b) = `λ (force (whnf b))
force (`var i) = `var i
force (f `∙ a) = force f `∙ force a
force (`if b `then ct `else cf) = `if force b `then force ct `else force cf

----------------------------------------------------------------------

norm : ∀{Γ A} → Exp Γ A → Exp Γ A
norm = force ∘ whnf

----------------------------------------------------------------------
