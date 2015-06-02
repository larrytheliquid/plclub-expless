module EnvExp where

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
  `¬_ : (b : Exp Γ `Bool) → Exp Γ `Bool
  _`∧_ : (b : Exp Γ `Bool) (b' : Exp Γ `Bool) → Exp Γ `Bool

----------------------------------------------------------------------

data Wh (Γ : Ctx) : Type → Set
data Neut (Γ : Ctx) : Type → Set

data Env (Φ : Ctx) : Ctx → Set where
  ∅ : Env Φ ∅
  _,_ : ∀{Γ A} → Env Φ Γ → Wh Φ A → Env Φ (Γ , A)

data Wh Γ where
  `true `false : Wh Γ `Bool
  `λ : ∀{Φ A B} (σ : Env Φ Γ) (b : Wh (Φ , A) B) → Wh Γ (A `→ B)
  `neut : ∀{A} → Neut Γ A → Wh Γ A

data Neut Γ where
  `var : ∀{A} (i : Var Γ A) → Neut Γ A
  _`∙_ : ∀{A B} (f : Neut Γ (A `→ B)) (a : Wh Γ A) → Neut Γ B
  `¬_ : (b : Neut Γ `Bool) → Neut Γ `Bool
  _`∧_ : (b : Neut Γ `Bool) (b' : Wh Γ `Bool) → Neut Γ `Bool

----------------------------------------------------------------------

-- postulate
--   sub : ∀{Γ A B} → Exp Γ A → Exp (Γ , A) B → Exp Γ B

-- if_then_else_ : ∀{Γ C} → Exp Γ `Bool → Exp Γ C → Exp Γ C → Exp Γ C
-- if `true then ct else cf = ct
-- if `false then ct else cf = cf
-- if b then ct else cf = `if b `then ct `else cf

-- ----------------------------------------------------------------------

-- {-# NO_TERMINATION_CHECK #-}
-- whnf : ∀{Γ A} → Exp Γ A → Exp Γ A

-- _∙_ : ∀{Γ A B} → Exp Γ (A `→ B) → Exp Γ A → Exp Γ B
-- `λ b ∙ a = whnf (sub a b)
-- f ∙ a = f `∙ a

-- whnf `true = `true
-- whnf `false = `false
-- whnf (`λ b) = `λ b
-- whnf (`var i) = `var i
-- whnf (f `∙ a) = whnf f ∙ whnf a
-- whnf (`if b `then ct `else cf) = if whnf b then whnf ct else whnf cf

-- ----------------------------------------------------------------------

-- {-# NO_TERMINATION_CHECK #-}
-- force : ∀{Γ A} → Exp Γ A → Exp Γ A -- WHNF as input
-- force `true = `true
-- force `false = `false
-- force (`λ b) = `λ (force (whnf b))
-- force (`var i) = `var i
-- force (f `∙ a) = force f `∙ force a
-- force (`if b `then ct `else cf) = `if force b `then force ct `else force cf

-- ----------------------------------------------------------------------

-- norm : ∀{Γ A} → Exp Γ A → Exp Γ A
-- norm = force ∘ whnf

-- ----------------------------------------------------------------------
