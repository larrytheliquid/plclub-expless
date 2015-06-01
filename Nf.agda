module Nf where

----------------------------------------------------------------------

open import Function
open import Data.Empty
open import Data.Unit
open import Relation.Nullary hiding ( ¬_ )
open import Relation.Binary.PropositionalEquality

open import Type

----------------------------------------------------------------------

data Nf (Γ : Ctx) : Type → Set
data Neut (Γ : Ctx) : Type → Set

data Nf Γ where
  `true `false : Nf Γ `Bool
  `λ : ∀{A B} (b : Nf (Γ , A) B) → Nf Γ (A `→ B)
  `neut : ∀{A} → Neut Γ A → Nf Γ A

data Neut Γ where
  `var : ∀{A} (i : Var Γ A) → Neut Γ A
  _`∙_ : ∀{A B} (f : Neut Γ (A `→ B)) (a : Nf Γ A) → Neut Γ B
  `¬_ : (b : Neut Γ `Bool) → Neut Γ `Bool
  _`∧_ : (b : Neut Γ `Bool) (b' : Nf Γ `Bool) → Neut Γ `Bool

----------------------------------------------------------------------

data Env (Φ : Ctx) : Ctx → Set where
  ∅ : Env Φ ∅
  _,_ : ∀{Γ A} → Env Φ Γ → Nf Φ A → Env Φ (Γ , A)

postulate
  lift : ∀{Φ Γ A} → Env Φ Γ → Env (Φ , A) (Γ , A)
  idEnv : ∀{Γ} → Env Γ Γ
  lookup : ∀{Φ Γ A} → Env Φ Γ → Var Γ A → Nf Φ A

----------------------------------------------------------------------

¬_ : ∀{Γ} → Nf Γ `Bool → Nf Γ `Bool
¬ `true = `false
¬ `false = `true
¬ `neut b = `neut (`¬ b)

_∧_ : ∀{Γ} → Nf Γ `Bool → Nf Γ `Bool → Nf Γ `Bool
`true ∧ b' = b'
`false ∧ b' = `false
`neut b ∧ b' = `neut (b `∧ b')

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
hsub : ∀{Φ Γ A} → Env Φ Γ → Nf Γ A → Nf Φ A
hsubᴺ : ∀{Φ Γ A} → Env Φ Γ → Neut Γ A → Nf Φ A

_∙_ : ∀{Γ A B} → Nf Γ (A `→ B) → Nf Γ A → Nf Γ B
`λ b ∙ a = hsub (idEnv , a) b
`neut f ∙ a = `neut (f `∙ a)

hsub σ `true = `true
hsub σ `false = `false
hsub σ (`λ b) = `λ (hsub (lift σ) b)
hsub σ (`neut a) = hsubᴺ σ a

hsubᴺ σ (`var i) = lookup σ i
hsubᴺ σ (f `∙ a) = hsubᴺ σ f ∙ hsub σ a
hsubᴺ σ (`¬ b) = ¬ hsubᴺ σ b
hsubᴺ σ (b `∧ b') = hsubᴺ σ b ∧ hsub σ b'

----------------------------------------------------------------------

data Exp (Γ : Ctx) : Type → Set where
  `λ : ∀{A B} (b : Exp (Γ , A) B) → Exp Γ (A `→ B)
  `var : ∀{A} (i : Var Γ A) → Exp Γ A
  _`∙_ : ∀{A B} (f : Exp Γ (A `→ B)) (a : Exp Γ A) → Exp Γ B

True : Type
True = `Bool

False : Type
False = `Bool

Not : Type
Not = `Bool `→ `Bool

And : Type
And = `Bool `→ `Bool `→ `Bool

Prelude : Ctx
Prelude = ∅ , True , False , Not , And

----------------------------------------------------------------------

true` : Nf ∅ True
true` = `true

false` : Nf ∅ False
false` = `false

¬`_ : Nf ∅ Not
¬`_ = `λ (`neut (`¬ `var here))

_∧`_ : Nf ∅ And
_∧`_ = `λ (`λ (`neut (`var (there here) `∧ `neut (`var here))))

prelude : Env ∅ Prelude
prelude = ∅ , true` , false` , ¬`_ , _∧`_

----------------------------------------------------------------------

norm : ∀{Γ A} → Exp Γ A → Nf Γ A
norm (`λ b) = `λ (norm b)
norm (`var i) = `neut (`var i)
norm (f `∙ a) = norm f ∙ norm a 

delta : ∀{A} → Exp Prelude A → Nf ∅ A
delta = hsub prelude ∘ norm

----------------------------------------------------------------------

