module Nf where

----------------------------------------------------------------------

open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product hiding ( map )
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

data Nf (Γ : Ctx) : Type → Set
data Neut (Γ : Ctx) : Type → Set

data Nf Γ where
  `true `false : Nf Γ `Bool
  `λ : ∀{A B} (b : Nf (Γ , A) B) → Nf Γ (A `→ B)
  `neut : ∀{A} → Neut Γ A → Nf Γ A

data Neut Γ where
  `var : ∀{A} (i : Var Γ A) → Neut Γ A
  _`∙_ : ∀{A B} (f : Neut Γ (A `→ B)) (a : Nf Γ A) → Neut Γ B
  `if_`then_`else_ : ∀{C} (b : Neut Γ `Bool) (ct cf : Nf Γ C) → Neut Γ C

----------------------------------------------------------------------

data Env (Φ : Ctx) : Ctx → Set where
  ∅ : Env Φ ∅
  _,_ : ∀{Γ A} → Env Φ Γ → Nf Φ A → Env Φ (Γ , A)

map : ∀{Φ Δ Γ} → (∀{A} → Nf Φ A → Nf Δ A) → Env Φ Γ → Env Δ Γ
map f ∅ = ∅
map f (σ , a) = map f σ , f a

postulate wkn : ∀{Γ A B} → Nf Γ B → Nf (Γ , A) B

lift : ∀{Φ Γ A} → Env Φ Γ → Env (Φ , A) (Γ , A)
lift σ = map wkn σ , `neut (`var here)

lookup : ∀{Φ Γ A} → Env Φ Γ → Var Γ A → Nf Φ A
lookup (σ , a) here = a
lookup (σ , a) (there i) = lookup σ i

idEnv : ∀{Γ} → Env Γ Γ
idEnv {∅} = ∅
idEnv {Γ , A} = map wkn idEnv , `neut (`var here)

----------------------------------------------------------------------

if_then_else_ : ∀{Γ C} → Nf Γ `Bool → Nf Γ C → Nf Γ C → Nf Γ C
if `true then ct else cf = ct
if `false then ct else cf = cf
if `neut b then ct else cf = `neut (`if b `then cf `else cf)

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
hsubᴺ σ (`if b `then ct `else cf) = if hsubᴺ σ b then hsub σ ct else hsub σ cf

----------------------------------------------------------------------
