module Nf where

----------------------------------------------------------------------

open import Function
open import Data.Nat
open import Data.Fin hiding ( lift ) renaming ( Fin to Var; zero to here; suc to there )
open import Relation.Nullary.Decidable using ( True )
open import Data.Vec hiding ( _>>=_ )

open import Prelude

----------------------------------------------------------------------

data Nf (γ : ℕ) : Set
data Ne (γ : ℕ) : Set

data Nf γ where
  `Type : Nf γ
  `Π : (A : Nf γ) (B : Bind Nf γ) → Nf γ
  `λ : (b : Bind Nf γ) → Nf γ
  `[_] : Ne γ → Nf γ

data Ne γ where
  `var : (i : Var γ) → Ne γ
  _`∙_ : (f : Ne γ) (a : Nf γ) → Ne γ

----------------------------------------------------------------------

Env : ℕ → ℕ → Set
Env φ = Vec (Nf φ)

postulate
  wkn : ∀{γ} → Nf γ → Nf (suc γ)
  idEnv : ∀{γ} → Env γ γ

----------------------------------------------------------------------

infixr 3 _`→_
_`→_ : ∀{γ} (A B : Nf γ) → Nf γ
A `→ B = `Π A `∣ wkn B ∣

----------------------------------------------------------------------

`xᴺ : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Ne δ
`xᴺ γ {γ<δ = γ<δ} = `var (#_ γ {m<n = γ<δ})

`x : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Nf δ
`x γ {γ<δ = γ<δ} = `[ `xᴺ γ {γ<δ = γ<δ} ]

----------------------------------------------------------------------

lift : ∀{φ γ} → Env φ γ → Env (suc φ) (suc γ)
lift σ = `x 0 ∷ map wkn σ

{-# NO_TERMINATION_CHECK #-}
hsub : ∀{φ γ} → Env φ γ → Nf γ → Nf φ
hsubᴺ : ∀{φ γ} → Env φ γ → Ne γ → Nf φ

hsubᴮ : ∀{φ γ} → Env φ γ → Bind Nf γ → Bind Nf φ
hsubᴮ σ `∣ b ∣ = `∣ hsub (lift σ) b ∣

_∙ᴷ_ : ∀{γ} → Bind Nf γ → Nf γ → Nf γ
`∣ b ∣ ∙ᴷ a = hsub (a ∷ idEnv) b

_∙_ : ∀{γ} → Nf γ → Nf γ → Nf γ
`λ b ∙ a = b ∙ᴷ a
`[ f ] ∙ a = `[ f `∙ a ]
f ∙ a = undefined

hsub σ `Type = `Type
hsub σ (`Π A B) = `Π (hsub σ A) (hsubᴮ σ B)
hsub σ (`λ b) = `λ (hsubᴮ σ b)
hsub σ `[ a ] = hsubᴺ σ a

hsubᴺ σ (`var i) = lookup i σ
hsubᴺ σ (f `∙ a) = hsubᴺ σ f ∙ hsub σ a

----------------------------------------------------------------------

data Exp (γ : ℕ) : Set where
  `λ : (b : Bind Exp γ) → Exp γ
  `var : (i : Var γ) → Exp γ
  _`∙_ : (f : Exp γ) (a : Exp γ) → Exp γ

----------------------------------------------------------------------

Pi : Nf 0
Pi = `Π `Type `∣ `x 0 `→ `Type ∣ `→ `Type

Π' : Nf 0
Π' = `λ `∣ `λ `∣ `Π (`x 1) `∣ `[ `xᴺ 1 `∙ `x 0 ] ∣ ∣ ∣

Prim : ℕ
Prim = 2

----------------------------------------------------------------------

prelude : Env 0 Prim
prelude = Π' ∷ `Type ∷ []

----------------------------------------------------------------------

norm : ∀{γ} → Exp γ → Nf γ

normᴮ : ∀{γ} → Bind Exp γ → Bind Nf γ
normᴮ `∣ b ∣ = `∣ norm b ∣

norm (`λ b) = `λ (normᴮ b)
norm (`var i) = `[ `var i ]
norm (f `∙ a) = norm f ∙ norm a 

prim-norm : Exp Prim → Nf 0
prim-norm = hsub prelude ∘ norm

----------------------------------------------------------------------

open import Data.Bool
open import Data.Maybe
open import Category.Monad
import Level

postulate
  Ctx : ℕ → Set
  _==_ : ∀{γ} → Nf γ → Nf γ → Bool

open RawMonad {Level.zero} monad

infer : ∀{γ} → Ctx γ → Exp γ → Maybe (Nf γ)
infer Γ (f `∙ a) =
  infer Γ a >>= λ A →
  infer Γ f >>= λ
  { (`Π A' B) →
    if A == A'
    then return (B ∙ᴷ norm a)
    else nothing
  ; _ → nothing }
infer Γ a = undefined

----------------------------------------------------------------------

