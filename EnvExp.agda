module EnvExp where

----------------------------------------------------------------------

open import Function
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding ( lift ) renaming ( Fin to Var; zero to here; suc to there )
open import Relation.Nullary.Decidable using ( True )
open import Data.Vec hiding ( _>>=_ )
open import Data.Maybe hiding ( map )
open import Category.Monad
import Level

open import Prelude

----------------------------------------------------------------------

data Exp (γ : ℕ) : Set where
  `Type : Exp γ
  `Π : (A : Exp γ) (B : Bind Exp γ) → Exp γ
  `λ : (b : Bind Exp γ) → Exp γ
  `var : (i : Var γ) → Exp γ
  _`∙_ : (f : Exp γ) (a : Exp γ) → Exp γ

----------------------------------------------------------------------

data Wh (γ : ℕ) : Set
data Nu (γ : ℕ) : Set

data Wh γ where
  `Type : Wh γ
  `Π : (A : Wh γ) (B : Close Wh Exp γ) → Wh γ
  `λ : (b : Close Wh Exp γ) → Wh γ
  `[_] : Nu γ → Wh γ

data Nu γ where
  `var : (i : Var γ) → Nu γ
  _`∙_ : (f : Nu γ) (a : Wh γ) → Nu γ

----------------------------------------------------------------------

Env : ℕ → ℕ → Set
Env φ = Vec (Wh φ)

----------------------------------------------------------------------

postulate
  wkn : ∀{γ} → Exp γ → Exp (suc γ)
  wknʷ : ∀{γ} → Wh γ → Wh (suc γ)
  idEnv : ∀{γ} → Env γ γ

----------------------------------------------------------------------

∣_∣ : ∀{γ} → Exp (suc γ) → Close Wh Exp γ
∣ a ∣ = idEnv `/ a

infixr 3 _`→_
_`→_ : ∀{γ} (A : Wh γ) (B : Exp γ) → Wh γ
A `→ B = `Π A ∣ wkn B ∣

----------------------------------------------------------------------

`xᴺ : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Nu δ
`xᴺ γ {γ<δ = γ<δ} = `var (#_ γ {m<n = γ<δ})

`x : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Wh δ
`x γ {γ<δ = γ<δ} = `[ `xᴺ γ {γ<δ = γ<δ} ]

lift : ∀{φ γ} → Env φ γ → Env (suc φ) (suc γ)
lift σ = `x 0 ∷ map wknʷ σ

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
eval : ∀{φ γ} → Env φ γ → Exp γ → Wh φ

evalᴷ : ∀{φ γ} → Env φ γ → Bind Exp γ → Close Wh Exp φ
evalᴷ σ `∣ b ∣ = σ `/ b

_∙ᴷ_ : ∀{γ} → Close Wh Exp γ → Wh γ → Wh γ
(σ `/ b) ∙ᴷ a = eval (a ∷ σ) b

_∙_ : ∀{γ} → Wh γ → Wh γ → Wh γ
`λ b ∙ a = b ∙ᴷ a
`[ f ] ∙ a = `[ f `∙ a ]
f ∙ a = undefined

eval σ `Type = `Type
eval σ (`Π A B) = `Π (eval σ A) (evalᴷ σ B)
eval σ (`λ b) = `λ (evalᴷ σ b)
eval σ (`var i) = lookup i σ
eval σ (f `∙ a) = eval σ f ∙ eval σ a

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

!_ : ∀{γ} → Close Wh Exp γ → Wh (suc γ)
! (σ `/ b) = eval (lift σ) b

{-# NO_TERMINATION_CHECK #-}
force : ∀{γ} → Wh γ → Nf γ
forceᴺ : ∀{γ} → Nu γ → Ne γ

forceᴷ : ∀{γ} → Close Wh Exp γ → Bind Nf γ
forceᴷ b = `∣ force (! b) ∣

force `Type = `Type
force (`Π A B) = `Π (force A) (forceᴷ B)
force (`λ b) = `λ (forceᴷ b)
force `[ a ] = `[ forceᴺ a ]

forceᴺ (`var i) = `var i
forceᴺ (f `∙ a) = forceᴺ f `∙ force a

----------------------------------------------------------------------

wh-norm : ∀{γ} → Exp γ → Wh γ

wh-normᴮ : ∀{γ} → Bind Exp γ → Close Wh Exp γ
wh-normᴮ `∣ b ∣ = ∣ b ∣

wh-norm `Type = `Type
wh-norm (`Π A B) = `Π (wh-norm A) (wh-normᴮ B)
wh-norm (`λ b) = `λ (wh-normᴮ b)
wh-norm (`var i) = `[ `var i ]
wh-norm (f `∙ a) = wh-norm f ∙ wh-norm a

norm : ∀{γ} → Exp γ → Nf γ
norm = force ∘ wh-norm

----------------------------------------------------------------------

postulate
  Ctx : ℕ → Set
  _==_ : ∀{γ} → Nf γ → Nf γ → Bool

open RawMonad {Level.zero} monad

infer : ∀{γ} → Ctx γ → Exp γ → Maybe (Wh γ)
infer Γ (f `∙ a) =
  infer Γ a >>= λ A →
  infer Γ f >>= λ
  { (`Π A' B) →
    if force A == force A'
    then return (B ∙ᴷ wh-norm a)
    else nothing
  ; _ → nothing }
infer Γ a = undefined

----------------------------------------------------------------------

