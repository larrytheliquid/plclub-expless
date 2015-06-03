module Wh where

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

data Wh (γ : ℕ) : Set
data Nu (γ : ℕ) : Set

data Wh γ where
  `Type : Wh γ
  `Π : (A : Wh γ) (B : Close Wh Wh γ) → Wh γ
  `λ : (b : Close Wh Wh γ) → Wh γ
  `[_] : Nu γ → Wh γ

data Nu γ where
  `var : (i : Var γ) → Nu γ
  _`∙_ : (f : Nu γ) (a : Wh γ) → Nu γ

----------------------------------------------------------------------

Env : ℕ → ℕ → Set
Env φ = Vec (Wh φ)

----------------------------------------------------------------------

postulate
  wkn : ∀{γ} → Wh γ → Wh (suc γ)
  idEnv : ∀{γ} → Env γ γ

----------------------------------------------------------------------

∣_∣ : ∀{γ} → Wh (suc γ) → Close Wh Wh γ
∣ a ∣ = idEnv `/ a

infixr 3 _`→_
_`→_ : ∀{γ} (A B : Wh γ) → Wh γ
A `→ B = `Π A ∣ wkn B ∣

----------------------------------------------------------------------

`xᴺ : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Nu δ
`xᴺ γ {γ<δ = γ<δ} = `var (#_ γ {m<n = γ<δ})

`x : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Wh δ
`x γ {γ<δ = γ<δ} = `[ `xᴺ γ {γ<δ = γ<δ} ]

lift : ∀{φ γ} → Env φ γ → Env (suc φ) (suc γ)
lift σ = `x 0 ∷ map wkn σ

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
wh-hsub : ∀{φ γ} → Env φ γ → Wh γ → Wh φ
wh-hsubᴺ : ∀{φ γ} → Env φ γ → Nu γ → Wh φ

wh-hsubᴷ : ∀{φ γ} → Env φ γ → Close Wh Wh γ → Close Wh Wh φ
wh-hsubᴷ σ (ρ `/ b) = map (wh-hsub σ) ρ `/ b

_∙ᴷ_ : ∀{γ} → Close Wh Wh γ → Wh γ → Wh γ
(σ `/ b) ∙ᴷ a = wh-hsub (a ∷ σ) b

_∙_ : ∀{γ} → Wh γ → Wh γ → Wh γ
`λ b ∙ a = b ∙ᴷ a
`[ f ] ∙ a = `[ f `∙ a ]
f ∙ a = undefined

wh-hsub σ `Type = `Type
wh-hsub σ (`Π A B) = `Π (wh-hsub σ A) (wh-hsubᴷ σ B)
wh-hsub σ (`λ b) = `λ (wh-hsubᴷ σ b)
wh-hsub σ `[ a ] = wh-hsubᴺ σ a

wh-hsubᴺ σ (`var i) = lookup i σ
wh-hsubᴺ σ (f `∙ a) = wh-hsubᴺ σ f ∙ wh-hsub σ a

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

!_ : ∀{γ} → Close Wh Wh γ → Wh (suc γ)
! (σ `/ b) = wh-hsub (lift σ) b

{-# NO_TERMINATION_CHECK #-}
force : ∀{γ} → Wh γ → Nf γ
forceᴺ : ∀{γ} → Nu γ → Ne γ

forceᴷ : ∀{γ} → Close Wh Wh γ → Bind Nf γ
forceᴷ b = `∣ force (! b) ∣

force `Type = `Type
force (`Π A B) = `Π (force A) (forceᴷ B)
force (`λ b) = `λ (forceᴷ b)
force `[ a ] = `[ forceᴺ a ]

forceᴺ (`var i) = `var i
forceᴺ (f `∙ a) = forceᴺ f `∙ force a

----------------------------------------------------------------------

data Exp (γ : ℕ) : Set where
  `λ : (b : Bind Exp γ) → Exp γ
  `var : (i : Var γ) → Exp γ
  _`∙_ : (f : Exp γ) (a : Exp γ) → Exp γ

----------------------------------------------------------------------

Pi : Wh 0
Pi = `Π `Type ∣ `x 0 `→ `Type ∣ `→ `Type

Π' : Wh 0
Π' = `λ ∣ `λ ∣ `Π (`x 1) ∣ `[ `xᴺ 1 `∙ `x 0 ] ∣ ∣ ∣

Prim : ℕ
Prim = 2

----------------------------------------------------------------------

prelude : Env 0 Prim
prelude = Π' ∷ `Type ∷ []

----------------------------------------------------------------------

wh-norm : ∀{γ} → Exp γ → Wh γ

wh-normᴮ : ∀{γ} → Bind Exp γ → Close Wh Wh γ
wh-normᴮ `∣ b ∣ = ∣ wh-norm b ∣

wh-norm (`λ b) = `λ (wh-normᴮ b)
wh-norm (`var i) = `[ `var i ]
wh-norm (f `∙ a) = wh-norm f ∙ wh-norm a 

prim-wh-norm : Exp Prim → Wh 0
prim-wh-norm = wh-hsub prelude ∘ wh-norm

norm : ∀{γ} → Exp γ → Nf γ
norm = force ∘ wh-norm

prim-norm : Exp Prim → Nf 0
prim-norm = force ∘ prim-wh-norm

----------------------------------------------------------------------

postulate
  _==_ : ∀{γ} → Close Wh Wh γ → Close Wh Wh γ → Bool
  _==ᴿ_ : ∀{γ} → Var γ → Var γ → Bool

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
_≈_ : ∀{γ} → Wh γ → Wh γ → Bool
_≈ᴺ_ : ∀{γ} → Nu γ → Nu γ → Bool

_≈ᴷ_ : ∀{γ} → Close Wh Wh γ → Close Wh Wh γ → Bool
b₁ ≈ᴷ b₂ = b₁ == b₂ ∨ (! b₁) ≈ (! b₂)

`Type ≈ `Type = true
`Π A₁ B₁ ≈ `Π A₂ B₂ = A₁ ≈ A₂ ∧ B₁ ≈ᴷ B₂
`λ b₁ ≈ `λ b₂ = b₁ ≈ᴷ b₂
`[ a₁ ] ≈ `[ a₂ ] = a₁ ≈ᴺ a₂
_ ≈ _ = false

(f₁ `∙ a₁) ≈ᴺ (f₂ `∙ a₂) = (f₁ ≈ᴺ f₂) ∧ a₁ ≈ a₂
`var i ≈ᴺ `var j = i ==ᴿ j
_ ≈ᴺ _ = false

----------------------------------------------------------------------

postulate Ctx : ℕ → Set

open RawMonad {Level.zero} monad

infer : ∀{γ} → Ctx γ → Exp γ → Maybe (Wh γ)
infer Γ (f `∙ a) =
  infer Γ a >>= λ A →
  infer Γ f >>= λ
  { (`Π A' B) →
    if A ≈ A'
    then return (B ∙ᴷ wh-norm a)
    else nothing
  ; _ → nothing }
infer Γ a = undefined

----------------------------------------------------------------------

