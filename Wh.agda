module Wh where

----------------------------------------------------------------------

postulate undefined : ∀{ℓ} {A : Set ℓ} → A

open import Function
open import Data.Nat
open import Data.Fin hiding ( lift ) renaming ( Fin to Var; zero to here; suc to there )
open import Relation.Nullary.Decidable using ( True )
open import Data.Vec

----------------------------------------------------------------------

data Wh (γ : ℕ) : Set
data Ne (γ : ℕ) : Set

Env : ℕ → ℕ → Set
Env φ = Vec (Wh φ)

infix 2 _`/_
record Bind (γ : ℕ) : Set where
  inductive
  constructor _`/_
  field
    {scope} : ℕ
    env : Env γ scope
    val : Wh (suc scope)

data Wh γ where
  `Type : Wh γ
  `Π : (A : Wh γ) (B : Bind γ) → Wh γ
  `λ : (b : Bind γ) → Wh γ
  `[_] : Ne γ → Wh γ

data Ne γ where
  `var : (i : Var γ) → Ne γ
  _`∙_ : (f : Ne γ) (a : Wh γ) → Ne γ

----------------------------------------------------------------------

postulate
  wkn : ∀{γ} → Wh γ → Wh (suc γ)
  lift : ∀{φ γ} → Env φ γ → Env (suc φ) (suc γ)
  idEnv : ∀{γ} → Env γ γ

----------------------------------------------------------------------

`∣_∣ : ∀{γ} → Wh (suc γ) → Bind γ
`∣ a ∣ = idEnv `/ a

infixr 3 _`→_
_`→_ : ∀{γ} (A B : Wh γ) → Wh γ
A `→ B = `Π A `∣ wkn B ∣

----------------------------------------------------------------------

`xᴺ : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Ne δ
`xᴺ γ {γ<δ = γ<δ} = `var (#_ γ {m<n = γ<δ})

`x : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Wh δ
`x γ {γ<δ = γ<δ} = `[ `xᴺ γ {γ<δ = γ<δ} ]

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
wh-hsub : ∀{φ γ} → Env φ γ → Wh γ → Wh φ
wh-hsubᴺ : ∀{φ γ} → Env φ γ → Ne γ → Wh φ

wh-hsubᴮ : ∀{φ γ} → Env φ γ → Bind γ → Bind φ
wh-hsubᴮ σ (ρ `/ b) = map (wh-hsub σ) ρ `/ b

_∙_ : ∀{γ} → Wh γ → Wh γ → Wh γ
`λ (σ `/ b) ∙ a = wh-hsub (a ∷ σ) b
`[ f ] ∙ a = `[ f `∙ a ]
f ∙ a = undefined

wh-hsub σ `Type = `Type
wh-hsub σ (`Π A B) = `Π (wh-hsub σ A) (wh-hsubᴮ σ B)
wh-hsub σ (`λ b) = `λ (wh-hsubᴮ σ b)
wh-hsub σ `[ a ] = wh-hsubᴺ σ a

wh-hsubᴺ σ (`var i) = lookup i σ
wh-hsubᴺ σ (f `∙ a) = wh-hsubᴺ σ f ∙ wh-hsub σ a

----------------------------------------------------------------------

data Exp (γ : ℕ) : Set where
  `λ : (b : Exp (suc γ)) → Exp γ
  `var : (i : Var γ) → Exp γ
  _`∙_ : (f : Exp γ) (a : Exp γ) → Exp γ

----------------------------------------------------------------------

Pi : Wh 0
Pi = `Π `Type `∣ `x 0 `→ `Type ∣ `→ `Type

Π' : Wh 0
Π' = `λ `∣ `λ `∣ `Π (`x 1) `∣ `[ `xᴺ 1 `∙ `x 0 ] ∣ ∣ ∣

Prim : ℕ
Prim = 2

----------------------------------------------------------------------

prelude : Env 0 Prim
prelude = Π' ∷ `Type ∷ []

----------------------------------------------------------------------

norm : ∀{γ} → Exp γ → Wh γ
norm (`λ b) = `λ `∣ norm b ∣
norm (`var i) = `[ `var i ]
norm (f `∙ a) = norm f ∙ norm a 

prim-norm : Exp Prim → Wh 0
prim-norm = wh-hsub prelude ∘ norm

----------------------------------------------------------------------

