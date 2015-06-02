module EnvExp where

----------------------------------------------------------------------

postulate undefined : ∀{ℓ} {A : Set ℓ} → A

open import Function
open import Data.Nat
open import Data.Fin hiding ( lift ) renaming ( Fin to Var; zero to here; suc to there )
open import Relation.Nullary.Decidable using ( True )
open import Data.Vec

----------------------------------------------------------------------

data Exp (γ : ℕ) : Set where
  `Type : Exp γ
  `Π : (A : Exp γ) (B : Exp (suc γ)) → Exp γ
  `λ : (b : Exp (suc γ)) → Exp γ
  `var : (i : Var γ) → Exp γ
  _`∙_ : (f : Exp γ) (a : Exp γ) → Exp γ

----------------------------------------------------------------------

data Nf (γ : ℕ) : Set
data Ne (γ : ℕ) : Set

Env : ℕ → ℕ → Set
Env φ = Vec (Nf φ)

record Bind (γ : ℕ) : Set where
  inductive
  constructor _`/_
  field
    {scope} : ℕ
    env : Env γ scope
    val : Exp (suc scope)

data Nf γ where
  `Type : Nf γ
  `Π : (A : Nf γ) (B : Nf (suc γ)) → Nf γ
  `λ : (b : Nf (suc γ)) → Nf γ
  `neut : Ne γ → Nf γ

data Ne γ where
  `var : (i : Var γ) → Ne γ
  _`∙_ : (f : Ne γ) (a : Nf γ) → Ne γ

----------------------------------------------------------------------

-- postulate
--   wkn : ∀{γ} → Exp γ → Exp (suc γ)
--   lift : ∀{φ γ} → Env φ γ → Env (suc φ) (suc γ)
--   idEnv : ∀{γ} → Env γ γ

-- ----------------------------------------------------------------------

-- infixr 3 _`→_
-- _`→_ : ∀{γ} (A B : Exp γ) → Exp γ
-- A `→ B = `Π A (wkn B)

-- ----------------------------------------------------------------------

-- `xᴺ : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Exp δ
-- `xᴺ γ {γ<δ = γ<δ} = `var (#_ γ {m<n = γ<δ})

-- `x : ∀ γ {δ} {γ<δ : True (suc γ ≤? δ)} → Exp δ
-- `x γ {γ<δ = γ<δ} = `neut (`xᴺ γ {γ<δ = γ<δ})

-- ----------------------------------------------------------------------

-- {-# NO_TERMINATION_CHECK #-}
-- hsub : ∀{φ γ} → Env φ γ → Exp γ → Exp φ
-- hsubᴺ : ∀{φ γ} → Env φ γ → Exp γ → Exp φ

-- _∙_ : ∀{γ} → Exp γ → Exp γ → Exp γ
-- `λ b ∙ a = hsub (a ∷ idEnv) b
-- `neut f ∙ a = `neut (f `∙ a)
-- f ∙ a = undefined

-- hsub σ `Type = `Type
-- hsub σ (`Π A B) = `Π (hsub σ A) (hsub (lift σ) B)
-- hsub σ (`λ b) = `λ (hsub (lift σ) b)
-- hsub σ (`neut a) = hsubᴺ σ a

-- hsubᴺ σ (`var i) = lookup i σ
-- hsubᴺ σ (f `∙ a) = hsubᴺ σ f ∙ hsub σ a

-- ----------------------------------------------------------------------

-- data Exp (γ : ℕ) : Set where
--   `λ : (b : Exp (suc γ)) → Exp γ
--   `var : (i : Var γ) → Exp γ
--   _`∙_ : (f : Exp γ) (a : Exp γ) → Exp γ

-- ----------------------------------------------------------------------

-- Pi : Exp 0
-- Pi = `Π `Type (`x 0 `→ `Type) `→ `Type

-- Π' : Exp 0
-- Π' = `λ (`λ (`Π (`x 1) (`neut (`xᴺ 1 `∙ `x 0))))

-- Prim : ℕ
-- Prim = 2

-- ----------------------------------------------------------------------

-- prelude : Env 0 Prim
-- prelude = Π' ∷ `Type ∷ []

-- ----------------------------------------------------------------------

-- norm : ∀{γ} → Exp γ → Exp γ
-- norm (`λ b) = `λ (norm b)
-- norm (`var i) = `neut (`var i)
-- norm (f `∙ a) = norm f ∙ norm a 

-- prim-norm : Exp Prim → Exp 0
-- prim-norm = hsub prelude ∘ norm

-- ----------------------------------------------------------------------

