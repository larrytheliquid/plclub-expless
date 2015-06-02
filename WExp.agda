module WExp where

----------------------------------------------------------------------

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

postulate sub : ∀{γ} → Exp γ → Exp (suc γ) → Exp γ

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
whnf : ∀{γ} → Exp γ → Exp γ

_∙_ : ∀{γ} → Exp γ → Exp γ → Exp γ
`λ b ∙ a = whnf (sub a b)
f ∙ a = f `∙ a

whnf `Type = `Type
whnf (`Π A B) = `Π (whnf A) B
whnf (`λ b) = `λ b
whnf (`var i) = `var i
whnf (f `∙ a) = whnf f ∙ whnf a

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
force : ∀{γ} → Exp γ → Exp γ -- WHNF as input
force `Type = `Type
force (`Π A B) = `Π (force A) (force (whnf B))
force (`λ b) = `λ (force (whnf b))
force (`var i) = `var i
force (f `∙ a) = force f `∙ force a

----------------------------------------------------------------------

norm : ∀{γ} → Exp γ → Exp γ
norm = force ∘ whnf

----------------------------------------------------------------------
