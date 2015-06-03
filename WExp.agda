module WExp where

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

postulate sub : ∀{γ} → Exp γ → Exp (suc γ) → Exp γ

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
wh-norm : ∀{γ} → Exp γ → Exp γ

wh-normᴮ : ∀{γ} → Bind Exp γ → Bind Exp γ
wh-normᴮ b = b

_∙ᴮ_ : ∀{γ} → Bind Exp γ → Exp γ → Exp γ
`∣ b ∣ ∙ᴮ a = wh-norm (sub a b)

_∙_ : ∀{γ} → Exp γ → Exp γ → Exp γ
`λ b ∙ a = b ∙ᴮ a
f ∙ a = f `∙ a

wh-norm `Type = `Type
wh-norm (`Π A B) = `Π (wh-norm A) (wh-normᴮ B)
wh-norm (`λ b) = `λ (wh-normᴮ b)
wh-norm (`var i) = `var i
wh-norm (f `∙ a) = wh-norm f ∙ wh-norm a

----------------------------------------------------------------------

{-# NO_TERMINATION_CHECK #-}
force : ∀{γ} → Exp γ → Exp γ -- WH-NORM as input

forceᴮ : ∀{γ} → Bind Exp γ → Bind Exp γ
forceᴮ `∣ b ∣ = `∣ force (wh-norm b) ∣

force `Type = `Type
force (`Π A B) = `Π (force A) (forceᴮ B)
force (`λ b) = `λ (forceᴮ b)
force (`var i) = `var i
force (f `∙ a) = force f `∙ force a

----------------------------------------------------------------------

norm : ∀{γ} → Exp γ → Exp γ
norm = force ∘ wh-norm

----------------------------------------------------------------------

postulate
  Ctx : ℕ → Set
  _==_ : ∀{γ} → Exp γ → Exp γ → Bool

open RawMonad {Level.zero} monad

infer : ∀{γ} → Ctx γ → Exp γ → Maybe (Exp γ)
infer Γ (f `∙ a) =
  infer Γ a >>= λ A →
  infer Γ f >>= λ
  { (`Π A' B) →
    if force A == force A'
    then return (B ∙ᴮ a)
    else nothing
  ; _ → nothing }
infer Γ a = undefined

----------------------------------------------------------------------
