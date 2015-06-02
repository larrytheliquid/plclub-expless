module Prelude where

----------------------------------------------------------------------

open import Data.Nat
open import Data.Vec

----------------------------------------------------------------------

postulate undefined : ∀{ℓ} {A : Set ℓ} → A

----------------------------------------------------------------------

record Bind (A : ℕ → Set) (γ : ℕ) : Set where
  inductive
  constructor `∣_∣
  field
    val : A (suc γ)

----------------------------------------------------------------------

infix 2 _`/_
record Close (A B : ℕ → Set) (γ : ℕ) : Set where
  inductive
  constructor _`/_
  field
    {scope} : ℕ
    env : Vec (A γ) scope
    val : B (suc scope)

----------------------------------------------------------------------
