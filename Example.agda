module Example where
open import Data.Empty
open import Data.Bool
open import Data.Nat

one : if true then ℕ else ⊥
one = (λ x → x) suc zero

One : Set
One = if true then ℕ else ⊥

one' : One
one' = (λ x → x) suc zero

one'' : ℕ
one'' = (λ x → x) suc zero
