module Type where

----------------------------------------------------------------------

infixr 3 _`→_

data Type : Set where
  `Bool : Type
  _`→_ : Type → Type → Type

----------------------------------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

data Var : Ctx → Type → Set where
  here : ∀{Γ A} → Var (Γ , A) A
  there : ∀{Γ A B} → Var Γ A → Var (Γ , B) A

_++_ : (Γ Δ : Ctx) → Ctx
Γ ++ ∅ = Γ
Γ ++ (Δ , A) = (Γ ++ Δ) , A

----------------------------------------------------------------------
