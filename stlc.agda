open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Data.Unit
open import Data.List
open import Data.Bool
open import Agda.Builtin.Equality

module stlc where
  data Type : Set where
    Boolean : Type
    Function : Type → Type → Type

  data STLC : Set where
    Var : ℕ → STLC
    Fun : Type → STLC → STLC
    App : STLC → STLC → STLC
    True : STLC
    False : STLC

  data OR (A B : Set) : Set where
    ∨-intro₁ : A → OR A B
    ∨-intro₂ : B → OR A B

  data Context : Set where
    Empty : Context
    Cons : Type → Context → Context

  data Type-Proof : STLC → Type → Set where
    Type-True : Context → Type-Proof True Boolean
    Type-False : Context → Type-Proof False Boolean
    Type-Var 
    Type-Fun : (t : Type) (e : STLC) (t′ : Type) → Type-Proof e t′ → Type-Proof (Fun t e) (Function t t′)
    Type-App : (t₁ : Type) (e₁ : STLC) (t₂ : Type) (e₂ : STLC) → Type-Proof e₁ (Function t₁ t₂) → Type-Proof e₂ t₂ → Type-Proof (App e₁ e₂) t₂

  data IsVal-Proof : STLC → Set where
    IsVal-True : IsVal-Proof True
    IsVal-False : IsVal-Proof False
    IsVal-Fun : (t : Type) (e : STLC) → IsVal-Proof (Fun t e)

  nat-equal : ℕ → ℕ → Bool
  nat-equal zero zero = true
  nat-equal zero (suc n) = false
  nat-equal (suc m) zero = false
  nat-equal (suc m) (suc n) = nat-equal m n

  subst : STLC → ℕ → STLC → STLC
  subst _ _ True = True
  subst _ _ False = False
  subst e n (Var i) with nat-equal n i
  subst e n (Var i)       | true = e
  subst e n (Var i)       | false = Var i
  subst e n (Fun t e₂) = Fun t (subst e (suc n) e₂)
  subst e n (App e₁ e₂) = App (subst e n e₁) (subst e n e₂)

  data Execution-Proof : STLC → STLC → Set where
    Execution-App₁ : (e₁ : STLC) (e₂ : STLC) (e₁′ : STLC) → Execution-Proof e₁ e₁′ → Execution-Proof (App e₁ e₂) (App e₁′ e₂)
    Execution-App₂ : (e₁ : STLC) (e₂ : STLC) (e₂′ : STLC) → IsVal-Proof e₁ → Execution-Proof e₂ e₂′ → Execution-Proof (App e₁ e₂) (App e₁ e₂′)
    Execution-AppFun : (e₁ : STLC) (e₂ : STLC) (t₁ : Type) (t₂ : Type) → Type-Proof e₁ (Function t₁ t₂) → Type-Proof e₂ t₂ → IsVal-Proof e₂ → Execution-Proof (App e₁ e₂) (subst e₂ 0 e₁)

  Progress : (e : STLC) (t : Type) → Type-Proof e t → OR (IsVal-Proof e) (Σ STLC (λ e′ → Execution-Proof e e′))
  
