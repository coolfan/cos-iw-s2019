open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Data.Unit
open import Data.List
open import Agda.Builtin.Equality
open import Data.Sum
open import Data.Bool

module stlc where
  data ⊥ : Set where

  data Type : Set where
    Boolean : Type
    Function : Type → Type → Type

  data Type-Box : Type → Set where
    Box : (t : Type) → Type-Box t

  data Context : Set where
    Empty : Context
    Extend : Type → Context → Context

  Variable : Context → Set
  Variable Empty = ⊥
  Variable (Extend t Γ) = (Variable Γ) ⊎ (Type-Box t)
  
  data Term (Γ : Context) : Set where
    Var : Variable Γ → Term Γ
    Fun : ∀ t → Term (Extend t Γ) → Term Γ
    App : Term Γ → Term Γ → Term Γ
    True : Term Γ
    False : Term Γ

  type-var : (Γ : Context) → Variable Γ → Type
  type-var (Extend t Δ) (inj₂ (Box t)) = t
  type-var (Extend t Δ) (inj₁ x) = type-var Δ x
  type-var Empty x = _

  data Type-Proof (Γ : Context) : Term Γ → Type → Set where
    Type-True : Type-Proof Γ True Boolean
    Type-False : Type-Proof Γ False Boolean
    Type-Var : (v : Variable Γ) → Type-Proof Γ (Var v) (type-var Γ v) 
    Type-Fun : (t : Type) (e : Term (Extend t Γ)) (t′ : Type) → Type-Proof (Extend t Γ) e t′ → Type-Proof Γ (Fun t e) (Function t t′)
    Type-App : (t₁ : Type) (e₁ : Term Γ) (t₂ : Type) (e₂ : Term Γ) → Type-Proof Γ e₁ (Function t₁ t₂) → Type-Proof Γ e₂ t₂ → Type-Proof Γ (App e₁ e₂) t₂

  data IsVal-Proof (Γ : Context) : Term Γ → Set where
    IsVal-True : IsVal-Proof Γ True
    IsVal-False : IsVal-Proof Γ False
    IsVal-Fun : (t : Type) (e : Term (Extend t Γ)) → IsVal-Proof Γ (Fun t e)

  var-equal : (Γ : Context) → Variable Γ → Variable Γ → Bool
  var-equal (Extend t Δ) (inj₂ _) (inj₂ _) = true
  var-equal (Extend t Δ) (inj₁ _) (inj₂ _) = false
  var-equal (Extend t Δ) (inj₂ _) (inj₁ _) = false
  var-equal (Extend t Δ) (inj₁ i) (inj₁ j) = var-equal Δ i j
  var-equal Empty x y = _

  promote : (Γ : Context) (Δ : Context) → Term Γ → Term Δ
  promote Γ Δ True = True
  promote Γ Δ False = False
  promote Γ Δ (Fun t e) = Fun t (promote (Extend t Γ) (Extend t Δ) e)
  promote Γ Δ (App e₁ e₂) = App (promote Γ Δ e₁) (promote Γ Δ e₂)
  promote Γ Δ (Var v) = ?

  subst : (Γ : Context) (Δ : Context) → Term Γ → Variable Δ → Term Δ → Term Δ
  subst Γ Δ _ _ True = True
  subst Γ Δ _ _ False = False
  subst Γ Δ e n (Var i) with var-equal Δ n i
  subst Γ Δ e n (Var i)       | true = promote Γ Δ e
  subst Γ Δ e n (Var i)       | false = Var i
  subst Γ Δ e n (Fun t e₂) = Fun t (subst Γ (Extend t Δ) e (inj₁ n) e₂)
  subst Γ Δ e n (App e₁ e₂) = App (subst Γ Δ e n e₁) (subst Γ Δ e n e₂)

  data Execution-Proof (Γ : Context) : Term Γ → Term Γ → Set where
    Execution-App₁ : (e₁ : Term Γ) (e₂ : Term Γ) (e₁′ : Term Γ) → Execution-Proof Γ e₁ e₁′ → Execution-Proof Γ (App e₁ e₂) (App e₁′ e₂)
    Execution-App₂ : (e₁ : Term Γ) (e₂ : Term Γ) (e₂′ : Term Γ) → IsVal-Proof Γ e₁ → Execution-Proof Γ e₂ e₂′ → Execution-Proof Γ (App e₁ e₂) (App e₁ e₂′)
    Execution-AppFun : (t₁ : Type) (e₁ : Term (Extend t₁ Γ)) (e₂ : Term Γ) (t₂ : Type) → Type-Proof Γ (Fun t₁ e₁) (Function t₁ t₂) → Type-Proof Γ e₂ t₂ → IsVal-Proof Γ e₂
      → Execution-Proof Γ (App (Fun t₁ e₁) e₂) (subst Γ (Extend t₁ Γ) e₂ (inj₂ (Box t₁)) e₁)

  --Progress : (e : Term) (t : Type) → Type-Proof e t → OR (IsVal-Proof e) (Σ Term (λ e′ → Execution-Proof e e′))
  
