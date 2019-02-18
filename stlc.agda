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
  type-var Empty ()

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
  var-equal Empty ()

  context-switch-id : (Γ : Context) → Variable Γ → Variable Γ
  context-switch-id Γ x = x

  context-switch-promote-right : (Γ : Context) (Δ : Context) (t : Type) → (Variable Γ → Variable Δ) → (Variable Γ → Variable (Extend t Δ))
  context-switch-promote-right Γ Δ t f x = inj₁ (f x)

  context-switch-promote-both : (Γ : Context) (Δ : Context) (t : Type) → (Variable Γ → Variable Δ) → (Variable (Extend t Γ) → Variable (Extend t Δ))
  context-switch-promote-both Γ Δ t f (inj₂ x) = inj₂ x
  context-switch-promote-both Γ Δ t f (inj₁ x) = inj₁ (f x)

  promote : (Γ : Context) (Δ : Context) → Term Γ → (Variable Γ → Variable Δ) → Term Δ
  promote Γ Δ True f = True
  promote Γ Δ False f = False
  promote Γ Δ (Fun t e) f = Fun t (promote (Extend t Γ) (Extend t Δ) e (context-switch-promote-both Γ Δ t f))
  promote Γ Δ (App e₁ e₂) f = App (promote Γ Δ e₁ f) (promote Γ Δ e₂ f)
  promote Γ Δ (Var v) f = Var (f v)

  subst : (Γ : Context) (Δ : Context) → Term Γ → Variable Δ → Term Δ → (Variable Γ → Variable Δ) → Term Δ
  subst Γ Δ _ _ True f = True
  subst Γ Δ _ _ False f = False
  subst Γ Δ e n (Var i) f with var-equal Δ n i
  subst Γ Δ e n (Var i) f       | true = promote Γ Δ e f
  subst Γ Δ e n (Var i) f       | false = Var i
  subst Γ Δ e n (Fun t e₂) f = Fun t (subst Γ (Extend t Δ) e (inj₁ n) e₂ (context-switch-promote-right Γ Δ t f))
  subst Γ Δ e n (App e₁ e₂) f = App (subst Γ Δ e n e₁ f) (subst Γ Δ e n e₂ f)

  data Execution-Proof (Γ : Context) : Term Γ → Term Γ → Set where
    Execution-App₁ : (e₁ : Term Γ) (e₂ : Term Γ) (e₁′ : Term Γ) → Execution-Proof Γ e₁ e₁′ → Execution-Proof Γ (App e₁ e₂) (App e₁′ e₂)
    Execution-App₂ : (e₁ : Term Γ) (e₂ : Term Γ) (e₂′ : Term Γ) → IsVal-Proof Γ e₁ → Execution-Proof Γ e₂ e₂′ → Execution-Proof Γ (App e₁ e₂) (App e₁ e₂′)
    Execution-AppFun : (t₁ : Type) (e₁ : Term (Extend t₁ Γ)) (e₂ : Term Γ) (t₂ : Type) → Type-Proof Γ (Fun t₁ e₁) (Function t₁ t₂) → Type-Proof Γ e₂ t₂ → IsVal-Proof Γ e₂
      → Execution-Proof Γ (App (Fun t₁ e₁) e₂) (subst Γ (Extend t₁ Γ) e₂ (inj₂ (Box t₁)) e₁)

  --Progress : (e : Term) (t : Type) → Type-Proof e t → OR (IsVal-Proof e) (Σ Term (λ e′ → Execution-Proof e e′))
  
