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
    Type-App : (t₁ : Type) (e₁ : Term Γ) (t₂ : Type) (e₂ : Term Γ) → Type-Proof Γ e₁ (Function t₁ t₂) → Type-Proof Γ e₂ t₁ → Type-Proof Γ (App e₁ e₂) t₂

  data IsVal-Proof (Γ : Context) : Term Γ → Set where
    IsVal-True : IsVal-Proof Γ True
    IsVal-False : IsVal-Proof Γ False
    IsVal-Fun : (t : Type) (e : Term (Extend t Γ)) (t′ : Type) → Type-Proof Γ (Fun t e) (Function t t′) → IsVal-Proof Γ (Fun t e)

  var-equal : (Γ : Context) → Variable Γ → Variable Γ → Bool
  var-equal (Extend t Δ) (inj₂ _) (inj₂ _) = true
  var-equal (Extend t Δ) (inj₁ _) (inj₂ _) = false
  var-equal (Extend t Δ) (inj₂ _) (inj₁ _) = false
  var-equal (Extend t Δ) (inj₁ i) (inj₁ j) = var-equal Δ i j
  var-equal Empty () 

  context-switch-id : (Γ : Context) → Variable Γ → Variable Γ
  context-switch-id Γ x = x

  context-switch-promote-right : ∀ Γ Δ t → (Variable Γ → Variable Δ) → (Variable Γ → Variable (Extend t Δ))
  context-switch-promote-right Γ Δ t f x = inj₁ (f x)
  
  context-switch-promote-both : (Γ : Context) (Δ : Context) (t : Type) → (Variable Γ → Variable Δ) → (Variable (Extend t Γ) → Variable (Extend t Δ))
  context-switch-promote-both Γ Δ t f (inj₂ x) = inj₂ x
  context-switch-promote-both Γ Δ t f (inj₁ x) = inj₁ (f x)

  context-switch-promote-both-opt : (Γ : Context) (Δ : Context) (t : Type) → (Variable Γ → Maybe (Variable Δ)) → (Variable (Extend t Γ) → Maybe (Variable (Extend t Δ)))
  context-switch-promote-both-opt Γ Δ t f (inj₂ x) = just (inj₂ x)
  context-switch-promote-both-opt Γ Δ t f (inj₁ x) with f x
  context-switch-promote-both-opt Γ Δ t f (inj₁ x)       | just fx = just (inj₁ fx)
  context-switch-promote-both-opt Γ Δ t f (inj₁ x)       | nothing = nothing

  promote : (Γ : Context) (Δ : Context) → Term Γ → (Variable Γ → Variable Δ) → Term Δ
  promote Γ Δ True f = True
  promote Γ Δ False f = False
  promote Γ Δ (Fun t e) f = Fun t (promote (Extend t Γ) (Extend t Δ) e (context-switch-promote-both Γ Δ t f))
  promote Γ Δ (App e₁ e₂) f = App (promote Γ Δ e₁ f) (promote Γ Δ e₂ f)
  promote Γ Δ (Var v) f = Var (f v)

  demote-variable : (Γ : Context) (t : Type) → Variable (Extend t Γ) → Maybe (Variable Γ)
  demote-variable Γ t (inj₁ x) = just x
  demote-variable Γ t (inj₂ _) = nothing
  
  subst : (Γ : Context) (Δ : Context) → Term Δ → Variable Γ → Term Γ → (Variable Δ → Variable Δ) → (Variable Γ → Maybe (Variable Δ)) → Term Δ
  subst Γ Δ _ _ True f g = True
  subst Γ Δ _ _ False f g = False
  subst Γ Δ e n (Var i) f g with g i
  subst Γ Δ e n (Var i) f g       | nothing = e 
  subst Γ Δ e n (Var i) f g       | just x = Var x
  subst Γ Δ e n (Fun t e₂) f g =
    Fun t (subst (Extend t Γ) (Extend t Δ) (promote Δ (Extend t Δ) e (context-switch-promote-right Δ Δ t f)) (inj₁ n) e₂ (context-switch-promote-both Δ Δ t f) (context-switch-promote-both-opt Γ Δ t g))
  subst Γ Δ e n (App e₁ e₂) f g = App (subst Γ Δ e n e₁ f g) (subst Γ Δ e n e₂ f g)

  data Execution-Proof (Γ : Context) : Term Γ → Term Γ → Set where
    Execution-App₁ : (e₁ : Term Γ) (e₂ : Term Γ) (e₁′ : Term Γ) → Execution-Proof Γ e₁ e₁′ → Execution-Proof Γ (App e₁ e₂) (App e₁′ e₂)
    Execution-App₂ : (e₁ : Term Γ) (e₂ : Term Γ) (e₂′ : Term Γ) → IsVal-Proof Γ e₁ → Execution-Proof Γ e₂ e₂′ → Execution-Proof Γ (App e₁ e₂) (App e₁ e₂′)
    Execution-AppFun : (t₁ : Type) (e₁ : Term (Extend t₁ Γ)) (e₂ : Term Γ) (t₂ : Type) → Type-Proof Γ (Fun t₁ e₁) (Function t₁ t₂) → Type-Proof Γ e₂ t₁ → IsVal-Proof Γ e₂
      → Execution-Proof Γ (App (Fun t₁ e₁) e₂) (subst (Extend t₁ Γ) Γ e₂ (inj₂ (Box t₁)) e₁ (context-switch-id Γ) (demote-variable Γ t₁))

  Progress : (e : Term Empty) (t : Type) → Type-Proof Empty e t → (IsVal-Proof Empty e) ⊎ (Σ (Term Empty) (λ e′ → Execution-Proof Empty e e′))
  Progress True t Type-True = inj₁ (IsVal-True)
  Progress False t Type-False = inj₁ (IsVal-False)
  Progress (Var v) t (Type-Var ())
  Progress (Fun t e) (Function t t′) (Type-Fun t e t′ p) = inj₁ (IsVal-Fun t e t′ (Type-Fun t e t′ p))
  Progress (App (Var ()) e₂) t₂ (Type-App t₁ (Var ()) t₂ e₂ p₁ p₂)
  Progress (App (Fun t₁ e₁) (Var ())) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ (Var ()) (Type-Fun t₁ e₁ t₂ p₂) p₃)
  Progress (App (Fun t₁ e₁) (Fun t e₂)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(Fun t e₂) (Type-Fun t₁ e₁ t₂ p₂) (Type-Fun t e₂ t′ p′)) = inj₂ (subst (Extend t₁ Empty) Empty (Fun t e₂) (inj₂ (Box t₁)) e₁ (context-switch-id Empty) (demote-variable Empty t₁) , Execution-AppFun t₁ e₁ (Fun t e₂) t₂ (Type-Fun t₁ e₁ t₂ p₂) (Type-Fun t e₂ t′ p′) (IsVal-Fun t e₂ t′ (Type-Fun t e₂ t′ p′)))
  Progress (App (Fun t₁ e₁) (App e₂ e₃)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(App e₂ e₃) (Type-Fun t₁ e₁ t₂ p₂) p₃) with Progress (App e₂ e₃) t₁ p₃
  Progress (App (Fun t₁ e₁) (App e₂ e₃)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(App e₂ e₃) (Type-Fun t₁ e₁ t₂ p₂) p₃)       | inj₁ ()
  Progress (App (Fun t₁ e₁) (App e₂ e₃)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(App e₂ e₃) (Type-Fun t₁ e₁ t₂ p₂) p₃)       | inj₂ pₓ = inj₂ (App (Fun t₁ e₁) (proj₁ pₓ) , Execution-App₂ (Fun t₁ e₁) (App e₂ e₃) (proj₁ pₓ) (IsVal-Fun t₁ e₁ t₂ (Type-Fun t₁ e₁ t₂ p₂)) (proj₂ pₓ))
  Progress (App (Fun t₁ e₁) True) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .True (Type-Fun t₁ e₁ t₂ p₂) p₃) = inj₂ ((subst (Extend t₁ Empty) Empty True (inj₂ (Box t₁)) e₁ (context-switch-id Empty) (demote-variable Empty t₁)) , (Execution-AppFun t₁ e₁ True t₂ (Type-Fun t₁ e₁ t₂ p₂) p₃ IsVal-True))
  Progress (App (Fun t₁ e₁) False) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .False (Type-Fun t₁ e₁ t₂ p₂) p₃) = inj₂ ((subst (Extend t₁ Empty) Empty False (inj₂ (Box t₁)) e₁ (context-switch-id Empty) (demote-variable Empty t₁)) , (Execution-AppFun t₁ e₁ False t₂ (Type-Fun t₁ e₁ t₂ p₂) p₃ IsVal-False))  
  Progress (App (App e₁ e₃) e₂) t₂ (Type-App t₁ (App e₁ e₃) t₂ .e₂ p₁ p₂) with Progress (App e₁ e₃) (Function t₁ t₂) p₁
  Progress (App (App e₁ e₃) e₂) t₂ (Type-App t₁ (App e₁ e₃) t₂ .e₂ p₁ p₂)       | inj₁ ()
  Progress (App (App e₁ e₃) e₂) t₂ (Type-App t₁ (App e₁ e₃) t₂ .e₂ p₁ p₂)       | inj₂ pₓ = inj₂ ((App (proj₁ pₓ) e₂) , (Execution-App₁ (App e₁ e₃) e₂ (proj₁ pₓ) (proj₂ pₓ)))
  Progress (App True e₂) t₂ (Type-App t₁ True t₂ e₂ () p₂) 
  Progress (App False e₂) t₂ (Type-App t₁ False t₂ e₂ () p₂) 
  
