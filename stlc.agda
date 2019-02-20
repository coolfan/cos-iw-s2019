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
    _,_ : Context → Type → Context

  Variable : Context → Set
  Variable Empty = ⊥
  Variable (Γ , t) = (Variable Γ) ⊎ (Type-Box t)
  
  data Term (Γ : Context) : Set where
    Var : Variable Γ → Term Γ
    Fun : ∀ t → Term (Γ , t) → Term Γ
    App : Term Γ → Term Γ → Term Γ
    True : Term Γ
    False : Term Γ

  type-var : (Γ : Context) → Variable Γ → Type
  type-var (Δ , t) (inj₂ (Box t)) = t
  type-var (Δ , t) (inj₁ x) = type-var Δ x
  type-var Empty ()

  data Type-Proof (Γ : Context) : Term Γ → Type → Set where
    Type-True : Type-Proof Γ True Boolean
    Type-False : Type-Proof Γ False Boolean
    Type-Var : (v : Variable Γ) → Type-Proof Γ (Var v) (type-var Γ v) 
    Type-Fun : (t : Type) (e : Term (Γ , t)) (t′ : Type) → Type-Proof (Γ , t) e t′ → Type-Proof Γ (Fun t e) (Function t t′)
    Type-App : (t₁ : Type) (e₁ : Term Γ) (t₂ : Type) (e₂ : Term Γ) → Type-Proof Γ e₁ (Function t₁ t₂) → Type-Proof Γ e₂ t₁ → Type-Proof Γ (App e₁ e₂) t₂

  data IsVal-Proof (Γ : Context) : Term Γ → Set where
    IsVal-True : IsVal-Proof Γ True
    IsVal-False : IsVal-Proof Γ False
    IsVal-Fun : (t : Type) (e : Term (Γ , t)) (t′ : Type) → Type-Proof Γ (Fun t e) (Function t t′) → IsVal-Proof Γ (Fun t e)

  var-equal : (Γ : Context) → Variable Γ → Variable Γ → Bool
  var-equal (Δ , t) (inj₂ _) (inj₂ _) = true
  var-equal (Δ , t) (inj₁ _) (inj₂ _) = false
  var-equal (Δ , t) (inj₂ _) (inj₁ _) = false
  var-equal (Δ , t) (inj₁ i) (inj₁ j) = var-equal Δ i j
  var-equal Empty ()
  
  _-_ : (Γ : Context) → Variable Γ → Context
  (Δ , t) - (inj₂ (Box t)) = Δ
  (Δ , t) - (inj₁ x) = (Δ - x) , t
  Empty - ()

  maybe-map : {A B : Set} → (A → B) → Maybe A → Maybe B
  maybe-map f (just x) = just (f x)
  maybe-map f nothing = nothing

  subst-var : (Γ : Context) (v : Variable Γ) → Variable Γ → Maybe (Variable (Γ - v))
  subst-var (Δ , t) (inj₁ x) (inj₁ x₁) = maybe-map (λ x → inj₁ x) (subst-var Δ x x₁)
  subst-var (Δ , t) (inj₁ x) (inj₂ y) = just (inj₂ y)
  subst-var (Δ , t) (inj₂ (Box t)) (inj₁ x) = just x
  subst-var (Δ , t) (inj₂ (Box t)) (inj₂ y₁) = nothing
  subst-var Empty () _
  
  weaken-var : (Γ : Context) (v : Variable Γ) → Variable (Γ - v) → Variable Γ
  weaken-var (Δ , t) (inj₁ x) (inj₁ x₁) = inj₁ (weaken-var Δ x x₁)
  weaken-var (Δ , t) (inj₁ x) (inj₂ y) = inj₂ y
  weaken-var (Δ , t) (inj₂ (Box t)) w with (Δ , t) - (inj₂ (Box t))
  weaken-var (Δ , t) (inj₂ (Box t)) ()       | Empty
  weaken-var (Δ , t) (inj₂ (Box t)) w       | Ε , t′ = inj₁ w
  weaken-var Empty () _

  weaken : (Γ : Context) (v : Variable Γ) → Term (Γ - v) → Term Γ
  weaken Γ v True = True
  weaken Γ v False = False
  weaken Γ v (Fun t e) = Fun t (weaken (Γ , t) (inj₁ v) e)
  weaken Γ v (App e₁ e₂) = App (weaken Γ v e₁) (weaken Γ v e₂)
  weaken Γ v (Var v₁) = Var (weaken-var Γ v v₁)

  weaken-type-proof : (Γ : Context) (v : Variable Γ) (e : Term (Γ - v)) (t : Type) → Type-Proof (Γ - v) e t → Type-Proof Γ (weaken Γ v e) t
  weaken-type-proof Γ v .True .Boolean Type-True = Type-True
  weaken-type-proof Γ v .False .Boolean Type-False = Type-False
  weaken-type-proof Γ v .(Var v₁) .(type-var (Γ - v) v₁) (Type-Var v₁) = {!!}
  weaken-type-proof Γ v .(Fun t e) .(Function t t′) (Type-Fun t e t′ p) = Type-Fun t (weaken (Γ , t) (inj₁ v) e) t′
                                                                            (weaken-type-proof (Γ , t) (inj₁ v) e t′ p)
  weaken-type-proof Γ v .(App e₁ e₂) t (Type-App t₁ e₁ .t e₂ p p₁) = Type-App t₁ (weaken Γ v e₁) t (weaken Γ v e₂)
                                                                       (weaken-type-proof Γ v e₁ (Function t₁ t) p)
                                                                       (weaken-type-proof Γ v e₂ t₁ p₁)
  
  subst : (Γ : Context)  (v : Variable Γ) (e :  Term (Γ - v)) → Term Γ → Type-Proof (Γ - v) e (type-var Γ v) → Term (Γ - v)
  subst Γ v e₁ True _ = True
  subst Γ v e₁ False _ = False
  subst Γ v e₁ (Var i) _ with subst-var Γ v i
  subst Γ v e₁ (Var i) _       | nothing = e₁ 
  subst Γ v e₁ (Var i) _       | just x = Var x
  subst Γ v e₁ (Fun t e₂) p = Fun t (subst (Γ , t) (inj₁ v) (weaken ((Γ , t) - inj₁ v) (inj₂ (Box t)) e₁) e₂ (weaken-type-proof ((Γ , t) - inj₁ v) (inj₂ (Box t)) e₁ (type-var Γ v) p))
  subst Γ v e (App e₁ e₂) p = App (subst Γ v e e₁ p) (subst Γ v e e₂ p) 

  data Execution-Proof (Γ : Context) : Term Γ → Term Γ → Set where
    Execution-App₁ : (e₁ : Term Γ) (e₂ : Term Γ) (e₁′ : Term Γ) → Execution-Proof Γ e₁ e₁′ → Execution-Proof Γ (App e₁ e₂) (App e₁′ e₂)
    Execution-App₂ : (e₁ : Term Γ) (e₂ : Term Γ) (e₂′ : Term Γ) → IsVal-Proof Γ e₁ → Execution-Proof Γ e₂ e₂′ → Execution-Proof Γ (App e₁ e₂) (App e₁ e₂′)
    Execution-AppFun : (t₁ : Type) (e₁ : Term (Γ , t₁)) (e₂ : Term Γ) (t₂ : Type) (p : Type-Proof Γ e₂ t₁) → Type-Proof Γ (Fun t₁ e₁) (Function t₁ t₂) → IsVal-Proof Γ e₂
      → Execution-Proof Γ (App (Fun t₁ e₁) e₂) (subst (Γ , t₁) (inj₂ (Box t₁)) e₂ e₁ p)

  Progress : (e : Term Empty) (t : Type) → Type-Proof Empty e t → (IsVal-Proof Empty e) ⊎ (Σ (Term Empty) (λ e′ → Execution-Proof Empty e e′))
  Progress True t Type-True = inj₁ (IsVal-True)
  Progress False t Type-False = inj₁ (IsVal-False)
  Progress (Var v) t (Type-Var ())
  Progress (Fun t e) (Function t t′) (Type-Fun t e t′ p) = inj₁ (IsVal-Fun t e t′ (Type-Fun t e t′ p))
  Progress (App (Var ()) e₂) t₂ (Type-App t₁ (Var ()) t₂ e₂ p₁ p₂)
  Progress (App (Fun t₁ e₁) (Var ())) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ (Var ()) (Type-Fun t₁ e₁ t₂ p₂) p₃)
  Progress (App (Fun t₁ e₁) (Fun t e₂)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(Fun t e₂) (Type-Fun t₁ e₁ t₂ p₂) (Type-Fun t e₂ t′ p′)) = inj₂ (subst (Empty , t₁) (inj₂ (Box t₁)) (Fun t e₂) e₁ (Type-Fun t e₂ t′ p′) , Execution-AppFun t₁ e₁ (Fun t e₂) t₂ (Type-Fun t e₂ t′ p′) (Type-Fun t₁ e₁ t₂ p₂) (IsVal-Fun t e₂ t′ (Type-Fun t e₂ t′ p′)))
  Progress (App (Fun t₁ e₁) (App e₂ e₃)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(App e₂ e₃) (Type-Fun t₁ e₁ t₂ p₂) p₃) with Progress (App e₂ e₃) t₁ p₃
  Progress (App (Fun t₁ e₁) (App e₂ e₃)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(App e₂ e₃) (Type-Fun t₁ e₁ t₂ p₂) p₃)       | inj₁ ()
  Progress (App (Fun t₁ e₁) (App e₂ e₃)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(App e₂ e₃) (Type-Fun t₁ e₁ t₂ p₂) p₃)       | inj₂ pₓ = inj₂ (App (Fun t₁ e₁) (proj₁ pₓ) , Execution-App₂ (Fun t₁ e₁) (App e₂ e₃) (proj₁ pₓ) (IsVal-Fun t₁ e₁ t₂ (Type-Fun t₁ e₁ t₂ p₂)) (proj₂ pₓ))
  Progress (App (Fun t₁ e₁) True) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .True (Type-Fun t₁ e₁ t₂ p₂) p₃) = inj₂ (subst (Empty , t₁) (inj₂ (Box t₁)) True e₁ p₃ , (Execution-AppFun t₁ e₁ True t₂ p₃ (Type-Fun t₁ e₁ t₂ p₂) IsVal-True))
  Progress (App (Fun t₁ e₁) False) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .False (Type-Fun t₁ e₁ t₂ p₂) p₃) = inj₂ (subst (Empty , t₁) (inj₂ (Box t₁)) False e₁ p₃ , (Execution-AppFun t₁ e₁ False t₂ p₃ (Type-Fun t₁ e₁ t₂ p₂) IsVal-False))  
  Progress (App (App e₁ e₃) e₂) t₂ (Type-App t₁ (App e₁ e₃) t₂ .e₂ p₁ p₂) with Progress (App e₁ e₃) (Function t₁ t₂) p₁
  Progress (App (App e₁ e₃) e₂) t₂ (Type-App t₁ (App e₁ e₃) t₂ .e₂ p₁ p₂)       | inj₁ ()
  Progress (App (App e₁ e₃) e₂) t₂ (Type-App t₁ (App e₁ e₃) t₂ .e₂ p₁ p₂)       | inj₂ pₓ = inj₂ ((App (proj₁ pₓ) e₂) , (Execution-App₁ (App e₁ e₃) e₂ (proj₁ pₓ) (proj₂ pₓ)))
  Progress (App True e₂) t₂ (Type-App t₁ True t₂ e₂ () p₂) 
  Progress (App False e₂) t₂ (Type-App t₁ False t₂ e₂ () p₂)

  --Preservation-Subst : (Γ : Context) 
  
  --Preservation : (e : Term Empty) (t : Type) (e′ : Term Empty) → Type-Proof Empty e t → Execution-Proof Empty e e′ → Type-Proof Empty e′ t
  
