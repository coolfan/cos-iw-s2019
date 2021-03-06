open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Data.Unit
open import Data.List
open import Agda.Builtin.Equality
open import Data.Sum
open import Data.Bool

module stlc where

  transport : ∀ {l1 l2} {A : Set l1} (C : A →  Set l2) {M N : A} 
              (P : M ≡ N) → C M → C N
  transport C refl x = x

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
    Type-Var : ∀ v → Type-Proof Γ (Var v) (type-var Γ v) 
    Type-Fun : (t : Type) (e : Term (Γ , t)) (t′ : Type) → Type-Proof (Γ , t) e t′ → Type-Proof Γ (Fun t e) (Function t t′)
    Type-App : (t₁ : Type) (e₁ : Term Γ) (t₂ : Type) (e₂ : Term Γ) → Type-Proof Γ e₁ (Function t₁ t₂) → Type-Proof Γ e₂ t₁ → Type-Proof Γ (App e₁ e₂) t₂

  Uniqueness-of-Type : ∀ Γ e t t′ → (Type-Proof Γ e t) → (Type-Proof Γ e t′) → t ≡ t′
  Uniqueness-of-Type Γ (Var x) .(type-var Γ x) .(type-var Γ x) (Type-Var .x) (Type-Var .x) = refl
  Uniqueness-of-Type Γ (Fun t₁ e) .(Function t₁ t′₁) .(Function t₁ t′) (Type-Fun .t₁ .e t′₁ p) (Type-Fun .t₁ .e t′ p′) with Uniqueness-of-Type (Γ , t₁) e t′₁ t′ p p′
  Uniqueness-of-Type Γ (Fun t₁ e) .(Function t₁ t′₁) .(Function t₁ t′) (Type-Fun .t₁ .e t′₁ p) (Type-Fun .t₁ .e t′ p′)       | refl = refl
  Uniqueness-of-Type Γ (App e e₁) t t′ (Type-App t₁ .e .t .e₁ p p₁) (Type-App t₂ .e .t′ .e₁ p′ p′₁) with Uniqueness-of-Type Γ e (Function t₁ t) (Function t₂ t′) p p′ | Uniqueness-of-Type Γ e₁ t₁ t₂ p₁ p′₁
  Uniqueness-of-Type Γ (App e e₁) t t′ (Type-App t₁ .e .t .e₁ p p₁) (Type-App t₂ .e .t′ .e₁ p′ p′₁)       | refl                                                                                            | refl = refl
  Uniqueness-of-Type Γ True .Boolean .Boolean Type-True Type-True = refl
  Uniqueness-of-Type Γ False .Boolean .Boolean Type-False Type-False = refl

  data IsVal-Proof : Term Empty → Set where
    IsVal-True : IsVal-Proof True
    IsVal-False : IsVal-Proof False
    IsVal-Fun : (t : Type) (e : Term (Empty , t)) (t′ : Type) → Type-Proof Empty (Fun t e) (Function t t′) → IsVal-Proof (Fun t e)
  
  _-_ : ∀ Γ → Variable Γ → Context
  (Δ , t) - (inj₂ (Box t)) = Δ
  (Δ , t) - (inj₁ x) = (Δ - x) , t
  Empty - ()

  weaken-var : ∀ Γ v → Variable (Γ - v) → Variable Γ
  weaken-var (Δ , t) (inj₁ x) (inj₁ x₁) = inj₁ (weaken-var Δ x x₁)
  weaken-var (Δ , t) (inj₁ x) (inj₂ y) = inj₂ y
  weaken-var (Δ , t) (inj₂ (Box t)) w with (Δ , t) - (inj₂ (Box t))
  weaken-var (Δ , t) (inj₂ (Box t)) ()       | Empty
  weaken-var (Δ , t) (inj₂ (Box t)) w       | Ε , t′ = inj₁ w
  weaken-var Empty () _

  subst-var : ∀ Γ v i → (Σ (Variable (Γ - v)) (λ x → type-var (Γ - v) x ≡ type-var Γ i )) ⊎ (v ≡ i)
  subst-var (Δ , t) (inj₁ x) (inj₁ x₁) with subst-var Δ x x₁
  subst-var (Δ , t) (inj₁ x) (inj₁ x₁)       | inj₁ (w , p) = inj₁ (inj₁ w , p)
  subst-var (Δ , t) (inj₁ x) (inj₁ x₁)       | inj₂ refl = inj₂ refl
  subst-var (Δ , t) (inj₁ x) (inj₂ (Box t)) = inj₁ (inj₂ (Box t) , refl)
  subst-var (Δ , t) (inj₂ (Box t)) (inj₁ x) = inj₁ (x , refl)
  subst-var (Δ , t) (inj₂ (Box t)) (inj₂ (Box t)) = inj₂ refl
  subst-var Empty () _ 

  weaken : ∀ Γ v → Term (Γ - v) → Term Γ
  weaken Γ v True = True
  weaken Γ v False = False
  weaken Γ v (Fun t e) = Fun t (weaken (Γ , t) (inj₁ v) e)
  weaken Γ v (App e₁ e₂) = App (weaken Γ v e₁) (weaken Γ v e₂)
  weaken Γ v (Var v₁) = Var (weaken-var Γ v v₁)

  weaken-type-proof : ∀ Γ v e t → Type-Proof (Γ - v) e t → Type-Proof Γ (weaken Γ v e) t
  weaken-type-proof Γ v .True .Boolean Type-True = Type-True
  weaken-type-proof Γ v .False .Boolean Type-False = Type-False
  weaken-type-proof Γ v .(Var v₁) .(type-var (Γ - v) v₁) (Type-Var v₁) = transport (\ X → Type-Proof Γ (Var (weaken-var Γ v v₁)) X) (eq-proof Γ v v₁) (Type-Var (weaken-var Γ v v₁))
    where
    eq-proof : ∀ Γ v v₁ → (type-var Γ (weaken-var Γ v v₁)) ≡ (type-var (Γ - v) v₁)
    eq-proof (Δ , t) (inj₁ x) (inj₁ x₁) = eq-proof Δ x x₁
    eq-proof (Δ , t) (inj₁ x) (inj₂ (Box t′)) = refl
    eq-proof (Δ , t) (inj₂ (Box t)) v₁ with (Δ , t) - (inj₂ (Box t))
    eq-proof (Δ , t) (inj₂ (Box t)) ()        | Empty
    eq-proof (Δ , t) (inj₂ (Box t)) v′        | Ε , t′ = refl
    eq-proof Empty () _
  weaken-type-proof Γ v .(Fun t e) .(Function t t′) (Type-Fun t e t′ p) = Type-Fun t (weaken (Γ , t) (inj₁ v) e) t′ (weaken-type-proof (Γ , t) (inj₁ v) e t′ p)
  weaken-type-proof Γ v .(App e₁ e₂) t (Type-App t₁ e₁ .t e₂ p p₁) = Type-App t₁ (weaken Γ v e₁) t (weaken Γ v e₂) (weaken-type-proof Γ v e₁ (Function t₁ t) p) (weaken-type-proof Γ v e₂ t₁ p₁)

  
  subst-aux : ∀ Γ v t e₂ e₁ → Type-Proof (Γ - v) e₂ (type-var Γ v) → Type-Proof Γ e₁ t → Σ (Term (Γ - v)) (λ x → Type-Proof (Γ - v) x t)
  subst-aux Γ v .Boolean e₂ True p₂ Type-True = (True , Type-True)
  subst-aux Γ v .Boolean e₂ False p₂ Type-False = (False , Type-False)
  subst-aux Γ v t e₂ (Var i) p₂ p₁                                 with subst-var Γ v i
  subst-aux Γ v t e₂ (Var v) p₂ (Type-Var v)                     | inj₂ refl = (e₂ , p₂) 
  subst-aux Γ v .(type-var Γ i) e₂ (Var i) p₂ (Type-Var i)  | inj₁ (x , p) = (Var x , transport (\ X → Type-Proof (Γ - v) (Var x) X) p (Type-Var x))
  subst-aux Γ v .(Function t′ t′′) e₂ (Fun t′ e₂′) p₂ (Type-Fun t′ e₂′ t′′ p₁′) with subst-aux (Γ , t′) (inj₁ v) t′′ (weaken ((Γ , t′) - inj₁ v) (inj₂ (Box t′)) e₂) e₂′ (weaken-type-proof ((Γ , t′) - inj₁ v) (inj₂ (Box t′)) e₂ (type-var Γ v) p₂) p₁′
  ...                                                                                                                     | (e′ , p′) = Fun t′ e′ , Type-Fun t′ e′ t′′ p′
  subst-aux Γ v t e (App e₁ e₂) p (Type-App t₁ e₁ t e₂ p₁ p₂) with subst-aux Γ v (Function t₁ t) e e₁ p p₁ | subst-aux Γ v t₁ e e₂ p p₂
  ...                                                                                                | (e₁′ , p₁′)                                                 | (e₂′ , p₂′) = App e₁′ e₂′ , Type-App t₁ e₁′ t e₂′ p₁′ p₂′

  subst : ∀ Γ v t e₂ e₁ → Type-Proof (Γ - v) e₂ (type-var Γ v) → Type-Proof Γ e₁ t → Term (Γ - v)
  subst Γ v t e₂ e₁ p p′ = proj₁ (subst-aux Γ v t e₂ e₁ p p′)

  data Execution-Proof : Term Empty → Term Empty → Set where
    Execution-App₁ : (e₁ e₂ e₁′ : Term Empty) → Execution-Proof e₁ e₁′ → Execution-Proof (App e₁ e₂) (App e₁′ e₂)
    Execution-App₂ : (e₁ e₂ e₂′ : Term Empty) → IsVal-Proof e₁ → Execution-Proof e₂ e₂′ → Execution-Proof (App e₁ e₂) (App e₁ e₂′)
    Execution-AppFun : (t₁ : Type) (e₁ : Term (Empty , t₁)) (e₂ : Term Empty) (t₂ : Type) (p : Type-Proof Empty e₂ t₁) (p′ : Type-Proof (Empty , t₁) e₁ t₂) → IsVal-Proof e₂
      → Execution-Proof (App (Fun t₁ e₁) e₂) (subst (Empty , t₁) (inj₂ (Box t₁)) t₂ e₂ e₁ p p′)

  Progress : (e : Term Empty) (t : Type) → Type-Proof Empty e t → (IsVal-Proof e) ⊎ (Σ (Term Empty) (λ e′ → Execution-Proof e e′))
  Progress True t Type-True = inj₁ (IsVal-True)
  Progress False t Type-False = inj₁ (IsVal-False)
  Progress (Var v) t (Type-Var ())
  Progress (Fun t e) (Function t t′) (Type-Fun t e t′ p) = inj₁ (IsVal-Fun t e t′ (Type-Fun t e t′ p))
  Progress (App (Var ()) e₂) t₂ (Type-App t₁ (Var ()) t₂ e₂ p₁ p₂)
  Progress (App (Fun t₁ e₁) (Var ())) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ (Var ()) (Type-Fun t₁ e₁ t₂ p₂) p₃)
  Progress (App (Fun t₁ e₁) (Fun t e₂)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(Fun t e₂) (Type-Fun t₁ e₁ t₂ p₂) (Type-Fun t e₂ t′ p′)) = inj₂ (subst (Empty , t₁) (inj₂ (Box t₁)) t₂ (Fun t e₂) e₁ (Type-Fun t e₂ t′ p′) p₂ , Execution-AppFun t₁ e₁ (Fun t e₂) t₂ (Type-Fun t e₂ t′ p′) p₂ (IsVal-Fun t e₂ t′ (Type-Fun t e₂ t′ p′)))
  Progress (App (Fun t₁ e₁) (App e₂ e₃)) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .(App e₂ e₃) (Type-Fun t₁ e₁ t₂ p₂) p₃) with Progress (App e₂ e₃) t₁ p₃
  ...                                                                                                                                                                               | inj₁ ()
  ...                                                                                                                                                                               | inj₂ (e′ , x) = inj₂ (App (Fun t₁ e₁) e′ , Execution-App₂ (Fun t₁ e₁) (App e₂ e₃) e′ (IsVal-Fun t₁ e₁ t₂ (Type-Fun t₁ e₁ t₂ p₂)) x)
  Progress (App (Fun t₁ e₁) True) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .True (Type-Fun t₁ e₁ t₂ p₂) p₃) = inj₂ (subst (Empty , t₁) (inj₂ (Box t₁)) t₂ True e₁ p₃ p₂ , (Execution-AppFun t₁ e₁ True t₂ p₃ p₂ IsVal-True))
  Progress (App (Fun t₁ e₁) False) t₂ (Type-App t₁ .(Fun t₁ e₁) t₂ .False (Type-Fun t₁ e₁ t₂ p₂) p₃) = inj₂ (subst (Empty , t₁) (inj₂ (Box t₁)) t₂ False e₁ p₃ p₂ , (Execution-AppFun t₁ e₁ False t₂ p₃ p₂ IsVal-False))  
  Progress (App (App e₁ e₃) e₂) t₂ (Type-App t₁ (App e₁ e₃) t₂ .e₂ p₁ p₂) with Progress (App e₁ e₃) (Function t₁ t₂) p₁
  ...                                                                                                                   | inj₁ ()
  ...                                                                                                                   | inj₂ (e′ , x) = inj₂ ((App e′ e₂) , (Execution-App₁ (App e₁ e₃) e₂ e′ x))
  Progress (App True e₂) t₂ (Type-App t₁ True t₂ e₂ () p₂) 
  Progress (App False e₂) t₂ (Type-App t₁ False t₂ e₂ () p₂)

  Preservation-Subst : ∀ Γ v t e₂ e₁ p p′ → Type-Proof (Γ - v) (subst Γ v t e₂ e₁ p p′) t
  Preservation-Subst Γ v t e₂ e₁ p p′ = proj₂ (subst-aux Γ v t e₂ e₁ p p′)

  Preservation : (e : Term Empty) (t : Type) (e′ : Term Empty) → Type-Proof Empty e t → Execution-Proof e e′ → Type-Proof Empty e′ t
  Preservation .True .Boolean e′ Type-True ()
  Preservation .False .Boolean e′ Type-False ()
  Preservation .(Var v) .(type-var Empty v) e′ (Type-Var v) ()
  Preservation .(Fun t e) .(Function t t′) e′ (Type-Fun t e t′ p) ()
  Preservation .(App e₁ e₂) t .(App e₁′ e₂) (Type-App t₁ e₁ .t e₂ p p₁) (Execution-App₁ .e₁ .e₂ e₁′ q) = Type-App t₁ e₁′ t e₂ (Preservation e₁ (Function t₁ t) e₁′ p q) p₁
  Preservation .(App e₁ e₂) t .(App e₁ e₂′) (Type-App t₁ e₁ .t e₂ p p₁) (Execution-App₂ .e₁ .e₂ e₂′ x q) = Type-App t₁ e₁ t e₂′ p (Preservation e₂ t₁ e₂′ p₁ q)
  Preservation .(App (Fun t₂ e₁) e₂) t .(subst (Empty , t₂) (inj₂ (Box t₂)) t₃ e₂ e₁ p₂ p′) (Type-App .t₂ .(Fun t₂ e₁) .t e₂ (Type-Fun .t₂ .e₁ .t p) p₁) (Execution-AppFun t₂ e₁ .e₂ t₃ p₂ p′ x) = transport (\ X → Type-Proof Empty (subst (Empty , t₂) (inj₂ (Box t₂)) t₃ e₂ e₁ p₂ p′) X) (Uniqueness-of-Type (Empty , t₂) e₁ t₃ t p′ p) (Preservation-Subst (Empty , t₂) (inj₂ (Box t₂)) t₃ e₂ e₁ p₂ p′)
  
  step : (e : Term Empty) (t : Type) → Type-Proof Empty e t → Σ (Term Empty) (λ x → Type-Proof Empty x t)
  step e t p with Progress e t p
  ...                    | inj₁ pv = (e , p)
  ...                    | inj₂ (e′ , x) = (e′ , Preservation e t e′ p x)

  eval : (e : Term Empty) (t : Type) → Type-Proof Empty e t → ℕ → Σ (Term Empty) (λ x → Type-Proof Empty x t)
  eval e t p zero = (e , p)
  eval e t p (suc n) with step e t p
  ...                                | (e′ , p′) = eval e′ t p′ n
  
  Id : Term Empty
  Id = Fun Boolean (Var (inj₂ (Box Boolean)))

  Id-Type-Proof : Type-Proof Empty Id (Function Boolean Boolean)
  Id-Type-Proof = Type-Fun Boolean (Var (inj₂ (Box Boolean))) Boolean
                    (Type-Var (inj₂ (Box Boolean)))

  App-of-Id-True : Term Empty
  App-of-Id-True = App Id True

  App-of-Id-True-Type-Proof : Type-Proof Empty App-of-Id-True Boolean
  App-of-Id-True-Type-Proof = Type-App Boolean (Fun Boolean (Var (inj₂ (Box Boolean)))) Boolean
                                True
                                (Type-Fun Boolean (Var (inj₂ (Box Boolean))) Boolean
                                 (Type-Var (inj₂ (Box Boolean))))
                                Type-True

  App-of-Id-False : Term Empty
  App-of-Id-False = App Id False

  App-of-Id-False-Type-Proof : Type-Proof Empty App-of-Id-False Boolean
  App-of-Id-False-Type-Proof = Type-App Boolean (Fun Boolean (Var (inj₂ (Box Boolean)))) Boolean
                                 False
                                 (Type-Fun Boolean (Var (inj₂ (Box Boolean))) Boolean
                                  (Type-Var (inj₂ (Box Boolean))))
                                 Type-False

  HOId : Term Empty
  HOId = Fun (Function Boolean Boolean) (Var (inj₂ (Box (Function Boolean Boolean))))

  HOId-Type-Proof : Type-Proof Empty HOId (Function (Function Boolean Boolean) (Function Boolean Boolean))
  HOId-Type-Proof = Type-Fun (Function Boolean Boolean)
                      (Var (inj₂ (Box (Function Boolean Boolean))))
                      (Function Boolean Boolean)
                      (Type-Var (inj₂ (Box (Function Boolean Boolean))))

  App-of-HOId-Id : Term Empty
  App-of-HOId-Id = App HOId Id

  App-of-HOId-Id-Type-Proof : Type-Proof Empty App-of-HOId-Id (Function Boolean Boolean)
  App-of-HOId-Id-Type-Proof = Type-App (Function Boolean Boolean)
                                (Fun (Function Boolean Boolean)
                                 (Var (inj₂ (Box (Function Boolean Boolean)))))
                                (Function Boolean Boolean) (Fun Boolean (Var (inj₂ (Box Boolean))))
                                (Type-Fun (Function Boolean Boolean)
                                 (Var (inj₂ (Box (Function Boolean Boolean))))
                                 (Function Boolean Boolean)
                                 (Type-Var (inj₂ (Box (Function Boolean Boolean)))))
                                (Type-Fun Boolean (Var (inj₂ (Box Boolean))) Boolean
                                 (Type-Var (inj₂ (Box Boolean))))
