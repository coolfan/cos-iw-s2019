open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Data.Unit
open import Data.List
open import Agda.Builtin.Equality
open import Data.Sum
open import Data.Bool

module stlc-intrinsic where

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

  type-var : (Γ : Context) → Variable Γ → Type
  type-var (Δ , t) (inj₂ (Box t)) = t
  type-var (Δ , t) (inj₁ x) = type-var Δ x
  type-var Empty ()
  
  data Term (Γ : Context) : Type → Set where
    Var : ∀ t v → (type-var Γ v ≡ t) → Term Γ t
    Fun : ∀ t t′ → Term (Γ , t) t′ → Term Γ (Function t t′)
    App : ∀ t t′ → Term Γ (Function t t′) → Term Γ t → Term Γ t′
    True : Term Γ Boolean
    False : Term Γ Boolean

  data IsVal-Proof (Γ : Context) : (t : Type) → Term Γ t → Set where
    IsVal-True : IsVal-Proof Γ Boolean True
    IsVal-False : IsVal-Proof Γ Boolean False
    IsVal-Fun : (t t′ : Type) (e : Term (Γ , t) t′) → IsVal-Proof Γ (Function t t′) (Fun t t′ e)
  
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

  weaken : ∀ Γ v t → Term (Γ - v) t → Term Γ t
  weaken Γ v .Boolean True = True
  weaken Γ v .Boolean False = False
  weaken Γ v .(Function t t′) (Fun t t′ e) = Fun t t′ (weaken (Γ , t) (inj₁ v) t′ e)
  weaken Γ v t′ (App t t′ e₁ e₂) = App t t′ (weaken Γ v (Function t t′) e₁) (weaken Γ v t e₂)
  weaken Γ v t (Var t′ v₁ refl) = Var t′ (weaken-var Γ v v₁) (eq-proof Γ v v₁)
    where
    eq-proof : ∀ Γ v v₁ → (type-var Γ (weaken-var Γ v v₁)) ≡ (type-var (Γ - v) v₁)
    eq-proof (Δ , t) (inj₁ x) (inj₁ x₁) = eq-proof Δ x x₁
    eq-proof (Δ , t) (inj₁ x) (inj₂ (Box t′)) = refl
    eq-proof (Δ , t) (inj₂ (Box t)) v₁ with (Δ , t) - (inj₂ (Box t))
    eq-proof (Δ , t) (inj₂ (Box t)) ()        | Empty
    eq-proof (Δ , t) (inj₂ (Box t)) v₁       | _ , _ = refl
    eq-proof Empty () _


  subst : ∀ Γ v t → Term (Γ - v) (type-var Γ v) → Term Γ t → Term (Γ - v) t
  subst Γ v .(type-var Γ v₁) e₂ (Var _ v₁ refl) with subst-var Γ v v₁
  subst Γ v .(type-var Γ v₁) e₂ (Var _ v₁ refl)       | inj₂ refl = e₂
  subst Γ v .(type-var Γ v₁) e₂ (Var t v₁ refl)       | inj₁ (x , p) = transport (\ X → Term (Γ - v) X) refl (Var t x p)
  subst Γ v .(Function t t′) e₂ (Fun t t′ e₁) = Fun t t′ (subst (Γ , t) (inj₁ v) t′ (weaken ((Γ - v) , t) (inj₂ (Box t)) (type-var Γ v) e₂) e₁)
  subst Γ v t e₂ (App t₁ .t e₁ e₃) = App t₁ t (subst Γ v (Function t₁ t) e₂ e₁) (subst Γ v t₁ e₂ e₃)
  subst Γ v .Boolean e₂ True = True
  subst Γ v .Boolean e₂ False = False

  data Execution-Proof (Γ : Context) : (t : Type) → Term Γ t → Term Γ t → Set where
    Execution-App₁ : (t t′ : Type) (e₁ : Term Γ (Function t t′)) (e₂ : Term Γ t) (e₁′ : Term Γ (Function t t′)) → Execution-Proof Γ (Function t t′) e₁ e₁′ → Execution-Proof Γ t′ (App t t′ e₁ e₂) (App t t′ e₁′ e₂)
    Execution-App₂ : (t t′ : Type) (e₁ : Term Γ (Function t t′)) (e₂ : Term Γ t) (e₂′ : Term Γ t) → IsVal-Proof Γ (Function t t′) e₁ → Execution-Proof Γ t e₂ e₂′ → Execution-Proof Γ t′ (App t t′ e₁ e₂) (App t t′ e₁ e₂′)
    Execution-AppFun : (t t′ : Type) (e₁ : Term (Γ , t) t′) (e₂ : Term Γ t) → IsVal-Proof Γ t e₂ → Execution-Proof Γ t′ (App t t′ (Fun t t′ e₁) e₂) (subst (Γ , t) (inj₂ (Box t)) t′ e₂ e₁)

  Progress : (t : Type) (e : Term Empty t) → (IsVal-Proof Empty t e) ⊎ (Σ (Term Empty t) (λ e′ → Execution-Proof Empty t e e′))
  Progress t (Var .t () x)
  Progress .(Function t t′) (Fun t t′ e) = inj₁ (IsVal-Fun t t′ e)
  Progress t (App t₁ .t (Var .(Function t₁ t) () x) e₁)
  Progress t (App t₁ .t (Fun .t₁ .t e) (Var .t₁ () x))
  Progress t (App .(Function t₁ t′) .t (Fun .(Function t₁ t′) .t e) (Fun t₁ t′ e₁)) = inj₂ (subst (Empty , (Function t₁ t′)) (inj₂ (Box (Function t₁ t′))) t (Fun t₁ t′ e₁) e , Execution-AppFun (Function t₁ t′) t e (Fun t₁ t′ e₁)
                                                                                                                                                                                  (IsVal-Fun t₁ t′ e₁))
  Progress t (App t₁ .t (Fun .t₁ .t e) (App t₂ .t₁ e₁ e₂)) with Progress t₁ (App t₂ t₁ e₁ e₂)
  ...                                                                                       | inj₁ ()
  ...                                                                                       | inj₂ (e′ , x) = inj₂
                                                                                                                (App t₁ t (Fun t₁ t e) e′ ,
                                                                                                                 Execution-App₂ t₁ t (Fun t₁ t e) (App t₂ t₁ e₁ e₂) e′
                                                                                                                 (IsVal-Fun t₁ t e) x)
  Progress t (App .Boolean .t (Fun .Boolean .t e) True) = inj₂ (subst (Empty , Boolean) (inj₂ (Box Boolean)) t True e , Execution-AppFun Boolean t e True IsVal-True)
  Progress t (App .Boolean .t (Fun .Boolean .t e) False) = inj₂ (subst (Empty , Boolean) (inj₂ (Box Boolean)) t False e , Execution-AppFun Boolean t e False IsVal-False)
  Progress t (App t₁ .t (App t₂ .(Function t₁ t) e e₂) e₁) with Progress (Function t₁ t) (App t₂ (Function t₁ t) e e₂)
  ...                                                                                         | inj₁ ()
  ...                                                                                         | inj₂ (e′ , x) = inj₂ ((App t₁ t e′ e₁) , (Execution-App₁ t₁ t (App t₂ (Function t₁ t) e e₂) e₁ e′ x))
  Progress .Boolean True = inj₁ IsVal-True
  Progress .Boolean False = inj₁ IsVal-False

  data Type-Proof (Γ : Context) : (t : Type) → Term Γ t → Set where
    Proof : (t : Type) (e : Term Γ t) → Type-Proof Γ t e

  Preservation : (t : Type) (e e′ : Term Empty t) → Execution-Proof Empty t e e′ → Type-Proof Empty t e′
  Preservation t e e′ x = Proof t e′

  step : (t : Type) (e : Term Empty t) → Term Empty t
  step t e with Progress t e
  ...                 | inj₁ _ = e
  ...                 | inj₂ (e′ , _) = e′

  eval : (t : Type) (e : Term Empty t) → ℕ → Term Empty t
  eval t e zero = e
  eval t e (suc n) = eval t (step t e) n

