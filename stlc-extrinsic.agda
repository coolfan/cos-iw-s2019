open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Data.Unit
open import Agda.Builtin.Equality
open import Data.Sum
open import Data.Bool
open import Data.List

module stlc-extrinsic where
  transport : ∀ {l1 l2} {A : Set l1} (C : A →  Set l2) {M N : A} 
              (P : M ≡ N) → C M → C N
  transport C refl x = x

  apd  : ∀ {l1 l2} {B : Set l1} {E : B → Set l2} {b₁ b₂ : B} 
         (f : (x : B) → E x) (β : b₁ ≡ b₂) 
      → transport E β (f b₁) ≡ (f b₂) 
  apd f refl = refl

  sym : ∀ {a} {A : Set a} {M N : A} → (M ≡ N) → (N ≡ M)
  sym refl = refl

  trans : ∀ {a} {A : Set a} {M N P : A} → (M ≡ N) → (N ≡ P) → (M ≡ P)
  trans refl refl = refl

  data ⊥ : Set where

  data Unit : Set where
    unit : Unit

  exfalso : ∀ {a} {A : Set a} → ⊥ → A
  exfalso ()

  num-eq : (i j : ℕ) → (i ≡ j) ⊎ ((i ≡ j) → ⊥)
  num-eq zero zero = inj₁ refl
  num-eq zero (suc j) = inj₂ (λ ())
  num-eq (suc i) zero = inj₂ (λ ())
  num-eq (suc i) (suc j) with num-eq i j
  ...                                        | inj₁ refl = inj₁ refl
  ...                                        | inj₂ neq = inj₂ (λ x → neq (demote x))
    where
    demote : ∀ {i j : ℕ} → (suc i) ≡ (suc j) → i ≡ j
    demote refl = refl

  num-less : ℕ → ℕ → Set
  num-less zero zero = ⊥
  num-less zero (suc j) = Unit
  num-less (suc i) zero = ⊥
  num-less (suc i) (suc j) = num-less i j

  num-less-same-false : ∀ i → num-less i i ≡ ⊥
  num-less-same-false zero = refl
  num-less-same-false (suc i) = num-less-same-false i

  neq-of-less : ∀ i j → num-less i j → (i ≡ j) → ⊥
  neq-of-less i .i p refl = transport (λ X → X) (num-less-same-false i) p
  
  data Type : Set where
    Boolean : Type
    Function : Type → Type → Type

  data Name : Set where
    N : ℕ → Name

  name-eq : (x y : Name) → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
  name-eq (N x) (N y) with num-eq x y
  ...                                      | inj₁ refl = inj₁ refl
  ...                                      | inj₂ neq = inj₂ (lift neq)
    where
    lift : ∀ {i j : ℕ} → ((i ≡ j) → ⊥) → ((N i ≡ N j) → ⊥)
    lift neq refl = neq refl

  Context = List (Name × Type)

  data Term : Set where
    True : Term
    False : Term
    Var : Name → Term
    Fun : Name → Type → Term → Term
    App : Term → Term → Term

  type-of-name : Context → Name → Maybe Type
  type-of-name [] n = nothing
  type-of-name ((x , t) ∷ tl) n with name-eq n x
  ...                                    | inj₁ refl = just t
  ...                                    | inj₂ _ = type-of-name tl n

  type-of-de-brujin-index : Context → ℕ → Maybe Type
  type-of-de-brujin-index [] n = nothing
  type-of-de-brujin-index ((x , t) ∷ tl) zero = just t
  type-of-de-brujin-index ((x , t) ∷ tl) (suc n) = type-of-de-brujin-index tl n

  name-of-de-brujin-index : Context → ℕ → Maybe Name
  name-of-de-brujin-index [] n = nothing
  name-of-de-brujin-index ((fst , snd) ∷ Γ) zero = just fst
  name-of-de-brujin-index ((fst , snd) ∷ Γ) (suc n) = name-of-de-brujin-index Γ n
{-
  name-de-brujin-index-match : ∀ Γ n x₁ → (name-of-de-brujin-index Γ n ≡ just x₁) ⊎ ((name-of-de-brujin-index Γ n ≡ just x₁) → ⊥)
  name-de-brujin-index-match Γ n x with name-of-de-brujin-index Γ n
  ...                                                              | nothing = inj₂ (λ ())
  ...                                                              | just y with name-eq y x
  ...                                                                                 | inj₁ refl = inj₁ refl
  ...                                                                                 | inj₂ neq = inj₂ (lift neq)
    where
    lift : ∀ {x y : Name} → ((x ≡ y) → ⊥) → ((just x ≡ just y) → ⊥)
    lift neq p = neq p
-}

  _∈_ : (Name × Type) → Context → Set
  (x , t) ∈ Γ = type-of-name Γ x ≡ just t

  _∈′_ : (ℕ × Name × Type) → Context → Set
  (i , x , t) ∈′ Γ = (type-of-de-brujin-index Γ i ≡ just t) × (name-of-de-brujin-index Γ i ≡ just x)

  _∈₂_ : (ℕ × Name × Type) → Context → Set
  (i , x , t) ∈₂ Γ = ((x , t) ∈ Γ) × ((i , x , t) ∈′ Γ)
    
  weaken-in-context : ∀ Γ n t n′ t′ → (n , t) ∈ Γ → ((n ≡ n′) → ⊥) → (n , t) ∈ ((n′ , t′) ∷ Γ)
  weaken-in-context Γ n t n′ t′ p neq with name-eq n n′
  ...                                                              | inj₁ refl = exfalso (neq refl)
  ...                                                              | inj₂ _ = p

  weaken-in₂-context : ∀ Γ i n t n′ t′ → (i , n , t) ∈₂ Γ → ((n ≡ n′) → ⊥) → (suc i , n , t) ∈₂ ((n′ , t′) ∷ Γ)
  weaken-in₂-context Γ i n t n′ t′ p neq with name-eq n n′
  ...                                                                  | inj₁ refl = exfalso (neq refl)
  ...                                                                  | inj₂ _ = p

  data Type-Proof (Γ : Context) : Term → Type → Set where
    Type-True : Type-Proof Γ True Boolean
    Type-False : Type-Proof Γ False Boolean
    Type-Var : (n : Name) (t : Type) (p : (n , t) ∈ Γ) → Type-Proof Γ (Var n) t
    Type-Fun : (n : Name) (t t′ : Type) (e : Term) → Type-Proof ((n , t) ∷ Γ) e t′ → Type-Proof Γ (Fun n t e) (Function t t′)
    Type-App : (t t′ : Type) (e₁ e₂ : Term) → Type-Proof Γ e₁ (Function t t′) → Type-Proof Γ e₂ t → Type-Proof Γ (App e₁ e₂) t′

  Uniqueness-of-Types-Var : ∀ Γ n t t′ → (type-of-name Γ n ≡ just t) → (type-of-name Γ n ≡ just t′) → (t ≡ t′)
  Uniqueness-of-Types-Var Γ n t t′ p p′ with trans (sym p) p′
  ...                                                                | refl = refl

  Uniqueness-of-Types : ∀ Γ e t t′ → Type-Proof Γ e t → Type-Proof Γ e t′ → t ≡ t′
  Uniqueness-of-Types Γ True .Boolean .Boolean Type-True Type-True = refl
  Uniqueness-of-Types Γ False .Boolean .Boolean Type-False Type-False = refl
  Uniqueness-of-Types Γ (Var x) t t′ (Type-Var .x .t p) (Type-Var .x .t′ p₁) = Uniqueness-of-Types-Var Γ x t t′ p p₁
  Uniqueness-of-Types Γ (Fun x t e) .(Function t t′₁) .(Function t t′) (Type-Fun .x t t′₁ .e p) (Type-Fun .x t t′ .e p′) with Uniqueness-of-Types ((x , t) ∷ Γ) e t′₁ t′ p p′
  ...                                                                                                                                                                                          | refl = refl
  Uniqueness-of-Types Γ (App e e₁) t t′ (Type-App t₁ .t .e .e₁ p p₁) (Type-App t₂ .t′ .e .e₁ p′ p′₁) with Uniqueness-of-Types Γ e (Function t₁ t) (Function t₂ t′) p p′ | Uniqueness-of-Types Γ e₁ t₁ t₂ p₁ p′₁
  ...                                                                                                                                                          | refl                                                                                             | refl = refl

  data IsVal-Proof : Term → Set where
    IsVal-True : IsVal-Proof True
    IsVal-False : IsVal-Proof False
    IsVal-Fun : (n : Name) (t t′ : Type) (e : Term) → Type-Proof [] (Fun n t e) (Function t t′) → IsVal-Proof (Fun n t e) 

  remove : (Γ : Context) (n : ℕ) → Context
  remove [] n = []
  remove ((x , t) ∷ Γ) zero = Γ
  remove ((x , t) ∷ Γ) (suc n) = (x , t) ∷ (remove Γ n)

  data IsBase : Context → Context → Set where
    Null : ∀ Δ → IsBase [] Δ
    Extend : ∀ Γ Δ n t → IsBase Γ Δ → IsBase ((n , t) ∷ Γ) ((n , t) ∷ Δ)

  type-var-with-base : ∀ Γ Δ n t → IsBase Γ Δ → ((n , t) ∈ Γ) → ((n , t) ∈ Δ)
  type-var-with-base [] Δ n t b ()
  type-var-with-base (x ∷ Γ) [] n t () p
  type-var-with-base ((fst , snd) ∷ Γ) ((.fst , .snd) ∷ Δ) n t (Extend .Γ .Δ .fst .snd b) p with name-eq n fst
  ...                                                                                                                                            | inj₁ refl = p
  ...                                                                                                                                            | inj₂ neq = type-var-with-base Γ Δ n t b p

  weaken-type-proof : ∀ Γ Δ e t → Type-Proof Γ e t → IsBase Γ Δ → Type-Proof Δ e t
  weaken-type-proof Γ Δ .True .Boolean Type-True b = Type-True
  weaken-type-proof Γ Δ .False .Boolean Type-False b = Type-False
  weaken-type-proof Γ Δ .(Var n) t (Type-Var n .t p) b = Type-Var n t (type-var-with-base Γ Δ n t b p)
  weaken-type-proof Γ Δ .(Fun n t e) .(Function t t′) (Type-Fun n t t′ e p) b = Type-Fun n t t′ e
                                                                             (weaken-type-proof ((n , t) ∷ Γ) ((n , t) ∷ Δ) e t′ p
                                                                              (Extend Γ Δ n t b))
  weaken-type-proof Γ Δ .(App e₁ e₂) t (Type-App t₁ .t e₁ e₂ p p₁) b = Type-App t₁ t e₁ e₂ (weaken-type-proof Γ Δ e₁ (Function t₁ t) p b)
                                                                    (weaken-type-proof Γ Δ e₂ t₁ p₁ b)

  to-maybe : ∀ {a} {A : Set a} → A → Maybe A
  to-maybe n = just n

  lift-eq-just : ∀ {a} {A : Set a} {n n′ : A} → ((n ≡ n′) → ⊥) → ((to-maybe n ≡ to-maybe n′) → ⊥)
  lift-eq-just neq refl = neq refl

  peel-eq-just : ∀ {a} {A : Set a} {n n′ : A} → (to-maybe n ≡ to-maybe n′) → (n ≡ n′)
  peel-eq-just refl = refl

  chain-eq-neq : ∀ {a} {A : Set a} {M N Q : A} → M ≡ N → ((N ≡ Q) → ⊥) → (M ≡ Q) → ⊥
  chain-eq-neq refl neq refl = neq refl

  unaffected : ∀ Γ i n t → ((name-of-de-brujin-index Γ i ≡ just n) → ⊥) → Type-Proof Γ (Var n) t → Type-Proof (remove Γ i) (Var n) t
  unaffected [] i n t neq (Type-Var .n .t ())
  unaffected ((fst , snd) ∷ Γ) i n t neq (Type-Var .n .t p) with name-eq n fst
  unaffected ((fst , snd) ∷ Γ) zero n t neq (Type-Var .n .t p) | inj₂ _ = Type-Var n t p
  unaffected ((fst , snd) ∷ Γ) (suc i) n t neq (Type-Var .n .t p) | inj₂ neq′ with unaffected Γ i n t neq (Type-Var n t p)
  unaffected ((fst , snd) ∷ Γ) (suc i) n t neq (Type-Var .n .t p) | inj₂ neq′ | Type-Var .n .t p₁ = Type-Var n t (weaken-in-context (remove Γ i) n t fst snd p₁ neq′)
  unaffected ((.n , snd) ∷ Γ) i n t neq (Type-Var .n .t p) | inj₁ refl with name-eq n n
  ...                                                                                                           | inj₂ lol = exfalso (lol refl)
  unaffected ((.n , snd) ∷ Γ) i n t neq (Type-Var .n .t p) | inj₁ refl | inj₁ refl with peel-eq-just p
  unaffected ((.n , .t) ∷ Γ) zero n t neq (Type-Var .n .t p) | inj₁ refl | inj₁ refl | refl = exfalso (neq refl)
  unaffected ((.n , .t) ∷ Γ) (suc i) n t neq (Type-Var .n .t p) | inj₁ refl | inj₁ refl | refl = Type-Var n t (helper (remove Γ i) n t)
    where
    helper : ∀ Γ n t → (n , t) ∈ ((n , t) ∷ Γ)
    helper Γ n t with name-eq n n
    ...                       | inj₁ refl = refl
    ...                       | inj₂ neq = exfalso (neq refl)

  shadowing : ∀ Γ i j n t t₁ e t′ → (i , n , t) ∈₂ Γ → Type-Proof Γ e t′ → (j , n , t₁) ∈′ Γ → (num-less i j) → Type-Proof (remove Γ j) e t′
  shadowing Γ i j n t tₐ .True .Boolean p Type-True p′′ neq = Type-True
  shadowing Γ i j n t tₐ .False .Boolean p Type-False p′′ neq = Type-False
  shadowing Γ i j n t tₐ .(Var n₁) t′ p (Type-Var n₁ .t′ p₁) p′′ neq with name-eq n₁ n
  ...                                                                                                        | inj₂ neq′ = unaffected Γ j n₁ t′ (chain-eq-neq (proj₂ p′′) (lift-eq-just (λ x → neq′ (sym x)))) (Type-Var n₁ t′ p₁)
  shadowing Γ i j .n₁ t tₐ .(Var n₁) t′ p (Type-Var n₁ .t′ p₁) p′′ neq | inj₁ refl = Type-Var n₁ t′ (shadowing-var Γ i j n₁ t′ tₐ (transport (λ X → (i , n₁ , X) ∈₂ Γ) (peel-eq-just (trans (sym (proj₁ p)) p₁)) p) p′′ neq)
    where
    shadowing-var : ∀ Γ i j n t t₁ → (i , n , t) ∈₂ Γ → (j , n , t₁) ∈′ Γ → num-less i j → (n , t) ∈ (remove Γ j)
    shadowing-var [] i j n t tₐ (() , snd) p′ neq
    shadowing-var ((fst , snd) ∷ Γ) i j n t tₐ p p′ neq with name-eq fst n
    shadowing-var ((fst , snd) ∷ Γ) i j .fst t tₐ p p′ neq | inj₁ refl with name-eq fst fst
    ...                                                                                                     | inj₂ lol = exfalso (lol refl)
    shadowing-var ((fst , snd) ∷ Γ) zero zero .fst .snd .snd (refl , p) (refl , snd₁) neq | inj₁ refl | inj₁ refl = exfalso neq
    shadowing-var ((fst , snd) ∷ Γ) (suc i) zero .fst .snd .snd (refl , fst₁ , snd₂) (refl , refl) neq | inj₁ refl | inj₁ refl = exfalso neq
    shadowing-var ((fst , snd) ∷ Γ) i (suc j) .fst t tₐ p p′ neq | inj₁ refl | inj₁ refl with name-eq fst fst
    ...                                                                                                                                   | inj₂ lol = exfalso (lol refl)
    ...                                                                                                                                   | inj₁ refl = proj₁ p
      where
      helper : ∀ Γ n t → (n , t) ∈ ((n , t) ∷ Γ)
      helper Γ n t with name-eq n n
      ...                       | inj₁ refl = refl
      ...                       | inj₂ neq = exfalso (neq refl)
    shadowing-var ((fst , snd) ∷ Γ) zero zero n t tₐ p p′ neq | inj₂ neq′ = exfalso neq
    shadowing-var ((fst , snd) ∷ Γ) (suc i) zero n t tₐ p p′ neq | inj₂ neq′ = exfalso neq
    shadowing-var ((fst , snd) ∷ Γ) i (suc j) n t tₐ p p′ neq | inj₂ neq′ with name-eq n fst
    shadowing-var ((fst , snd) ∷ Γ) i (suc j) .fst t tₐ p p′ neq | inj₂ neq′ | inj₁ refl = exfalso (neq′ refl)
    shadowing-var ((fst , snd) ∷ Γ) zero (suc j) n t tₐ p p′ neq | inj₂ neq′ | inj₂ y = exfalso (neq′ (sym (equality Γ n t fst snd ((weaken-in-context Γ n t fst snd (proj₁ p) y) , (proj₂ p)))))
      where
      equality : ∀ Γ n t n′ t′ → (zero , n , t) ∈₂ ((n′ , t′) ∷ Γ) → (n ≡ n′)
      equality Γ n t .n .t (fst , refl , refl) = refl
    shadowing-var ((fst , snd) ∷ Γ) (suc i) (suc j) n t tₐ p p′ neq | inj₂ neq′ | inj₂ _ = shadowing-var Γ i j n t tₐ p p′ neq
  shadowing Γ i j n t tₐ .(Fun n₁ t₁ e) .(Function t₁ t′) p (Type-Fun n₁ t₁ t′ e p′) p′′ neq with name-eq n₁ n
  ...                                                                                                                                             | inj₂ neq′ with shadowing ((n₁ , t₁) ∷ Γ) (suc i) (suc j) n t tₐ e t′ (weaken-in-context Γ n t n₁ t₁ (proj₁ p) (λ x → neq′ (sym x)) , proj₂ p) p′ p′′ neq
    where
    lift-eq-suc : {n n′ : ℕ} → ((n ≡ n′) → ⊥) → ((suc n ≡ suc n′) → ⊥)
    lift-eq-suc neq refl = neq refl
  ...                                                                                                                                                               | pₐ = Type-Fun n₁ t₁ t′ e pₐ
  shadowing Γ i j .n₁ t tₐ .(Fun n₁ t₁ e) .(Function t₁ t′) p (Type-Fun n₁ t₁ t′ e p′) p′′ neq | inj₁ refl with shadowing ((n₁ , t₁) ∷ Γ) zero (suc j) n₁ t₁ tₐ e t′ (helper Γ n₁ t₁ , (refl , refl)) p′ p′′ unit
    where
    helper : ∀ Γ n t → (n , t) ∈ ((n , t) ∷ Γ)
    helper Γ n t with name-eq n n
    ...                       | inj₁ refl = refl
    ...                       | inj₂ neq = exfalso (neq refl)
  ...                                                                                                                                                              | pₐ = Type-Fun n₁ t₁ t′ e pₐ
  shadowing Γ i j n t tₐ .(App e₁ e₂) t′ p (Type-App t₁ .t′ e₁ e₂ p′ p′₁) p′′ neq = Type-App t₁ t′ e₁ e₂ (shadowing Γ i j n t tₐ e₁ (Function t₁ t′) p p′ p′′ neq) (shadowing Γ i j n t tₐ e₂ t₁ p p′₁ p′′ neq)

  subst-aux : ∀ Γ i n t t′ e₂ e₁ (p : (i , n , t) ∈₂ Γ) → Type-Proof [] e₂ t → Type-Proof Γ e₁ t′ → Σ Term (λ x → Type-Proof (remove Γ i) x t′)
  subst-aux Γ i n t .Boolean e₂ .True p p₂ Type-True = True , Type-True
  subst-aux Γ i n t .Boolean e₂ .False p p₂ Type-False = True , Type-True
  subst-aux Γ i n t t′ e₂ .(Var n₁) p p₂ (Type-Var n₁ .t′ p₁) with name-eq n n₁
  subst-aux Γ i .n₁ t t′ e₂ .(Var n₁) (fst , p) p₂ (Type-Var n₁ .t′ p₁) | inj₁ refl = e₂ , transport (λ X → Type-Proof (remove Γ i) e₂ X) (Uniqueness-of-Types Γ (Var n₁) t t′ (Type-Var n₁ t fst) (Type-Var n₁ t′ p₁)) (weaken-type-proof [] (remove Γ i) e₂ t p₂ (Null (remove Γ i)))
  subst-aux Γ i n t t′ e₂ .(Var n₁) (fst , fst₁ , snd) p₂ (Type-Var n₁ .t′ p₁) | inj₂ neq = (Var n₁) , (unaffected Γ i n₁ t′ (chain-eq-neq snd (lift-eq-just neq)) (Type-Var n₁ t′ p₁))
  subst-aux Γ i n t .(Function t₁ t′) e₂ .(Fun n₁ t₁ e) p p₂ (Type-Fun n₁ t₁ t′ e p₁) with name-eq n n₁
  subst-aux Γ i .n₁ t .(Function t₁ t′) e₂ .(Fun n₁ t₁ e) p p₂ (Type-Fun n₁ t₁ t′ e p₁) | inj₁ refl = (Fun n₁ t₁ e) , Type-Fun n₁ t₁ t′ e (shadowing ((n₁ , t₁) ∷ Γ) zero (suc i) n₁ t₁ t e t′ (helper Γ n₁ t₁ , refl , refl) p₁ (proj₂ p) unit) -- shadowing
    where
    helper : ∀ Γ n t → (n , t) ∈ ((n , t) ∷ Γ)
    helper Γ n t with name-eq n n
    ...                       | inj₁ refl = refl
    ...                       | inj₂ neq = exfalso (neq refl)
  ...                                                                                                                                   | inj₂ neq with subst-aux ((n₁ , t₁) ∷ Γ) (suc i) n t t′ e₂ e (weaken-in₂-context Γ i n t n₁ t₁ p neq) p₂ p₁
  ...                                                                                                                                                          | (e′ , p′) = Fun n₁ t₁ e′ , Type-Fun n₁ t₁ t′ e′ p′
  subst-aux Γ i n t t′ e₂ .(App e₁ e₃) p p₂ (Type-App t₁ .t′ e₁ e₃ p₁ p₃) with subst-aux Γ i n t (Function t₁ t′) e₂ e₁ p p₂ p₁ | subst-aux Γ i n t t₁ e₂ e₃ p p₂ p₃
  ...                                                                                                               | (e₁′ , p₁′)                                                           | (e₂′ , p₂′) = App e₁′ e₂′ , Type-App t₁ t′ e₁′ e₂′ p₁′ p₂′

  subst : ∀ Γ i n t t′ e₂ e₁ (p : (i , n , t) ∈₂ Γ) → Type-Proof [] e₂ t → Type-Proof Γ e₁ t′ → Term
  subst Γ i n t t′ e₂ e₁ p p₂ p₁ = proj₁ (subst-aux Γ i n t t′ e₂ e₁ p p₂ p₁)

 
  helper : ∀ Γ n t → (n , t) ∈ ((n , t) ∷ Γ)
  helper Γ n t with name-eq n n
  ...                       | inj₁ refl = refl
  ...                       | inj₂ neq = exfalso (neq refl)
  
  data Execution-Proof : Term → Term → Set where
    Execution-App₁ : (e₁ e₂ e₁′ : Term) → Execution-Proof e₁ e₁′ → Execution-Proof (App e₁ e₂) (App e₁′ e₂)
    Execution-App₂ : (e₁ e₂ e₂′ : Term) → IsVal-Proof e₁ → Execution-Proof e₂ e₂′ → Execution-Proof (App e₁ e₂) (App e₁ e₂′)
    Execution-AppFun : (n : Name) (t t′ : Type) (e₁ e₂ : Term) (p₁ : Type-Proof [(n , t)] e₁ t′) (p₂ : Type-Proof [] e₂ t) → IsVal-Proof e₂ → Execution-Proof (App (Fun n t e₁) e₂) (subst [(n , t)] zero n t t′ e₂ e₁ (helper [] n t , refl , refl) p₂ p₁)


  Progress : (e : Term) (t : Type) → Type-Proof [] e t → IsVal-Proof e ⊎ Σ Term (λ e′ → Execution-Proof e e′)
  Progress .True .Boolean Type-True = inj₁ IsVal-True
  Progress .False .Boolean Type-False = inj₁ IsVal-False
  Progress .(Var n) t (Type-Var n .t ())
  Progress .(Fun n t e) .(Function t t′) (Type-Fun n t t′ e p) = inj₁ (IsVal-Fun n t t′ e (Type-Fun n t t′ e p))
  Progress .(App True e₂) t (Type-App t₁ .t True e₂ () p₁)
  Progress .(App False e₂) t (Type-App t₁ .t False e₂ () p₁)
  Progress .(App (Var x) e₂) t (Type-App t₁ .t (Var x) e₂ (Type-Var .x .(Function t₁ t) ()) p₁)
  Progress .(App (Fun x Boolean e₁) True) t (Type-App .Boolean .t (Fun x .Boolean e₁) True (Type-Fun .x .Boolean .t .e₁ p) Type-True) = inj₂ (subst [(x , Boolean)] zero x Boolean t True e₁ (helper [] x Boolean , refl , refl) Type-True p , Execution-AppFun x Boolean t e₁ True p Type-True IsVal-True)
  Progress .(App (Fun x Boolean e₁) False) t (Type-App .Boolean .t (Fun x .Boolean e₁) False (Type-Fun .x .Boolean .t .e₁ p) Type-False) = inj₂ ((subst [(x , Boolean)] zero x Boolean t False e₁ (helper [] x Boolean , refl , refl) Type-False p) , (Execution-AppFun x Boolean t e₁ False p Type-False IsVal-False))
  Progress .(App (Fun x x₁ e₁) (Var x₂)) t (Type-App t₁ .t (Fun x x₁ e₁) (Var x₂) p (Type-Var .x₂ .t₁ ()))
  Progress .(App (Fun x (Function x₃ t′) e₁) (Fun x₂ x₃ e₂)) t (Type-App .(Function x₃ t′) .t (Fun x .(Function x₃ t′) e₁) (Fun x₂ x₃ e₂) (Type-Fun .x .(Function x₃ t′) .t .e₁ p) (Type-Fun .x₂ .x₃ t′ .e₂ p₁)) = inj₂ ((subst [(x , Function x₃ t′)] zero x (Function x₃ t′) t (Fun x₂ x₃ e₂) e₁ ((helper [] x (Function x₃ t′)) , (refl , refl)) (Type-Fun x₂ x₃ t′ e₂ p₁) p) , (Execution-AppFun x (Function x₃ t′) t e₁ (Fun x₂ x₃ e₂) p
                                                                                                                                                                                                                                                                                                                                                                                      (Type-Fun x₂ x₃ t′ e₂ p₁)
                                                                                                                                                                                                                                                                                                                                                                                      (IsVal-Fun x₂ x₃ t′ e₂ (Type-Fun x₂ x₃ t′ e₂ p₁))))
  Progress .(App (Fun x x₁ e₁) (App e₂ e₃)) t (Type-App t₁ .t (Fun x x₁ e₁) (App e₂ e₃) p p₁) with Progress (App e₂ e₃) t₁ p₁
  Progress .(App (Fun x x₁ e₁) (App e₂ e₃)) t (Type-App t₁ .t (Fun x x₁ e₁) (App e₂ e₃) p p₁) | inj₁ ()
  Progress .(App (Fun x t₁ e₁) (App e₂ e₃)) t (Type-App t₁ .t (Fun x .t₁ e₁) (App e₂ e₃) (Type-Fun .x .t₁ .t .e₁ p) p₁) | inj₂ (e′ , pₓ) = inj₂ ((App (Fun x t₁ e₁) e′) , Execution-App₂ (Fun x t₁ e₁) (App e₂ e₃) e′ (IsVal-Fun x t₁ t e₁ (Type-Fun x t₁ t e₁ p)) pₓ)
  Progress .(App (App e₁ e₃) e₂) t (Type-App t₁ .t (App e₁ e₃) e₂ p p₁) with Progress (App e₁ e₃) (Function t₁ t) p
  Progress .(App (App e₁ e₃) e₂) t (Type-App t₁ .t (App e₁ e₃) e₂ p p₁) | inj₁ ()
  ...                                                                                                                | inj₂ (e′ , pₓ) = inj₂ ((App e′ e₂) , (Execution-App₁ (App e₁ e₃) e₂ e′ pₓ))

  Preservation-Subst : ∀ Γ i n t t′ e₂ e₁ (p : (i , n , t) ∈₂ Γ) (p₂ : Type-Proof [] e₂ t) (p₁ : Type-Proof Γ e₁ t′) → Type-Proof (remove Γ i) (subst Γ i n t t′ e₂ e₁ p p₂ p₁) t′
  Preservation-Subst Γ i n t t′ e₂ e₁ p p₂ p₁ = proj₂ (subst-aux Γ i n t t′ e₂ e₁ p p₂ p₁)

  Preservation : (e e′ : Term) (t : Type) → Type-Proof [] e t → Execution-Proof e e′ → Type-Proof [] e′ t
  Preservation .True e′ .Boolean Type-True ()
  Preservation .False e′ .Boolean Type-False ()
  Preservation .(Var n) e′ t (Type-Var n .t p) ()
  Preservation .(Fun n t e) e′ .(Function t t′) (Type-Fun n t t′ e p) ()
  Preservation .(App e₁ e₂) .(App e₁′ e₂) t (Type-App t₁ .t e₁ e₂ p p₁) (Execution-App₁ .e₁ .e₂ e₁′ x) = Type-App t₁ t e₁′ e₂ (Preservation e₁ e₁′ (Function t₁ t) p x) p₁
  Preservation .(App e₁ e₂) .(App e₁ e₂′) t (Type-App t₁ .t e₁ e₂ p p₁) (Execution-App₂ .e₁ .e₂ e₂′ x x₁) = Type-App t₁ t e₁ e₂′ p (Preservation e₂ e₂′ t₁ p₁ x₁)
  Preservation .(App (Fun n t₂ e₁) e₂) .(proj₁ (subst-aux ((n , t₂) ∷ []) 0 n t₂ t′ e₂ e₁ ((helper [] n t₂) , refl , refl) p₃ p₂)) t (Type-App .t₂ .t .(Fun n t₂ e₁) e₂ (Type-Fun .n .t₂ .t .e₁ p) p₁) (Execution-AppFun n t₂ t′ e₁ .e₂ p₂ p₃ x) = transport (λ X → Type-Proof [] (subst ((n , t₂) ∷ []) zero n t₂ t′ e₂ e₁ ((helper [] n t₂) , refl , refl) p₃ p₂) X) (Uniqueness-of-Types [(n , t₂)] e₁ t′ t p₂ p) (Preservation-Subst [(n , t₂)] zero n t₂ t′ e₂ e₁ ((helper [] n t₂) , (refl , refl)) p₃ p₂)


