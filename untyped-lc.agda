{-# OPTIONS --cubical --with-K #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Data.Product hiding (swap)

module untyped-lc where
  compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x ; (i = i1) → q j }) (p i)  

  data ⊥ : Set where

  exfalso : ∀ {ℓ : Level} {A : Set ℓ} → ⊥ → A
  exfalso ()

  data NumEq : ℕ → ℕ → Set where
    Eq : ∀ i → NumEq i i

  num-eq : (i j : ℕ) → (NumEq i j) ⊎ (NumEq i j → ⊥)
  num-eq zero zero = inl (Eq zero)
  num-eq zero (suc j) = inr (λ ())
  num-eq (suc i) zero = inr (λ ())
  num-eq (suc i) (suc j) with num-eq i j
  ...                                     | inl (Eq x) = inl (Eq (suc x))
  ...                                     | inr (neq) = inr (λ x → neq (demote x))
    where
    demote : ∀ {i j : ℕ} → NumEq (suc i) (suc j) → NumEq i j
    demote (Eq (suc k)) = Eq k

  data Term : Set where
    Var : ℕ → Term
    Fun : ℕ → Term → Term
    App : Term → Term → Term

  fresh : ℕ → Term → Set
  fresh n (Var x) = NumEq n x → ⊥
  fresh n (Fun x t) = NumEq n x ⊎ fresh n t
  fresh n (App t t₁) = fresh n t × fresh n t₁

  is-fresh : (n : ℕ) (t : Term) → (fresh n t) ⊎ (fresh n t → ⊥)
  is-fresh n (Var x) with num-eq n x
  ...                              | inl w = inr (λ x → x w)
  ...                              | inr neq = inl neq
  is-fresh n (Fun x t) with num-eq n x
  ...                                | inl w = inl (inl w)
  ...                                | inr neq with is-fresh n t
  ...                                                   | inl fresh-n-t = inl (inr fresh-n-t)
  ...                                                   | inr not-fresh-n-t = inr ((λ { (inl x) → neq x ; (inr y) → not-fresh-n-t y }))
  is-fresh n (App t t₁) with is-fresh n t
  ...                                 | inr not-fresh-n-t = inr (λ x → not-fresh-n-t (fst x))
  ...                                 | inl fresh-n-t with is-fresh n t₁
  ...                                                            | inr not-fresh-n-t₁ = inr (λ x → not-fresh-n-t₁ (snd x))
  ...                                                            | inl fresh-n-t₁ = inl (fresh-n-t , fresh-n-t₁)

  greater-of : ℕ → ℕ → ℕ
  greater-of zero n = n
  greater-of (suc m) zero = suc m
  greater-of (suc m) (suc n) = suc (greater-of m n)

  gen-fresh : (t : Term) → Σ ℕ (λ n → fresh n t)
  gen-fresh t = {!!}

  swap : ℕ → ℕ → Term → Term
  swap m n (Var x) with num-eq m x
  ...                              | inl _ = Var n
  ...                              | inr _ with num-eq n x
  ...                                             | inl _ = Var m
  ...                                             | inr _ = Var x
  swap m n (Fun x t) with num-eq m x
  ...                                 | inl _ = Fun n (swap m n t)
  ...                                 | inr _ with num-eq n x
  ...                                                | inl _ = Fun m (swap m n t)
  ...                                                | inr _ = Fun x (swap m n t)
  swap m n (App t t₁) = App (swap m n t) (swap m n t₁)

  swap-comm : (m n : ℕ) (t : Term) → (swap m n t ≡ swap n m t)
  swap-comm m n (Var x) with num-eq m x
  swap-comm m n (Var x)      | inl (Eq .m) with num-eq n x
  swap-comm m n (Var x)      | inl (Eq .m)      | inl (Eq .m) = refl
  swap-comm m n (Var x)      | inl (Eq .m)      | inr neq with num-eq m m
  swap-comm m n (Var x)      | inl (Eq .m)      | inr neq      | inl (Eq .m) = refl
  swap-comm m n (Var x)      | inl (Eq .m)      | inr neq      | inr neq′ = exfalso (neq′ (Eq m))
  swap-comm m n (Var x)      | inr neq with num-eq n x
  swap-comm m n (Var x)      | inr neq      | inl (Eq .n) = refl
  swap-comm m n (Var x)      | inr neq      | inr neq′ with num-eq m x
  swap-comm m n (Var x)      | inr neq      | inr neq′      | inl (Eq .m) = exfalso (neq (Eq x))
  swap-comm m n (Var x)      | inr neq      | inr neq′      | inr neq′′ = refl
  swap-comm m n (Fun x t) with num-eq m x
  swap-comm m n (Fun x t)      | inl (Eq .m) with num-eq m n
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inl (Eq .m) with num-eq m m
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inl (Eq .m)      | inl (Eq .m) = refl
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inl (Eq .m)      | inr neq = exfalso (neq (Eq m))
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inr neq with num-eq n m
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inr neq      | inl (Eq .m) = exfalso (neq (Eq m))
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inr neq      | inr neq′ with num-eq m m
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inr neq      | inr neq′      | inl (Eq .m) = cong (λ X → Fun n X) (swap-comm m n t)
  swap-comm m n (Fun x t)      | inl (Eq .m)      | inr neq      | inr neq′      | inr neq′′ = exfalso (neq′′ (Eq m))
  swap-comm m n (Fun x t)      | inr neq with num-eq n x
  swap-comm m n (Fun x t)      | inr neq      | inl (Eq .n) = cong (λ X → Fun m X) (swap-comm m x t)
  swap-comm m n (Fun x t)      | inr neq      | inr neq′ with num-eq m x
  swap-comm m n (Fun x t)      | inr neq      | inr neq′      | inl (Eq .m) = exfalso (neq (Eq x))
  swap-comm m n (Fun x t)      | inr neq      | inr neq′      | inr neq′′ = cong (λ X → Fun x X) (swap-comm m n t)
  swap-comm m n (App t t₁) with swap-comm m n t | swap-comm m n t₁
  ...                                             | eq₁                         | eq₂ = compPath part-one part-two
    where
    part-one : App (swap m n t) (swap m n t₁) ≡ App (swap m n t) (swap n m t₁)
    part-one = cong (λ X → App (swap m n t) X) eq₂
    part-two : App (swap m n t) (swap n m t₁) ≡ App (swap n m t) (swap n m t₁)
    part-two = cong (λ X → App X (swap n m t₁)) eq₁

  swap-inv-is-inv : (m n : ℕ) (t : Term) → (t ≡ swap n m (swap m n t))
  swap-inv-is-inv m n (Var x) with num-eq m x
  swap-inv-is-inv m n (Var .m)    | inl (Eq .m) with num-eq n n
  swap-inv-is-inv m n (Var .m)    | inl (Eq .m)      | inl (Eq .n) = refl
  swap-inv-is-inv m n (Var .m)    | inl (Eq .m)      | inr neq = exfalso (neq (Eq n))
  swap-inv-is-inv m n (Var x)      | inr neq with num-eq n x
  swap-inv-is-inv m n (Var .n)      | inr neq     | inl (Eq .n) with num-eq n m
  swap-inv-is-inv m n (Var .n)      | inr neq     | inl (Eq .n)      | inl (Eq .n) = exfalso (neq (Eq n))
  swap-inv-is-inv m n (Var .n)      | inr neq     | inl (Eq .n)      | inr neq′ with num-eq m m
  swap-inv-is-inv m n (Var .n)      | inr neq     | inl (Eq .n)      | inr neq′      | inl (Eq .m) = refl
  swap-inv-is-inv m n (Var .n)      | inr neq     | inl (Eq .n)      | inr neq′      | inr neq′′ = exfalso (neq′′ (Eq m))
  swap-inv-is-inv m n (Var x)      | inr neq      | inr neq′ with num-eq n x
  swap-inv-is-inv m n (Var .n)      | inr neq      | inr neq′      | inl (Eq .n) = exfalso (neq′ (Eq n))
  swap-inv-is-inv m n (Var x)      | inr neq      | inr neq′       | inr neq′′ with num-eq m x
  swap-inv-is-inv m n (Var x)      | inr neq      | inr neq′       | inr neq′′      | inl (Eq .m) = exfalso (neq (Eq x))
  swap-inv-is-inv m n (Var x)      | inr neq      | inr neq′       | inr neq′′      | inr neq′′′ = refl
  swap-inv-is-inv m n (Fun x t) with num-eq m x
  swap-inv-is-inv m n (Fun .m t)    | inl (Eq .m) with num-eq n n
  swap-inv-is-inv m n (Fun .m t)    | inl (Eq .m)      | inl (Eq .n) = cong (λ X → Fun m X) (swap-inv-is-inv m n t)
  swap-inv-is-inv m n (Fun .m t)    | inl (Eq .m)      | inr neq = exfalso (neq (Eq n))
  swap-inv-is-inv m n (Fun x t)      | inr neq with num-eq n x
  swap-inv-is-inv m n (Fun .n t)      | inr neq     | inl (Eq .n) with num-eq n m
  swap-inv-is-inv m n (Fun .n t)      | inr neq     | inl (Eq .n)      | inl (Eq .n) = exfalso (neq (Eq n))
  swap-inv-is-inv m n (Fun .n t)      | inr neq     | inl (Eq .n)      | inr neq′ with num-eq m m
  swap-inv-is-inv m n (Fun .n t)      | inr neq     | inl (Eq .n)      | inr neq′      | inl (Eq .m) = cong (λ X → Fun n X) (swap-inv-is-inv m n t)
  swap-inv-is-inv m n (Fun .n t)      | inr neq     | inl (Eq .n)      | inr neq′      | inr neq′′ = exfalso (neq′′ (Eq m))
  swap-inv-is-inv m n (Fun x t)      | inr neq      | inr neq′ with num-eq n x
  swap-inv-is-inv m n (Fun x t)      | inr neq      | inr neq′      | inl (Eq .n) = exfalso (neq′ (Eq x))
  swap-inv-is-inv m n (Fun x t)      | inr neq      | inr neq′      | inr neq′′ with num-eq m x
  swap-inv-is-inv m n (Fun x t)      | inr neq      | inr neq′      | inr neq′′      | inl (Eq .m) = exfalso (neq (Eq x))
  swap-inv-is-inv m n (Fun x t)      | inr neq      | inr neq′      | inr neq′′      | inr neq′′′ = cong (λ X → Fun x X) (swap-inv-is-inv m n t)
  swap-inv-is-inv m n (App t t₁) with swap-inv-is-inv m n t | swap-inv-is-inv m n t₁
  ...                                                 | eq₁                             | eq₂ = compPath part-one part-two
    where
    part-one : App t t₁ ≡ App t (swap n m (swap m n t₁))
    part-one = cong (λ X → App t X) eq₂
    part-two : App t (swap n m (swap m n t₁)) ≡ App (swap n m (swap m n t)) (swap n m (swap m n t₁))
    part-two = cong (λ X → App X (swap n m (swap m n t₁))) eq₁

  swap-is-self-inv : (m n : ℕ) (t : Term) → (t ≡ swap m n (swap m n t))
  swap-is-self-inv m n t = compPath (swap-inv-is-inv m n t) (swap-comm n m (swap m n t))
  
  data α-Term : Set where
    T : Term → α-Term
    α : (t : Term) (x y : ℕ) → fresh x t → fresh y t → T t ≡ T (swap x y t)

  lc-subst : ℕ → Term → Term → Term
  lc-subst n e₂ e₁ = {!!}
 
  α-subst : ℕ → Term → α-Term → α-Term
  α-subst n e₂ (T (Var x)) = {!!}
  α-subst n e₂ (T (Fun x x₁)) = {!!}
  α-subst n e₂ (T (App x x₁)) = T (App {!!} {!!})
  α-subst n e₂ (α t x y x₁ x₂ i) = {!!}
