{-# OPTIONS --cubical --safe #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism

module cubical_test where

  compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x ; (i = i1) → q j }) (p i)

  data S : Set where
    base : S
    loop : base ≡ base

  data T : Set where
    north : T
    south : T
    ns : north ≡ south
    sn : south ≡ north

  f : S → T
  f base = north
  f (loop i) = compPath ns sn i

  proof : ∀ {A : Set} {B : A → Set} → ((x : A) → B x) → Σ A (λ x → B x)
  proof p = {!!} , {!!}

  g : T → S
  g north = base
  g south = base
  g (ns i) = loop i
  g (sn i) = refl i

  s : ∀ b → f (g b) ≡ b
  s north = refl
  s south = ns
  s (ns i) = {!!}
  s (sn i) = refl

  r : ∀ a → g (f a) ≡ a
  r base = refl
  r (loop i) = refl i
