{-# OPTIONS --without-K --safe #-}

module ch01 where

  open import Agda.Builtin.Equality
  open import Agda.Primitive
  -- open import Agda.Builtin.Cubical.Path public
  -- open import Agda.Primitive public using ( Level ; _⊔_ ; Setω )

  -- variable ℓ : Level

  -- refl : {A : Set ℓ} (x : A) → x ≡ x
  -- refl x = λ _ → x

  module defs where

    data _×_ (A B : Set) : Set where
      _,_ : A → B → A × B

    pr₁ : {A B : Set} → A × B → A
    pr₁ (a , b) = a

    pr₂ : {A B : Set} → A × B → B
    pr₂ (a , b) = b

    data Σ (A : Set) (B : A → Set) : Set where
      _,_ : (a : A) → B a → Σ A B

    π₁ : {A : Set}{B : A → Set} → Σ A B → A
    π₁ (a , b) = a

    π₂ : {A : Set}{B : A → Set} → (p : Σ A B) → B (π₁ p)
    π₂ (a , b) = b

    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ

    subst : {A : Set} (C : A → Set) {x y : A} → x ≡ y → C x → C y
    subst C refl cₓ = cₓ

    cong :
      {A : Set}
      {B : Set}
      (f : A → B)
      {x y : A}
      (p : x ≡ y)
      → -----------
      f x ≡ f y
    cong _ refl = refl

  module ex01 where

    open defs

    _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
    g ∘ f = \ x → g (f x)

  module ex02 where

    open defs

    rec-× : {A B C : Set} -> (A → B → C) → A × B → C
    rec-× g p = g (pr₁ p) (pr₂ p)

    rec-×-β : {A B C : Set} -> (a : A)(b : B)(g : A → B → C) → rec-× g (a , b) ≡ g a b
    rec-×-β a b g = refl

    rec-Σ : {A C : Set}{B : A → Set} → ((a : A) → B a → C) → Σ A B → C
    rec-Σ g p = g (π₁ p) (π₂ p)

    rec-Σ-β : {A C : Set}{B : A → Set} → (a : A)(b : B a)(g : (a : A) → B a → C) → rec-Σ g (a , b) ≡ g a b
    rec-Σ-β a b g = refl

  module ex03 where

    open defs

    uniq-× : {A B : Set} → (p : A × B) → (pr₁ p , pr₂ p) ≡ p
    uniq-× (a , b) = refl

    ind-× : {A B : Set} → (C : A × B → Set) → ((a : A)(b : B) → C (a , b)) → (p : A × B) → C p
    ind-× C g p = subst C (uniq-× p) (g (pr₁ p) (pr₂ p))

    uniq-Σ : {A : Set}{B : A → Set} → (p : Σ A B) → (π₁ p , π₂ p) ≡ p
    uniq-Σ (a , b) = refl

    ind-Σ : {A : Set}{B : A → Set} → (C : Σ A B → Set) → ((a : A) → (b : B a) → C (a , b)) → (p : Σ A B) → C p
    ind-Σ C g p = subst C (uniq-Σ p) (g (π₁ p) (π₂ p))

  module ex04 where

    open defs

    iter : {C : Set} → C → (C → C) → ℕ → C
    iter c₀ cₛ zero = c₀
    iter c₀ cₛ (succ n) = cₛ (iter c₀ cₛ n)

    module _ {C : Set} (c₀ : C) (cₛ : ℕ → C → C) where

      rec : ℕ → C
      rec zero = c₀
      rec (succ n) = cₛ n (rec n)

      cₛ' : ℕ × C → ℕ × C
      cₛ' p = (succ (pr₁ p) , cₛ (pr₁ p) (pr₂ p))

      rec' : ℕ → ℕ × C
      rec' n = iter (zero , c₀) cₛ' n

      rec'-id : (n : ℕ) → pr₁ (rec' n) ≡ n
      rec'-id zero = refl
      rec'-id (succ n) = cong succ (rec'-id n)

      rec-iter : ℕ → C
      rec-iter n = pr₂ (rec' n)

      rec-zero : rec-iter zero ≡ c₀
      rec-zero = refl

      rec-succ : (n : ℕ) → rec-iter (succ n) ≡ cₛ n (rec-iter n)
      rec-succ n = cong (λ x → cₛ x (rec-iter n)) (rec'-id n)
