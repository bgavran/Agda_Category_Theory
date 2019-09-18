module Equality where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} {a b : A}
  → a ≡ b
  → (f : A → B)
    -----
  → f a ≡ f b
cong refl f = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    -----
  → {a : A} → f a ≡ g a
cong-app refl = refl

-- subst : ∀ {A : Set} {a b : A}
--   → a ≡ b
--   → (p : A → Set)

module ≡-Reasoning {A : Set} where

  infix 1 begin_
  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin refl = refl


  infixr 2 _≡<_>_ _≡<>_

  -- this is just infix trans?
  _≡<_>_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
     -----
    → x ≡ z
  x ≡< x≡y > y≡z = trans x≡y y≡z

  -- _≡<>_ is equal to _≡< refl >_
  _≡<>_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡<> x≡y = x≡y

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning


trans' : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans' {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡< x≡y >
    y
  ≡< y≡z >
    z
  ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = {!!}
--  begin
--    {!!}
--  ≡< {!!} >
--     {!!}
--  ∎
+-comm m (suc n) =
  begin
     m + suc n
  ≡< {!!} >
     suc (n + m)
  ∎
