{-# OPTIONS --allow-unsolved-metas #-}
module AgdaCategories where

open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category


-- should I call things Set or Type? Agda seems to call them Type
𝕋𝕪𝕡𝕖 : (o : Level) → Cat (suc o) o
𝕋𝕪𝕡𝕖 o = MkCat
  (Type o)
  (λ a b → a → b)
  (Function.id)
  (λ f g → λ a → g (f a))
  refl
  refl
  refl
  {!!}

FamCat : {n : Level} → Type n → Cat (suc n) n
FamCat {n} a = MkCat
  (a → Type n)
  (λ a' b' → (x : a) → a' x → b' x)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

Fam0Cat : {n : Level} → Type n → Cat (suc n) n
Fam0Cat {n} a = MkCat
  ((@0 x : a) → Type n)
  (λ a' b' → (@0 x : a) → a' x → b' x)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
