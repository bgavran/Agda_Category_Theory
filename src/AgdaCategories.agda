{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --with-K #-}
module AgdaCategories where

open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open Cat


-- should I call things Set or Type? Agda seems to call them Type
𝕋𝕪𝕡𝕖 : (o : Level) → Cat (suc o) o
𝕋𝕪𝕡𝕖 o = MkCat
  (Type o)
  (λ a b → a → b)
  Function.id
  (λ f g → λ a → g (f a))
  refl
  refl
  refl
  {!!}

Fam : {n o m : Level} → Cat o m → Type n → Cat (o ⊔ n) (n ⊔ m)
Fam c a = MkCat
  (a → obj c)
  (λ a' b' → (x : a) → c [ a' x , b' x ]) --c [ a' x , b' x ] )
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

Fam0 : {n o m : Level} → Cat o m → Type n → Cat (o ⊔ n) (n ⊔ m)
Fam0 c a = MkCat
  ((@0 _ : a) → obj c)
  (λ a' b' → (@0 x : a) → c [ a' x , b' x ])
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}



Fam0Test : {n : Level} → Type n → Cat (suc n) n
Fam0Test {n} a = MkCat
  ((_ : a) -> Type n)
  (λ a' b' → (@0 x : a) → a' x)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
