{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Utils
open import Category
open import Functor
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal

open Cat

module CategoryOfCategories where

leftIdFunctor : {n m : Level} → {a b : Cat n m} {f : a Functor b} → (f ●F idFunctor) ≡ f
leftIdFunctor {f = f} = let t = cong₄ MkFunctor {!!} {!!} {!!} {!!} in {!t!}

catOfCats : {n m : Level} → Cat (suc n ⊔ suc m) (n ⊔ m)
catOfCats {n = n} {m = m} = MkCat
  (Cat n m)
  _Functor_
  idFunctor
  _●F_
  leftIdFunctor
  {!!}
  {!!}
  {!!}


cc : {n m : Level} → {cat : Cat n m} → {mc : Monoidal cat} → Set (n ⊔ m)
cc {cat = cat} {mc = mc} = SymmetricMonoidal mc

-- category of cd-affine categories?
-- category of monoidal categories
catOfSMC : {n m : Level} → Cat {!!} {!!}
catOfSMC {n = n} {m = m} = MkCat
  cc
  {!!} -- monoidal functor
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
