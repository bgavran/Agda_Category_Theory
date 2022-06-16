open import Level
open import Function renaming (id to id')
open import Cubical.Core.Everything hiding (comp)
open import Cubical.Foundations.Prelude hiding (comp)

open import Category
open import CategoryOfSets

module Poly.Test
  {o m : Level} where

record PolyObj : Set (suc (o ⊔ m)) where
  constructor MkPolyObj
  field
    base : Set o
    arr : base → Set m

open PolyObj

record PolyHom (A B : PolyObj) : Set (o ⊔ m) where
  constructor MkPolyHom
  field
    f : base A → base B
    f# : {a : base A} → arr B (f a) → arr A a

polyComp : {A B C : PolyObj} → (F : PolyHom A B) → (G : PolyHom B C) → PolyHom A C
polyComp (MkPolyHom f f#) (MkPolyHom g g#) = MkPolyHom (g ∘ f) λ {a} → f# ∘ g# {f a}

poly : Cat (suc (o ⊔ m)) (o ⊔ m)
poly = MkCat
  PolyObj
  (λ A B → PolyHom A B)
  (MkPolyHom id' id')
  polyComp
  {!!}
  {!!}
  {!!}
  {!!}


-- Comonoids in Poly perspective. For each object there's a set of directions where we can go...
record PolyCat (o m : Level) : Set (suc (o ⊔ m)) where
  constructor MkPolyCat
  field
    obj : Set o
    arr : obj → Set m
    tgt : {a : obj} → arr a → obj
    id : (a : obj) → arr a
    comp : {a : obj} → (f : arr a) → (g : arr (tgt f)) → arr a

    idLaw : {a : obj} → tgt (id a) ≡ a
    -- compLaw : {a : obj} {f : arr a} → comp (id a) f ≡ f

-- l0 : {o : Level} → Set o
-- l0 = {!!}
-- 
-- l1 : {o m : Level} → (A : l0 {o}) → Set m
-- l1 = {!!}
-- 
-- l2 : {o m m' : Level} → (A : l0 {o}) → (A' : l1 {m = m} A) → Set m'
-- l2 = {!!}
