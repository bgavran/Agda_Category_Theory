open import Level
open import Data.Product
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
    pos : Set o
    dir : pos → Set m

open PolyObj

record PolyHom (A B : PolyObj) : Set (o ⊔ m) where
  constructor MkPolyHom
  field
    f : pos A → pos B
    f# : {a : pos A} → dir B (f a) → dir A a

record NewPolyHom (A B : PolyObj) : Set (suc o ⊔ m) where
  constructor MkNewPolyHom
  field
    res : Set o
    f : pos A → res × pos B
    f# : {r : res} → {!!}
    -- f# : {a : pos A} → dir B (proj₂ (f a)) → dir A a -- can't use {a : A} in implementation?

polyComp : {A B C : PolyObj} → (F : PolyHom A B) → (G : PolyHom B C) → PolyHom A C
polyComp (MkPolyHom f f#) (MkPolyHom g g#) = MkPolyHom (g ∘ f) {!!} -- λ {a} → f# ∘ g# {f a}

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
    dir : obj → Set m
    tgt : {a : obj} → dir a → obj
    id : (a : obj) → dir a
    comp : {a : obj} → (f : dir a) → (g : dir (tgt f)) → dir a

    idLaw : {a : obj} → tgt (id a) ≡ a
    -- compLaw : {a : obj} {f : dir a} → comp (id a) f ≡ f
