{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Data.Product
open import Function renaming (id to id')
open import Cubical.Core.Everything hiding (comp)
open import Cubical.Foundations.Prelude hiding (comp)

open import Category
open import CategoryOfSets

module DependentOptics.DepLens
  {o m : Level} where

record Cont : Set (suc (o ⊔ m)) where
  constructor MkCont
  field
    pos : Set o
    dir : pos → Set m

record Cont0 : Set (suc (o ⊔ m)) where
  constructor MkCont0
  field
    pos0 : Set o
    dir0 : (@0 _ : pos0) → Set m

open Cont

record DepLens (A B : Cont) : Set (o ⊔ m) where
  constructor MkDepLens
  field
    f : pos A → pos B
    f# : {a : pos A} → dir B (f a) → dir A a

polyComp : {A B C : Cont} → (F : DepLens A B) → (G : DepLens B C) → DepLens A C
polyComp (MkDepLens f f#) (MkDepLens g g#) = MkDepLens (g ∘ f) (λ {a} → f# ∘ g# {f a}) -- λ {a} f# ∘ g# {f a}
                                                                                       --   there's going to be a point in history 'a'

poly : Cat (suc (o ⊔ m)) (o ⊔ m)
poly = MkCat
  Cont
  (λ A B → DepLens A B)
  (MkDepLens id' id')
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
