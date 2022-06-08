{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning
open import Data.Product

open import Category
open import Functor
open import Shapes
open import NaturalTransformation
open import Comma

open Cat

-- category of cones is just the comma category!

module Cone {o m} {cat₁ cat₂ : Cat o m} (F : cat₁ Functor cat₂) where

  record Cone (x : obj cat₂) : Set (o ⊔ m) where
    constructor MkCone
    field
      coneNatTrans : (constFunctor x) NatTrans F


  -- record _coneHom_ {x y : obj cat₂ } (a : Cone x) (b : Cone y) : Set {!!} where
  --   constructor MkConeHom
  --   module c1 = Cone a
  --   module c2 = Cone b
  --   open c1 renaming (coneNatTrans to coneNatTrans₁) 
  --   open c2 renaming (coneNatTrans to coneNatTrans₂) 
  --   field
  --     aa : constFunctor 


  categoryOfCones : Cat {!!} {!!}
  categoryOfCones = {!commaCat!}
