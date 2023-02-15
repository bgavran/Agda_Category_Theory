{-# OPTIONS --allow-unsolved-metas #-}
module DepAct where

open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import CategoryOfCategories
open import Slice


variable
  o m : Level

record DepAct
  (c : Cat o m)
  (d : c Functor (ℂ𝕒𝕥 o m)) : Type ((suc o) ⊔ m)  where
  constructor MkDepAct
  field
    act : (groth d) Functor c


NonDepAct : (c, d : Cat o m) → Type (suc o ⊔ m)
NonDepAct c d = DepAct c (constFunctor d) 
