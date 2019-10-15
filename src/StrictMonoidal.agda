{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Monoidal

module StrictMonoidal {n m} (cat : Cat n m) where

private
  module cc = Cat cat
  variable n' m' n'' m'' : Level

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open cc hiding (_[_,_])
open Isomorphism._≅_
open Cat using (_[_,_])
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_



record StrictMonoidal : Set (n ⊔ m) where
  constructor MkStrictMonoidal

  field
    ⊗ : (cat X cat) Functor cat
    𝟙 : obj


  x⊗[y⊗z] : (cat X (cat X cat)) Functor cat
  x⊗[y⊗z] = (idFunctor 𝕏 ⊗) ●F ⊗

  [x⊗y]⊗z : (cat X (cat X cat)) Functor cat
  [x⊗y]⊗z = (productAssociatorᵣ ●F (⊗ 𝕏 idFunctor {cat = cat}))  ●F ⊗

  [𝟙⊗x] : cat Functor cat
  [𝟙⊗x] = (constFunctor 𝟙 \/ idFunctor {cat = cat}) ●F (⊗)

  [x⊗𝟙] : cat Functor cat
  [x⊗𝟙] = (idFunctor \/ constFunctor 𝟙) ●F ⊗

  field
    associator  : _≅_ {cat = functorCategory} [x⊗y]⊗z x⊗[y⊗z]
    leftUnitor  : _≅_ {cat = functorCategory} [𝟙⊗x] idFunctor
    rightUnitor : _≅_ {cat = functorCategory} [x⊗𝟙] idFunctor
    --▵-identity : associator ●≅ (? ⊗≅ ?)
