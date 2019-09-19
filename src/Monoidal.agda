module Monoidal where

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation

private
  variable n m n' m' n'' m'' : Level



record Monoidal (cat : Cat n m) : (Set (n ⊔ m)) where
  constructor MkMonoidal
  open Cat
  open _Functor_

  field
    _⊗_ : (cat X cat) Functor cat
    𝟙 : obj cat

  -- map on objects
  _⊗ₒ_ : obj (cat X cat) → obj cat
  _⊗ₒ_ = mapObj _⊗_


  x⊗[y⊗z] : (cat X (cat X cat)) Functor cat
  x⊗[y⊗z] = _⊗_ functorComp (idFunctor 𝕏 _⊗_)

  [x⊗y]⊗z : (cat X (cat X cat)) Functor cat
  [x⊗y]⊗z = _⊗_ functorComp ((_⊗_ 𝕏 idFunctor) functorComp productAssociatorᵣ)

  field
    associator  : Isomorphism (functorCategory (cat X (cat X cat)) cat)
      x⊗[y⊗z] [x⊗y]⊗z
    leftUnitor  : Isomorphism (functorCategory cat cat)
      {!!} idFunctor
    rightUnitor : Isomorphism (functorCategory cat cat)
      {!!} idFunctor
