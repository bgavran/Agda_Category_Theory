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

  ---- map on morphisms
  --_⊗ₘ_ : obj (cat X cat) → obj cat
  --_⊗ₘ_ = mapMor _⊗_

  x⊗[y⊗z] : (cat X (cat X cat)) Functor cat
  x⊗[y⊗z] = functorComposition _⊗_ ((idFunctor) 𝕏 (_⊗_))

  multiplyTwiceAssociator : (cat X (cat X cat)) Functor cat
  multiplyTwiceAssociator = {!!}

  field
    associator : Isomorphism (functorCategory (cat X (cat X cat)) cat)
      x⊗[y⊗z] multiplyTwiceAssociator


ff : {a b : Set} → a × b → a × a
ff = λ x → {!!}
