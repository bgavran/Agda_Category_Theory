module Monoidal where

open import Level
open import Function using (flip)
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation

private
  variable n m n' m' n'' m'' : Level

record Monoidal (cat : Cat n m): (Set (n ⊔ m)) where
  constructor MkMonoidal
  open Cat
  field
    _⊗_ : (cat X cat) Functor cat
    𝟙 : obj cat
    associator : Isomorphism (functorCategory (cat X (cat X cat)) cat) ? ?
