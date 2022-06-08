{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian

module Lens.D
  {n m n' m'}
  {cat1 : Cat n m}
  {cat2 : Cat n' m'}
  where

import Lens.Lens as L
import Lens.LensCategory as LC
import Lens.LensAssociativity
--private
--  module c1 = Cat cat1
--  module c2 = Cat cat2

open Cat
open _Functor_
open Cat.CommutativeSquare
open import Isomorphism

record _dHom_ (a b : obj cat1) : Set {!!} where
  field
    ff : cat1 [ a , b ]

d : Cat {!!} {!!}
d = MkCat
  (obj cat1)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
