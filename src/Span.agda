{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian

module Span {o m} (cat : Cat o m) where

  open Cat cat

  record SpanMor (x y : obj) : Set (o ⊔ m) where
    constructor MkSpanMor
    field
      z : obj
      p : z hom x
      q : z hom y


  span : Cat o (o ⊔ m)
  span = MkCat
    obj
    SpanMor
    (λ {x} → MkSpanMor x id id)
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
