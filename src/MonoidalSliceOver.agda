{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Product

open import Category
open import Functor
open import CategoryOfCategories
open import SetInstance
open import Monoidal
open import Product
open import SliceOver
import Shapes

module MonoidalSliceOver
  {o m}
  (cat : Cat o m)
  (mc : Monoidal cat)
  (x : Cat.obj cat) where

open Cat cat
open Monoidal.Monoidal mc

-- need monoids to define this?

sliceMonFunctor : ((cat / x) X (cat / x)) Functor (cat / x)
sliceMonFunctor = MkFunctor
  (λ ((MkSliceObj a p) , (MkSliceObj b q)) → MkSliceObj (a ⊗ₒ b) (p ⊗ₘ q ● {!!}))
  {!!}
  {!!}
  {!!}

mm : Monoidal (cat / x)
mm = MkMonoidal
  sliceMonFunctor
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
