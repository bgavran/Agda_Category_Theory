{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor
open import Monoidal
open import Product
open import Shapes

open Cat

module Closed
  {o m}
  {cat : Cat o m}
  (mc : Monoidal cat) where

record ClosedMonoidal : Set (o ⊔ m) where
  constructor MkClosed
  field
    comp : ((cat ᵒᵖ) X cat) Functor cat
    condition : {!!} -- for every object there's an adjunction
