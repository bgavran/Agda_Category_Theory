open import Level
open import Function using (flip)
open import Data.Product
--open import IO
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import CategoryOfCategories

open Cat using (_[_,_])
-- open import NaturalTransformation
-- open import Monoidal
-- open import SymmetricMonoidal
-- open import CD-Category
-- open import CDAffine-Category
-- open import Cartesian

module Twisty {o m} (cat : Cat o m) where

  open Cat cat

  -- the category needs to be closed
  tw : (cat X (cat ᵒᵖᶜ)) Functor cat
  tw = MkFunctor
    (λ (x , x') → {!!})
    {!!}
    {!!}
    {!!}
