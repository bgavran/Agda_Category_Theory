open import Level
open import Function using (flip)
open import Data.Product
--open import IO
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor
open import Product

open Cat using (_[_,_];_ᵒᵖ)
-- open import NaturalTransformation
-- open import Monoidal
-- open import SymmetricMonoidal
-- open import CD-Category
-- open import CDAffine-Category
-- open import Cartesian

module Twisty {o m} (cat : Cat o m) where

  module cat = Cat cat
  open cat hiding (_ᵒᵖ)

  -- the category needs to be closed
  tw : (cat X (cat ᵒᵖ)) Functor cat
  tw = MkFunctor
    (λ (x , x') → {!!})
    {!!}
    {!!}
    {!!}
