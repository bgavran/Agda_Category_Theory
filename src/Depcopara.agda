open import Category
open import Monoidal
module Depcopara {n m} {cat : Cat n m} {mc : Monoidal cat} where

open import Level
open import Function using (flip)
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Functor
open import Product
open import NaturalTransformation
open import SymmetricMonoidal
