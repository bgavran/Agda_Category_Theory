open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Monoidal
open import SymmetricMonoidal
open import Enriched
open import CategoryOfCategories


module Bicategory {n m} where

record 2-Category (o : Level) : Set {!!} where
  constructor MkBicat
  field
     ct : EnrichedCat {v = catOfCats {n = n} {m = m}} {mc = catOfCatsMonoidal} o
