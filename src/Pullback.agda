open import Level
open import Function using (flip)
open import Data.Product
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import Shapes

-- this should be an instance of a terminal cone?
module Pullback {o m} {cat : Cat o m} where
  open Cat cat
  open Shapes cat

  record Pullback {a b e : obj} (f : a hom b) (g : b hom e) : Set {!!} where
    constructor MkPullback
    field
      p : obj
      π₁ : p hom a
      π₂ : p hom b
      -- comm : CommutativeSquare π₁ f π₂ g
