open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category

module MonoidalFunctor {n m n' m'} (cat1 : Cat n m) (cat2 : Cat n' m') where

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open Isomorphism._≅_
open Cat using (_[_,_])
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_
