open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category

module Cartesian
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  (cda : CDAffine-Category cd) where

private
  variable
    n' m' n'' m'' : Level
  module C = Cat cat
  module M = Monoidal.Monoidal mc
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  module CD = CD-Category.CD-Category cd

open _Functor_
open C
open M
open S
open CD

record Cartesian : (Set (n ⊔ m)) where
  constructor MkCartesian

  field
    copyApply   : {a b : obj} {f : a hom b} → f ● δ ≡ δ ● (f ⊗ₘ f)
