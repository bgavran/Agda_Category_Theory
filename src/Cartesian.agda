open import Level
open import Function using (flip)
open import Data.Product
--open import IO
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
  module CDA = CDAffine-Category.CDAffine-Category cda

open _Functor_
open C
open M
open S
open CD
open CDA

-- record Cartesian' : {!!} where
--   constructor MkCartesian'
--   field
--     _x_ : obj → obj → obj
--     π₁' : {a b : obj} → a x b → a

record Cartesian : (Set (n ⊔ m)) where
  constructor MkCartesian

  field
    copyApply   : {a b : obj} {f : a hom b} → f ● δₘ ≡ δₘ ● (f ⊗ₘ f)
