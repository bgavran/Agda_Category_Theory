open import Level
open import Function using (flip)
open import Data.Bool
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian

module Lens.LinearLens
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

import Lens.Lens as L
import Lens.LensCategory as LC
import Lens.LensAssociativity
import Lens.SimpleLens

private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart
  module lenss = L cart
  module lc = LC cart
  module ls = Lens.SimpleLens cart
  module lensassoc = Lens.LensAssociativity cart

open _Functor_
open Cat.CommutativeSquare
open import Isomorphism
open cct
open mc
open smc
open cd
open cda
open cart
open lenss
open lc
open lensassoc using (lensAssoc)
open ls

record LinearLens (a b : obj) : (Set m) where
  constructor MkLinearLens
  field
    simpleLens : SimpleLens a b
    -- extraStructure, put is linear in the 2nd argument


  -- module simpleLens = SimpleLens simpleLens
  -- open simpleLens
  -- module lls = Lens lens
  -- open lls


linearLensCategory : Cat n m
linearLensCategory = MkCat
  (Cat.obj simpleLensCategory)
  LinearLens
  (MkLinearLens (Cat.id simpleLensCategory))
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

linearLensMonoidal : Monoidal linearLensCategory
linearLensMonoidal = {!!}

linearLensSymmetricMonoidal : SymmetricMonoidal linearLensMonoidal
linearLensSymmetricMonoidal = {!!}
