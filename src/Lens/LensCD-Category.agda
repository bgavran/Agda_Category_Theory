{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip; _∘′_) renaming (id to id')
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
open import Lens.Lens using (Lens)
import Lens.LensAssociativity
import Lens.LensCategory
import Lens.LensMonoidal

module Lens.LensCD-Category
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart
  module lens = Lens.Lens cart
  module lensassoc = Lens.LensAssociativity cart
  module lenscart = Lens.LensCategory cart
  module lensmon = Lens.LensMonoidal cart

open Cat using (_[_,_];_ᵒᵖ)
open _Functor_
open _NatTrans_
open Cat.CommutativeSquare
open import Isomorphism
open import MonoidalNaturalTransformation
open cct hiding (_ᵒᵖ)
open mc
open smc
open cd
open cda
open cart
open lens
open lensassoc using (lensAssoc)
open lenscart
open lensmon


lensCD : CD-Category lensSymmetricMonoidal
lensCD = MkCD-Category
  {!!}
  (MkMonoidalNatTrans (MkNatTrans (λ {a} → {!!}) {!!}) {!!} {!!})
  {!!}
  {!!}
  {!!}
