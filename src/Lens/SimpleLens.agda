open import Level
open import Function using (flip)
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

module Lens.SimpleLens
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

import Lens.Lens as L
private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart
  module lenss = L cart

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


record SimpleLens (a b : obj) : (Set m) where
  constructor MkSimpleLens
  field
    lens : Lens a a b b

record LawfulSimpleLens (a b : obj) : (Set m) where
  constructor MkLawfulSimpleLens
  field
    simpleLens : SimpleLens a b
  module simpleLens = SimpleLens simpleLens
  open simpleLens
  module lls = Lens lens
  open lls

  field
    putGetLaw : put ● get ≡ π₂
    putPutLaw : (put ⊗ₘ id ) ● put ≡ (π₁ ⊗ₘ id ) ● put
    getPutLaw : δ ● (id ⊗ₘ get) ● put ≡ id
