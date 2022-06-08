
{-# OPTIONS --allow-unsolved-metas #-}
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
open import Cartesian
open Cat using (_ᵒᵖ)

module Bicartesian
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda)
  {mcop : Monoidal (cat ᵒᵖ)}
  {smcop : SymmetricMonoidal mcop}
  {cdop : CD-Category smcop}
  {cdaop : CDAffine-Category cdop}
  (cartop : Cartesian cdaop) where

private
  variable
    n' m' n'' m'' : Level
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module mcop = Monoidal.Monoidal mcop
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cdop = CD-Category.CD-Category cdop
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart

open _Functor_
open Cat.CommutativeSquare
open import Isomorphism
open Cat using (_[_●_])
open cct hiding (_[_●_]; _ᵒᵖ)
open mc
open mcop renaming (_⊗ₘ_ to _⊗ₘ'_)
open smc
open cd
open cdop renaming (εₘ to ηₘ; δₘ to +ₘ)
open cda
open cart

record Bicartesian : (Set (n ⊔ m)) where
  constructor MkBicartesian
  field
    compatibility : {a : obj} → +ₘ {c = a} ● δₘ
                                ≡ let t = +ₘ
                                      t' = δₘ
                                   in {!!}   -- (δₘ ⊗ₘ'  δₘ) ● {!!} ● (+ₘ ⊗ₘ +ₘ)  -- (δₘ ⊗ₘ δₘ) ● ? -- αₘ' ● (αₘ ⊗ₘ id) ● (αₘ' ⊗ₘ id) ● αₘ ● (+ₘ ⊗ₘ +ₘ)
