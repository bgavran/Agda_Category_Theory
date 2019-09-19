module Lens where


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
open import Comonoid

open Cat


private
  variable
    n m n' m' n'' m'' : Level
--     cat : Cat n m
--     mc : Monoidal cat
--     smc : SymmetricMonoidal mc


-- TODO just get's should be morphisms in cart,not puts also?
-- for this I need the notion of a subcategory

record Lens {cat : Cat n m}
            {mc : Monoidal cat}
            {smc : SymmetricMonoidal mc}
            (cart : Cartesian smc)
            (s t a b : obj cat)
            : (Set m) where
  constructor MkLens
  open _Functor_
  module M = Monoidal.Monoidal mc
  open M
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  open S

  field
    get : cat [ s , a ]
    put : cat [ s ⊗ₒ b , t ]

open Comonoid.Cartesian using (π₂)

lensHom : {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  → (cart : Cartesian smc) → (obj cat × obj cat) → (obj cat × obj cat) → Set m
lensHom cart (s , t) (a , b) = Lens cart s t a b

lensId : {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  → (cart : Cartesian smc) → {a : obj cat × obj cat} → lensHom cart a a
lensId {cat = cat} cart = MkLens (id cat) (π₂ cart)


lensCompose : {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc} {cart : Cartesian smc} {a b c : obj cat × obj cat}
  → lensHom cart b c → lensHom cart a b → lensHom cart a c
lensCompose {cat = cat} {mc = mc} {smc = smc} {cart = cart}
  (MkLens get₂ put₂) (MkLens get₁ put₁)
  = MkLens
    (get₂ ● get₁)
    (put₁ ● ((idd ⊗ₘ put₂) ● αₒ) ● (((idd ⊗ₘ get₁) ⊗ₘ idd)) ● (δ ⊗ₘ idd) )

  where
  module cat = Cat cat
  open cat renaming (id to idd; _∘_ to _●_)
  module M = Monoidal.Monoidal mc
  open M
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  open S
  module cart = Comonoid.Cartesian cart
  open cart

lensCategory : {cat : Cat n m} {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc} {cart : Cartesian smc}
  → Cat n m
lensCategory {cat = cat} {mc = mc} {smc = smc} {cart = cart} = MkCat
  (obj cat × obj cat)
  (lensHom cart)
  (lensId cart)
  lensCompose
  {!!}
  {!!}
  {!!}

  where
  module M = Monoidal.Monoidal mc
  open M
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  open S

