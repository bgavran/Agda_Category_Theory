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


record Lens {cat : Cat n m}
            {mc : Monoidal cat}
            (smc : SymmetricMonoidal mc)
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

lensHom : {cat : Cat n m} {mc : Monoidal cat}
  → (smc : SymmetricMonoidal mc) → (obj cat × obj cat) → (obj cat × obj cat) → Set m
lensHom smc (s , t) (a , b) = Lens smc s t a b


lensId : {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  → (a : obj cat × obj cat) → lensHom smc a a
lensId {cat = cat} (a , a') = MkLens (id cat) {!!}

lensCategory : {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  → Cat n m
lensCategory {cat = cat} {mc = mc} {smc = smc} = MkCat
  (obj cat × obj cat)
  (lensHom smc)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  where
  module M = Monoidal.Monoidal mc
  open M
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  open S

