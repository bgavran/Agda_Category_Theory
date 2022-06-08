open import Level
open import Function renaming (id to id→; _∘_ to _∘ᶠ_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor
open import Product
import Enriched
open import Monoidal
open import SymmetricMonoidal
open Cat

open Enriched using (_ᵒᵖ)

module Profunctor
  {n m}
  {v : Cat n m}
  {mc : Monoidal v}
  {smc : SymmetricMonoidal mc}where

private
  variable
    n' n'' m' m'' o o' : Level
  module e = Enriched smc
  open e hiding (_ᵒᵖ;obj)

open EnrichedCat

record EFunctor (c : EnrichedCat o) (d : EnrichedCat o) : {!!} where
  constructor MkEFunctor
  field
    mapObjE : obj c → obj d
    mapMorE : {a b : }

-- Profunctor : (c : EnrichedCat o) (d : EnrichedCat o) → Set {!!} -- (n ⊔ m ⊔ n' ⊔ m' ⊔ n'' ⊔ m'')
-- Profunctor c d = ((d ᵒᵖ) X c) Functor v
-- 
-- syntax Profunctor cat1 cat2 = cat1 ↠ cat2

--idProfunctor : {v : Cat n' m'} {cat : Cat n m} → Profunctor {v = v} cat cat
--idProfunctor = MkFunctor (λ x → {!!}) {!!} {!!} {!!}
--
--profunctorCategory : {o p : Level} {v : Cat n m} → Cat {!!} {!!}
--profunctorCategory {o = o} {p = p} {v = v} = MkCat
--  (Cat o p)
--  (Profunctor {v = v})
--  {!!}
--  {!!}
--  {!!}
--  {!!}
--  {!!}
--  {!!}
