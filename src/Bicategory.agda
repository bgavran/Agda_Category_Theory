open import Level
open import Function using (flip)
open import Data.Product
open import Data.Empty using (⊥) -- for the initial category

open import Category
open import Monoidal
open import Functor
open import SymmetricMonoidal
open import Enriched
open import CategoryOfCategories
open Cat
open Category


module Bicategory where

-- this is actually a 2-category?
Bicat : {o m m' : Level} → Set (suc o ⊔ suc m ⊔ suc m')
Bicat {o} {m} {m'} = EnrichedCat (catSymmetricMonoidal {m} {m'}) {o}

-- adds the trivial layer of 2-cells
catOfCatsBiCat : {o m : Level} → (cat : Cat o m) → Bicat {o} {m} {m}
catOfCatsBiCat {o} {m} cat = MkEnriched
  obj'
  (λ a b → disc (a hom' b))
  (λ {a} → MkFunctor (λ x → id' {a}) (λ x → {!!}) {!!} {!!})
  (λ a b c → MkFunctor (λ x → {!!}) {!!} {!!} {!!})
  {!!}
  {!!}
  {!!}
  where
  open Cat cat renaming (obj to obj'; _hom_ to _hom'_; id to id')
  open Monoidal.Monoidal (catOfCatsMonoidal {o} {m})

-- first need to write deloop at a lower level?
𝔹 : {o m m' : Level} {cat : Cat m m'} {mc : Monoidal cat}
  (smc : SymmetricMonoidal mc) → Bicat {o} {m} {m'}
𝔹 {o} {cat = cat} {mc = mc} smc = MkEnriched
  (Lift o ⊥)
  (λ x y → cat)
  (λ {x} → constFunctor (𝕀 mc))
  (λ a b c → ⊗ mc)
  (λ a b → {!leftUnitor mc!}) -- Goal is builtin equality, but I've got isomorphism?
  {!!}
  {!!}
  where
  open Monoidal.Monoidal

-- private
--   variable o o' m m' n n' : Level

2Functor : {o o' m m' : Level}
  → (bicat₁ : Bicat {o} {m} {m'}) → (bicat₂ : Bicat {o'} {m} {m'}) → Set (o ⊔ o' ⊔ m ⊔ m' )
2Functor {o = o} {o' = o'} {m = m} {m' = m'} bicat₁ bicat₂ = _EnrichedFunctor_ (catSymmetricMonoidal {m} {m'}) {o = o} {o' = o'} bicat₁ bicat₂

-- this should be just a Cat-enriched functor?
-- record _LaxFunctor_ (bicat₁ : Bicat o m m') (bicat₂ : Bicat o n n') : Set ? where
--   constructor MkLaxFunctor
--   field

