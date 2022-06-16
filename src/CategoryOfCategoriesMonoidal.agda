{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (Lift)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function hiding (flip)
open import Data.Unit using (⊤; tt) -- for the terminal category
open import Data.Empty using (⊥) -- for the initial category
open import Data.Product
open import Agda.Builtin.Bool
open import Function renaming (id to idff)
open import Data.Empty

open import Utils
open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import MonoidalNaturalTransformation
open import Shapes
open import Isomorphism

open import CategoryOfSets
open import CategoryOfCategories

module CategoryOfCategoriesMonoidal where

catOfCatsMonoidal : {o m : Level} → Monoidal (catOfCats {o} {m})
catOfCatsMonoidal = MkMonoidal
  (MkFunctor (λ (c , d) → c X d) {!!} {!!} {!!})
  oneObjectCat
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

catSymmetricMonoidal : {o m : Level} → SymmetricMonoidal (catOfCatsMonoidal {o} {m})
catSymmetricMonoidal = MkSymmMonoidal (MkIso {!!} {!!} {!!} {!!}) {!!}

-- CatCDCategory : CD-Category CatSymmetricMonoidal
-- CatCDCategory = MkCD-Category
--   --                                               should × go there?
--   (MkMonoidalNatTrans (MkNatTrans (MkFunctor (λ x → {!!} × {!!}) {!!} {!!} {!!}) {!!}) {!!} {!!})
--   (MkMonoidalNatTrans (MkNatTrans (MkFunctor (λ _ → lift tt) {!!} {!!} {!!}) {!!}) {!!} {!!})
--   {!!}
--   {!!}
--   {!!}


cc : {n m : Level} → {cat : Cat n m} → {mc : Monoidal cat} → Set (n ⊔ m)
cc {cat = cat} {mc = mc} = SymmetricMonoidal mc

-- category of cd-affine categories?
-- category of monoidal categories
catOfSMC : {n m : Level} → Cat {!!} {!!}
catOfSMC {n = n} {m = m} = MkCat
  cc
  {!!} -- monoidal functor
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
