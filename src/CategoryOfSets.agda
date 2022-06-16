{-# OPTIONS --allow-unsolved-metas #-}
module CategoryOfSets where

open import Data.Product
open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category

𝕊𝕖𝕥 : {o : Level} → Cat (suc o) o
𝕊𝕖𝕥 {o = o} = MkCat
  (Set o)
  (λ a b → a → b)
  id'
  (flip _∘′_)
  refl
  refl
  refl
  λ f≡g h≡i → {!!}


oo : {o m : Level} → Cat o o → Cat o m
oo cat = {!cat!}
