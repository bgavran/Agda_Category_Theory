{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning
open import Data.Product

open import Category
open import Functor
open import SetInstance
open import Comma
open import CategoryOfCategories

open Cat

module FreeCoproduct where

-- record freeCoproductObj : Set {!!} where
--   constructor MkFreeCoproductObj
--   field
--     i : obj 𝕊𝕖𝕥
    
freeCoproduct : {o m : Level} → (cat : Cat o m) → Cat {!!} {!!}
freeCoproduct {o = o} cat = _⇒_ {catE = catOfCats} (let x = disc' {o = o} in {!x!}) (name cat) 
--freeCoproduct {o = o} cat = _⇒_ {cat₁ = 𝕊𝕖𝕥} {cat₂ = oneObjectCat} {catE = catOfCats {o = o}} disc' let x = name cat in {!x!}
