{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor
open import Monoidal
open import Product
open import Shapes

module Closed
  {o m}
  {cat : Cat o m}
  (mc : Monoidal cat) where


open Cat cat hiding (_[_,_];_ᵒᵖ)
open Cat using (_[_,_];_ᵒᵖ)
open _Functor_


record ClosedMonoidal : Set (o ⊔ m) where
  constructor MkClosed
  field
    comp : ((cat ᵒᵖ) X cat) Functor cat

  infixl 10 [_,_]ₒ, [_,_]ₘ
  [_,_]ₒ : obj → obj → obj
  [_,_]ₒ = curry (mapObj comp)

  [_,_]ₘ : {a b c d : obj}
    → b hom a -- this is from cat 
    → c hom d
    → [ b , c ]ₒ hom [ a , d ]ₒ
  [ f , g ]ₘ = let t = mapMor comp (( f ᵒᵖ , g )) in {!!}

  field
    conditionAdj : {!!} -- for every object there's an adjunction
    conditionNatTransf : {!!} -- for every a, b, c there's an isomorphism of homs

