{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
import Monoidal
import MonoidalFunctor

module MonoidalNaturalTransformation {n m n' m'}
  {cat1 : Cat n m}
  {cat2 : Cat n' m'}
  {mc1 : Monoidal.Monoidal cat1}
  {mc2 : Monoidal.Monoidal cat2}
  (mf1 : mc1 MonoidalFunctor.MonoidalFunctor mc2)
  (mf2 : mc1 MonoidalFunctor.MonoidalFunctor mc2)
  where

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open Isomorphism._≅_
open Cat
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_
private
  --module MC1 = Monoidal.Monoidal mc1
  --module MC2 = Monoidal.Monoidal mc2
  module MF1 = MonoidalFunctor._MonoidalFunctor_ mf1
  module MF2 = MonoidalFunctor._MonoidalFunctor_ mf2


open MF1 renaming (F to F₁; ϕ to ϕ₁; ψ to ψ₁)
open MF2 renaming (F to F₂; ϕ to ϕ₂; ψ to ψ₂)
-- open MC1 renaming (⊗ to ⊗₁;𝟙 to 𝟙₁)
-- open MC2 renaming (⊗ to ⊗₂;𝟙 to 𝟙₂)

record _MonoidalNatTrans_ : Set (n ⊔ m ⊔ n' ⊔ m') where
  constructor MkMonoidalNatTrans
  field
    θ : F₁ NatTrans F₂
    identityTriangle : cat2 [ ψ₁ ● η θ ] ≡ ψ₂
    squareMonoidalTrans : {!!} [ ϕ₁ ● θ ] ≡ {!!} [ {!!} , ϕ₂ ]
