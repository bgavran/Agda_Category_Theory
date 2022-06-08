{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal


module SymmetricMonoidalUtils
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  (smc : SymmetricMonoidal mc) where

private
  module scc = Cat cat
  module M = Monoidal.Monoidal mc
open scc hiding (_[_,_])
open Isomorphism._≅_
open Cat using (_[_,_])
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_
open M

-- it's easier to understand this natural transformation in terms of the morphism it associates to each object
|⇆|⊗ :
    ((swapFunctor ●F (⊗ 𝕏 idFunctor)) ●F ((productAssociatorᵣ ●F (⊗ 𝕏 idFunctor)) ●F ⊗))
  NatTrans
    ((swapFunctor ●F (⊗ 𝕏 idFunctor)) ●F ((idFunctor 𝕏 ⊗) ●F ⊗))
|⇆|⊗ = whiskerₗ (swapFunctor ●F (⊗ 𝕏 idFunctor)) (forward associator)


-- ff = {!!} ●F {!!}
-- |⇆|⊗ₘ : {a b c d : obj}
--   → (a ⊗ₒ b) ⊗ₒ (c ⊗ₒ d) hom
--     (a ⊗ₒ c) ⊗ₒ (b ⊗ₒ d)
-- |⇆|⊗ₘ {a = a} {b = b} {c = c} {d = d} = let t = η |⇆|⊗ {a = (a , b) , (c , d)} in {!!}

-- ((c ⊗ d) ⊗ a) ⊗ b) hom
-- (c ⊗ d) ⊗ (a ⊗ b)

-- |⇆|□ : {a b} {f : }
-- |⇆|□ = naturality |⇆|⊗
