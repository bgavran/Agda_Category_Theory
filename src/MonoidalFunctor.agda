{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Monoidal

module MonoidalFunctor where

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open Isomorphism._≅_
open Cat using (_[_,_])
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_

-- lax
record _MonoidalFunctor_
  {n m n' m'}
  {cat1 : Cat n m}
  {cat2 : Cat n' m'}
  (mc1 : Monoidal cat1)
  (mc2 : Monoidal cat2)
  : Set (n ⊔ m ⊔ n' ⊔ m') where
  constructor MkMonoidalFunctor

  private
    module MC1 = Monoidal.Monoidal mc1
    module MC2 = Monoidal.Monoidal mc2

  open MC1 renaming (⊗ to ⊗₁;𝟙 to 𝟙₁)
  open MC2 renaming (⊗ to ⊗₂;𝟙 to 𝟙₂)

  field
    F : cat1 Functor cat2
    ϕ : ((F 𝕏 F) ●F ⊗₂) NatTrans (⊗₁ ●F F)
    ε : cat2 [ 𝟙₂ , mapObj F 𝟙₁ ]

  -- Add coherence conditions

private
  variable
    n m n' m' : Level
    cat : Cat n m
    mc : Monoidal cat

idFunctorMonoidal : mc MonoidalFunctor mc
idFunctorMonoidal = MkMonoidalFunctor idFunctor {!!} {!!}
