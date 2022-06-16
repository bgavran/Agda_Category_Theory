{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Monoidal
open import Shapes


module MonoidalFunctor where

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open Isomorphism._≅_
open Cat
open Shapes.CommutativeSquare
open _Functor_
open _NatTrans_

-- lax
record _MonoidalFunctor_
  {o₁ m₁ o₂ m₂}
  {cat1 : Cat o₁ m₁}
  {cat2 : Cat o₂ m₂}
  (mc1 : Monoidal cat1)
  (mc2 : Monoidal cat2)
  : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  constructor MkMonoidalFunctor

  private
    module MC1 = Monoidal.Monoidal mc1
    module MC2 = Monoidal.Monoidal mc2

  open MC1 renaming (⊗ to ⊗₁;𝕀 to 𝕀₁)
  open MC2 renaming (⊗ to ⊗₂;𝕀 to 𝕀₂)

  field
    F : cat1 Functor cat2
    ϕ : ((F 𝕏 F) ●F ⊗₂) NatTrans (⊗₁ ●F F) -- laxator
    ψ : cat2 [ 𝕀₂ , mapObj F 𝕀₁ ] -- unitor

  -- Add coherence conditions

private
  variable
    n m n' m' : Level

idFunctorMonoidal : {cat : Cat n m} {mc : Monoidal cat} → mc MonoidalFunctor mc
idFunctorMonoidal {cat = cat} = MkMonoidalFunctor
  idFunctor
  (MkNatTrans (id cat) (MkCommSq {!!}))
  (id cat)
