open import Level
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor
open import Monoidal

module Lens.Optic
  {o m' : Level} -- renamed to m' because residual is called m
  {cat : Cat o m'}
  {mc : Monoidal cat} where

open Cat cat
open Monoidal.Monoidal mc


record OpticHom (a a' b b' : obj) : Set (o ⊔ m') where
  constructor MkOpticHom
  field
    m : obj
    f : a hom (m ⊗ₒ b)
    f# : (m ⊗ₒ b') hom a'

opticComp : {(a , a') (b , b') (c , c') : Cat.obj cat × Cat.obj cat} → OpticHom a a' b b' → OpticHom b b' c c' → OpticHom a a' c c'
opticComp (MkOpticHom m f f#) (MkOpticHom n g g#) = MkOpticHom (m ⊗ₒ n) {!!} {!!}

-- make this into a bicat?
opticCat : Cat o (o ⊔ m')
opticCat = MkCat
  (obj × obj)
  (λ (a , a') (b , b') → OpticHom a a' b b')
  (MkOpticHom 𝕀 λₘ' λₘ)
  opticComp
  {!!}
  {!!}
  {!!}
  {!!}
