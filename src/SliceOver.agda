{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Product

open import Category
open import Functor
open import CategoryOfCategories
open import AgdaCategories
open import Monoidal
import Shapes

-- Covariant Slice
module SliceOver {o m} (cat : Cat o m) (x : Cat.obj cat) where
  open Cat cat
  open Shapes cat
  -- open Cat using (_[_,_])

  objLvl : Level
  objLvl = o ⊔ m

  mrphLvl : Level
  mrphLvl = suc objLvl

  record SliceObj : Set objLvl where
    constructor MkSliceObj
    field
      total : obj
      proj : total hom x

  open SliceObj


  record _sliceHom_ (f g : SliceObj) : Set mrphLvl where
    constructor MkSliceHom
    private
      module F = SliceObj f
      module G = SliceObj g
    field
      -- conn for connecting morphism, comm for commutative triangle
      conn : F.total hom G.total
      comm : CommutativeTriangle conn G.proj F.proj

  _sliceComp_ : {f' g' h' : SliceObj} → f' sliceHom g' → g' sliceHom h' → f' sliceHom h'
  _sliceComp_ (MkSliceHom conn₁ comm₁) (MkSliceHom conn₂ comm₂)= MkSliceHom (conn₁ ● conn₂) (glue▵→s comm₁ comm₂)

  idSlice : {f : SliceObj} → f sliceHom f
  idSlice = MkSliceHom id (MkCommTr right-id)

  -- is this that I can't define this because the 2nd argument is a commutative triangle, which itself has a ≡ operator in it?
  sliceLeftId : {f g : SliceObj} {r : f sliceHom g} → (r sliceComp idSlice) ≡ r
  sliceLeftId {f = f} {g = g} {MkSliceHom a (MkCommTr t)} = {!!}

  _/_ : Cat objLvl mrphLvl
  _/_ = MkCat
    SliceObj
    _sliceHom_
    idSlice
    _sliceComp_
    sliceLeftId
    {!!}
    {!!}
    {!!}
