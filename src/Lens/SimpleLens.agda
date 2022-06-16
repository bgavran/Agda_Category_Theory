{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Isomorphism
open import Shapes
open import Functor
open import Product
open import Monoidal
open import SymmetricMonoidal
open import NaturalTransformation
open import MonoidalNaturalTransformation
open import CD-Category
open import CDAffine-Category
open import Cartesian
open import CategoryOfSets

module Lens.SimpleLens
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

import Lens.Lens as L
import Lens.LensCategory as LC
import Lens.LensAssociativity
import Lens.LensMonoidal

open _Functor_
open Shapes.CommutativeSquare
open Cat cat
open Monoidal.Monoidal mc
open SymmetricMonoidal.SymmetricMonoidal smc
open CD-Category.CD-Category cd
open CDAffine-Category.CDAffine-Category cda
open Cartesian.Cartesian cart
open L cart
open LC cart
open Lens.LensAssociativity cart using (lensAssoc)
open Lens.LensMonoidal cart

-- also called monomorphic lenses
record SimpleLens (a b : obj) : (Set m) where
  constructor MkSimpleLens
  field
    lens : Lens a a b b

MkSimpleLens' : {a b : obj} → a hom b → a ⊗ₒ b hom a → SimpleLens a b
MkSimpleLens' g p = MkSimpleLens (MkLens g p)

_●ₛₗ_ : {a b c : obj} →
  SimpleLens a b → SimpleLens b c → SimpleLens a c
_●ₛₗ_ (MkSimpleLens g) (MkSimpleLens f) = MkSimpleLens (g ●ₗ f)

simpleLensId : {a : obj} → SimpleLens a a
simpleLensId = MkSimpleLens lensId

simpleLensCategory : Cat n m
simpleLensCategory = MkCat
  obj
  SimpleLens
  simpleLensId
  _●ₛₗ_
  {!!} -- (cong MkSimpleLens lensLeftId)
  {!!} -- (cong MkSimpleLens lensRightId)
  {!!} -- (cong MkSimpleLens lensAssoc)
  λ f≡g h≡i → {!!} -- cong MkSimpleLens (●ₗ-resp-≡ (cong SimpleLens.lens f≡g) (cong SimpleLens.lens h≡i))

simpleLensMonoidal : Monoidal simpleLensCategory
simpleLensMonoidal = MkMonoidal
  (MkFunctor
    (mapObj ⊗)
    (λ (MkSimpleLens l , MkSimpleLens r) → MkSimpleLens (mapMor ⊗ₗ (l , r)))
    {!!} -- (cong MkSimpleLens (idLaw ⊗ₗ))
    (λ f g → {!!})) -- cong MkSimpleLens let t = compLaw ⊗ₗ in {!!}))
  𝕀
  {!!}
  (MkIso (MkNatTrans (MkSimpleLens (MkLens λₘ {!!})) {!!}) {!!} {!!} {!!})
  {!!}
  {!!}
  {!!}
  -- (cong MkSimpleLens (Monoidal.▵-identity lensMonoidal))
  -- (cong MkSimpleLens (Monoidal.⬠-identity lensMonoidal))

-- simpleLensSymmetricMonoidal : SymmetricMonoidal simpleLensMonoidal
-- simpleLensSymmetricMonoidal = MkSymmMonoidal (MkIso
--   (MkNatTrans (MkSimpleLens (◿ σₘ || σₘ ◺)) (Shapes.MkCommSq (cong MkSimpleLens {!!})))
--   (MkNatTrans (MkSimpleLens (◿ σₘ || σₘ ◺)) (Shapes.MkCommSq (cong MkSimpleLens {!!})))
--   {!!}
--   {!!})


-- simpleLensCDCategory : CD-Category simpleLensSymmetricMonoidal
-- simpleLensCDCategory = MkCD-Category
--   (MkMonoidalNatTrans (MkNatTrans (MkSimpleLens' δₘ (π₂ ●  π₁)) (Shapes.MkCommSq {!!})) {!!} {!!})
--   (MkMonoidalNatTrans (MkNatTrans (MkSimpleLens (CoPt id)) (Shapes.MkCommSq (cong MkSimpleLens {!!}))) {!!} {!!})
--   {!!}
--   {!!}
--   {!!}

