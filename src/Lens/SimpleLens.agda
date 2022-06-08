{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian
open import SetInstance

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
open import MonoidalNaturalTransformation
private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart
  module lenss = L cart
  module lc = LC cart
  module lensassoc = Lens.LensAssociativity cart
  module lensmon = Lens.LensMonoidal cart

open _Functor_
open Cat.CommutativeSquare
open import Isomorphism
open cct
open mc
open smc
open cd
open cda
open cart
open lenss
open lc
open lensassoc using (lensAssoc)
open lensmon

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
  (cong MkSimpleLens lensLeftId)
  (cong MkSimpleLens lensRightId)
  (cong MkSimpleLens lensAssoc)
  λ f≡g h≡i → cong MkSimpleLens (●ₗ-resp-≡ (cong SimpleLens.lens f≡g) (cong SimpleLens.lens h≡i))

simpleLensMonoidal : Monoidal simpleLensCategory
simpleLensMonoidal = MkMonoidal
  (MkFunctor
    (mapObj ⊗)
    (λ (MkSimpleLens l , MkSimpleLens r) → MkSimpleLens (mapMor ⊗ₗ (l , r)))
    (cong MkSimpleLens (idLaw ⊗ₗ))
    (λ f g → cong MkSimpleLens let t = compLaw ⊗ₗ in {!!}))
  𝟙
  {!!}
  (MkIso (MkNatTrans (MkSimpleLens (MkLens λₘ {!!})) {!!}) {!!} {!!} {!!})
  {!!}
  {!!}
  {!!}
  -- (cong MkSimpleLens (Monoidal.▵-identity lensMonoidal))
  -- (cong MkSimpleLens (Monoidal.⬠-identity lensMonoidal))

simpleLensSymmetricMonoidal : SymmetricMonoidal simpleLensMonoidal
simpleLensSymmetricMonoidal = MkSymmMonoidal (MkIso
  (MkNatTrans (MkSimpleLens (◿ σₘ || σₘ ◺)) (Cat.MkCommSq (cong MkSimpleLens {!!})))
  (MkNatTrans (MkSimpleLens (◿ σₘ || σₘ ◺)) (Cat.MkCommSq (cong MkSimpleLens {!!})))
  {!!}
  {!!})


simpleLensCDCategory : CD-Category simpleLensSymmetricMonoidal
simpleLensCDCategory = MkCD-Category
  (MkMonoidalNatTrans (MkNatTrans (MkSimpleLens' δₘ (π₂ ●  π₁)) (Cat.MkCommSq {!!})) {!!} {!!})
  (MkMonoidalNatTrans (MkNatTrans (MkSimpleLens (CoPt id)) (Cat.MkCommSq (cong MkSimpleLens {!!}))) {!!} {!!})
  {!!}
  {!!}
  {!!}

