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
open import Comonoid
open import Lens.Lens using (Lens)
import Lens.LensAssociativity

module Lens.LensCategory
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  (cart : Cartesian smc) where

private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cart = Comonoid.Cartesian cart
  module lens = Lens.Lens cart
  module lensassoc = Lens.LensAssociativity cart

open cct
open mc
open smc
open cart
open lens
open lensassoc using (lensAssoc)

lensId : {a : obj × obj} → a lensHom a
lensId = MkLens id π₂

lensLeftId : {a b : obj × obj} {f : a lensHom b}
  → f ●ₗ lensId ≡ f
lensLeftId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens left-id
   (begin
       _ ● put
   ≡⟨
       (begin
          (δ ⊗ₘ id) ● ((id ⊗ₘ get) ⊗ₘ id) ●  αₘ ● _
       ≡⟨   (assocApply α□) ⟨●⟩refl ⟩
          ((δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (get ⊗ₘ id))) ● _
       ≡⟨   assoc  ⟩
          (δ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (get ⊗ₘ id)) ● (id ⊗ₘ π₂))
       ≡⟨   (refl⟨●⟩ sym distribute⊗) ⟩
          (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ( (get ⊗ₘ id) ● π₂))
       ≡⟨  refl⟨●⟩ ( ⊗-resp-≡ left-id π₂law ) ⟩
          (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ π₂)
       ≡⟨   copyαπ₂≡id   ⟩
          id
       ∎ )

        ⟨●⟩refl   ⟩
       id ● put
   ≡⟨  right-id   ⟩
       put
   ∎)





lensCategory : Cat n m
lensCategory = MkCat
  (obj × obj)
  _lensHom_
  lensId
  _●ₗ_
  lensLeftId
  {!!}
  lensAssoc
  {!!}
