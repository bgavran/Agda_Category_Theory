open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import Comonoid

module Lens
  {n m }
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  (cart : Cartesian smc) where

open _Functor_
module cat = Cat cat
open cat
module mc = Monoidal.Monoidal mc
open mc
module smc = SymmetricMonoidal.SymmetricMonoidal smc
open smc
module cart = Comonoid.Cartesian cart
open cart

private
  variable
    n' m' n'' m'' : Level


-- TODO just get's should be morphisms in cart,not puts also?
-- for this I need the notion of a subcategory
record Lens (s t a b : obj) : (Set m) where
  constructor MkLens

  field
    get : cat [ s , a ]
    put : cat [ s ⊗ₒ b , t ]

lensHom : (cart : Cartesian smc) → (obj × obj) → (obj × obj) → Set m
lensHom cart (s , t) (a , b) = Lens s t a b

lensId : (cart : Cartesian smc) → {a : obj × obj} → lensHom cart a a
lensId cart = MkLens id π₂


lensCompose : {a b c : obj × obj}
  → lensHom cart b c → lensHom cart a b → lensHom cart a c
lensCompose {a = (a , a')} {b = (b , b')} {c = (c , c')}
  (MkLens get₂ put₂) (MkLens get₁ put₁)
  = MkLens
    (get₂ ∘ get₁)
    (                  begin→⟨     a      ⊗ₒ c'    ⟩
        δ ⊗ₘ id            →⟨ (a ⊗ₒ a) ⊗ₒ c'    ⟩
      (id ⊗ₘ get₁) ⊗ₘ id  →⟨ (a ⊗ₒ b) ⊗ₒ c'    ⟩
         αₒ                 →⟨  a ⊗ₒ (b ⊗ₒ c')   ⟩
       id ⊗ₘ put₂          →⟨  a ⊗ₒ     b'       ⟩
       put₁                 →⟨  a'                 ⟩end )

lensLeftId : (cart : Cartesian smc) {a b : obj × obj} {f : lensHom cart a b} → lensCompose (lensId cart) f ≡ f
lensLeftId cart {f} = cong₂ MkLens left-id {!!}

lensCategory : {cart : Cartesian smc} → Cat n m
lensCategory {cart = cart} = MkCat
  (obj × obj)
  (lensHom cart)
  (lensId cart)
  lensCompose
  (lensLeftId cart)
  {!!}
  {!!}
