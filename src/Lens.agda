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

_lensHom_ : (obj × obj) → (obj × obj) → Set m
_lensHom_ (s , t) (a , b) = Lens s t a b

--lensId : {a : obj × obj} → lensHom a a
--lensId = MkLens id π₂


_∘ₗ_ : {a b c : obj × obj}
  → b lensHom c → a lensHom b → a lensHom c
_∘ₗ_ {a = (a , a')} {b = (b , b')} {c = (c , c')}
  (MkLens get₂ put₂) (MkLens get₁ put₁)
  = MkLens
    (get₂ ∘ get₁)
    (                  begin→⟨     a      ⊗ₒ c'    ⟩
        δ ⊗ₘ id            →⟨ (a ⊗ₒ a) ⊗ₒ c'    ⟩
      (id ⊗ₘ get₁) ⊗ₘ id  →⟨ (a ⊗ₒ b) ⊗ₒ c'    ⟩
         αₒ                 →⟨  a ⊗ₒ (b ⊗ₒ c')   ⟩
       id ⊗ₘ put₂          →⟨  a ⊗ₒ     b'       ⟩
       put₁                 →⟨  a'                 ⟩end )

lensLeftId : {a b : obj × obj} {f : a lensHom b}
  → (MkLens id π₂) ∘ₗ f ≡ f
lensLeftId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens left-id
   (begin
       put ∘ (id ⊗ₘ π₂) ∘ αₒ ∘ ((id ⊗ₘ get) ⊗ₘ id) ∘ (δ ⊗ₘ id)
   ≡⟨  refl ⟩
       put ∘ (id ⊗ₘ ( λₒ ∘ (ε ⊗ₘ id) )  ) ∘ αₒ ∘ ((id ⊗ₘ get) ⊗ₘ id) ∘ (δ ⊗ₘ id)
   ≡⟨ {!!} ⟩
       put ∘ (id ⊗ₘ λₒ) ∘ (id ⊗ₘ ( ε ⊗ₘ id )  ) ∘ αₒ ∘ ((id ⊗ₘ get) ⊗ₘ id) ∘ (δ ⊗ₘ id)
   ≡⟨ {!!} ⟩
      put ∘ (id ⊗ₘ λₒ) ∘ αₒ ∘ ( (id ⊗ₘ ε ) ⊗ₘ id ) ∘ ((id ⊗ₘ get) ⊗ₘ id) ∘ (δ ⊗ₘ id)
   ≡⟨ {!!} ⟩
      put ∘ (id ⊗ₘ λₒ) ∘ αₒ ∘ (((id ⊗ₘ ε) ∘ (id ⊗ₘ get)) ⊗ₘ (id ∘ id)) ∘ (δ ⊗ₘ id)
   ≡⟨ {!!} ⟩
      put
   ∎ )

-- TODO replace a function with its definitioN?
-- TODO cong?
-- TODO fall back on definition of π₂ and prove using ε and λₒ?
-- TODO create new combinators for π₂ ?

lensCategory : Cat n m
lensCategory = MkCat
  (obj × obj)
  _lensHom_
  (MkLens id π₂)
  _∘ₗ_
  lensLeftId
  {!!}
  {!!}
  {!!}
