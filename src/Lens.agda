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

module Lens
  {n m }
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  (cart : Cartesian smc) where

open _Functor_
open _NatTrans_
open Cat.CommutativeSquare
open import Isomorphism
module cct = Cat cat
open cct
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
    get :    s      hom a
    put : (s ⊗ₒ b) hom t

_lensHom_ : (obj × obj) → (obj × obj) → Set m
_lensHom_ (s , t) (a , b) = Lens s t a b

lensId : {a : obj × obj} → a lensHom a
lensId = MkLens id π₂

_●ₗ_ : {a b c : obj × obj}
  → a lensHom b
  →           b lensHom c
  → a      lensHom      c
_●ₗ_ {a = (a , a')} {b = (b , b')} {c = (c , c')}
  (MkLens get₁ put₁) (MkLens get₂ put₂)
  = MkLens
    (get₁ ● get₂)
    (                  begin→⟨     a      ⊗ₒ c'    ⟩
        δ ⊗ₘ id            →⟨ (a ⊗ₒ a) ⊗ₒ c'    ⟩
      (id ⊗ₘ get₁) ⊗ₘ id  →⟨ (a ⊗ₒ b) ⊗ₒ c'    ⟩
         αₘ                 →⟨  a ⊗ₒ (b ⊗ₒ c')   ⟩
       id ⊗ₘ put₂          →⟨  a ⊗ₒ     b'       ⟩
       put₁                 →⟨  a'                 ⟩end )

lensLeftIdHelper : {a b x : obj} {f : a hom x}
  → (δ ⊗ₘ id {a = b}) ● ((id ⊗ₘ f) ⊗ₘ id) ●  αₘ ● (id ⊗ₘ π₂) ≡ id
lensLeftIdHelper {f = f} =
    (begin
        (δ ⊗ₘ id) ● ((id ⊗ₘ f) ⊗ₘ id) ●  αₘ ● (id ⊗ₘ π₂)
    ≡⟨   (assocApply α□) ⟨●⟩refl ⟩
        ((δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (f ⊗ₘ id))) ● (id ⊗ₘ π₂)
    ≡⟨   assoc  ⟩
        (δ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (f ⊗ₘ id)) ● (id ⊗ₘ π₂))
    ≡⟨   (refl⟨●⟩ sym distribute⊗) ⟩
        (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ( (f ⊗ₘ id) ● π₂))
    ≡⟨⟩
        (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ( (f ⊗ₘ id) ● ((ε ⊗ₘ id) ● λₘ)))
    ≡⟨   (refl⟨●⟩ ⊗-resp-≡ᵣ (sym assoc) ) ⟩
        (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ( (f ⊗ₘ id) ● (ε ⊗ₘ id) ● λₘ))
    ≡⟨   (refl⟨●⟩ ⊗-resp-≡ᵣ (sym distribute⊗ ⟨●⟩refl) ) ⟩
        (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ( (f ● ε) ⊗ₘ (id ● id) ● λₘ ))
    ≡⟨  refl⟨●⟩ ⊗-resp-≡ᵣ ( ⊗-resp-≡ (sym deleteApply) (left-id) ⟨●⟩refl) ⟩
        (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ( (ε ⊗ₘ id) ● λₘ ))
    ≡⟨    (refl⟨●⟩ distribute⊗)   ⟩
        (δ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (ε ⊗ₘ id)) ● ( id ⊗ₘ λₘ ))
    ≡⟨   sym assoc     ⟩
        (δ ⊗ₘ id) ● αₘ ●  (id ⊗ₘ (ε ⊗ₘ id)) ● (id ⊗ₘ λₘ)
    ≡⟨  strangeLaw  ⟩
        id
    ∎ )

lensLeftId : {a b : obj × obj} {f : a lensHom b}
  → f ●ₗ lensId ≡ f
lensLeftId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens left-id
   (begin
       (δ ⊗ₘ id) ● ((id ⊗ₘ get) ⊗ₘ id) ●  αₘ ● (id ⊗ₘ π₂) ● put
   ≡⟨  lensLeftIdHelper ⟨●⟩refl   ⟩
       id ● put
   ≡⟨  right-id   ⟩
       put
   ∎)




lensCategory : Cat n m
lensCategory = MkCat
  (obj × obj)
  _lensHom_
  (MkLens id π₂)
  _●ₗ_
  lensLeftId
  {!!}
  {!!}
  {!!}
