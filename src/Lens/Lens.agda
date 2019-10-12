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

module Lens.Lens
  {n m }
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

private
  variable
    n' m' n'' m'' : Level
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cart = Cartesian.Cartesian cart

open _Functor_
open _NatTrans_
open Cat.CommutativeSquare
open import Isomorphism
open cct
open mc
open smc
open cart
open cd


record Lens (s t a b : obj) : (Set m) where
  constructor MkLens

  field
    get :     s     hom a -- TODO make this even stronger by enforcing only "get" to be a comonoid homomorphism
    put : (s ⊗ₒ b) hom t

_lensHom_ : (obj × obj) → (obj × obj) → Set m
_lensHom_ (s , t) (a , b) = Lens s t a b

Pt : {x s : obj} {f : 𝟙 hom x}
  → (𝟙 , 𝟙) lensHom (x , s)
Pt {f = f} = MkLens f (λₘ ● ε)

CoPt : {y r : obj} {f : y hom r}
  → (y , r) lensHom (𝟙 , 𝟙)
CoPt {f = f} = MkLens ε (ρₘ ● f)

counit : {x : obj} → (x , x) lensHom (𝟙 , 𝟙)
counit = MkLens ε ρₘ


-- function lifting

◿ : {x y : obj}
  → (f : x hom y) → (x , 𝟙) lensHom (y , 𝟙)
Lens.get (◿ f) = f
Lens.put (◿ f) = ε ⊗ₘ id ● λₘ


_◺ : {x y : obj}
  → (f : x hom y) → (𝟙 , y) lensHom (𝟙 , x)
Lens.get (f ◺) = id
Lens.put (f ◺) = λₘ ● f

--counitLaw : {x y : obj} {f : x hom y}
--  → (ρₘ' ⊗ₘ id) ● ((◿ f) ⊗ₘ id) ● (ρₘ ⊗ₘ id) ● counit ≡ (id ⊗ₘ λₘ') ● (id ⊗ₘ (f ◺)) ● (id ⊗ₘ λₘ) ● counit


-- ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₂) ● put₁)
_●ₗ_ : {a b c : obj × obj}
  → a lensHom b
  →           b lensHom c
  → a      lensHom      c
_●ₗ_ {a = (a , a')} {b = (b , b')} {c = (c , c')}
  (MkLens get₁ put₁) (MkLens get₂ put₂)
  = MkLens
  (get₁ ● get₂)
    (                 begin→⟨     a      ⊗ₒ c'    ⟩
       δ ⊗ₘ id            →⟨ (a ⊗ₒ a) ⊗ₒ c'    ⟩
     (id ⊗ₘ get₁) ⊗ₘ id  →⟨ (a ⊗ₒ b) ⊗ₒ c'    ⟩
        αₘ                 →⟨  a ⊗ₒ (b ⊗ₒ c')   ⟩
       id ⊗ₘ put₂          →⟨  a ⊗ₒ     b'       ⟩
       put₁                 →⟨  a'                 ⟩end )
