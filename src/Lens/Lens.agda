open import Level
open import Function using (flip)
open import Data.Product
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

open import CategoryOfCategories
open CategoryOfCategories
--module catc = Cat catOfCats
--open catc using (monomorphism)

module Lens.Lens
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  --{catc : Cat n m}
  --(incl : Cat._hom_ catOfCats catc cat)
  --(mₚ : Cat.monomorphism catOfCats incl)
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
import Shapes
open Shapes.CommutativeSquare
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

Pt : {x s : obj}
  → (f : 𝕀 hom x) → (𝕀 , 𝕀) lensHom (x , s)
Pt f = MkLens f (λₘ ● εₘ)

CoPt : {y r : obj}
  → (f : y hom r) → (y , r) lensHom (𝕀 , 𝕀)
CoPt f = MkLens εₘ (ρₘ ● f)


-- function lifting

◿_||_◺ : {x y z w : obj}
  → (f : x hom y) → (g : w hom z) → (x , z) lensHom (y , w)
◿ f || g ◺ = MkLens f (π₂ ● g)

◿ : {x y : obj}
  → (f : x hom y) → (x , 𝕀) lensHom (y , 𝕀)
◿ f = ◿ f || id ◺


_◺ : {x y : obj}
  → (f : x hom y) → (𝕀 , y) lensHom (𝕀 , x)
f ◺ = ◿ id || f ◺

lensId : {a : obj × obj} → a lensHom a
lensId = ◿ id || id ◺

-- ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₂) ● put₁)
_●ₗ_ : {a b c : obj × obj}
  → a lensHom b
  →           b lensHom c
  → a      lensHom      c
_●ₗ_ {a = (a , a')} {b = (b , b')} {c = (c , c')}
  (MkLens get₁ put₁) (MkLens get₂ put₂)
  = MkLens
  (get₁ ● get₂)
    (                 begin→⟨     a      ⊗ₒ c'    ⟩
       δₘ ⊗ₘ id            →⟨ (a ⊗ₒ a) ⊗ₒ c'    ⟩
     (id ⊗ₘ get₁) ⊗ₘ id  →⟨ (a ⊗ₒ b) ⊗ₒ c'    ⟩
        αₘ                 →⟨  a ⊗ₒ (b ⊗ₒ c')   ⟩
       id ⊗ₘ put₂          →⟨  a ⊗ₒ     b'       ⟩
       put₁                 →⟨  a'                 ⟩end )
