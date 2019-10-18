open import Level
open import Function using (flip)
open import Data.Product
open import Data.Bool
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
open import Bicartesian

open Cat using (_ᵒᵖ)

module LearnersGames.Learner
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  {cart : Cartesian cda}
  {mcop : Monoidal (cat ᵒᵖ)}
  {smcop : SymmetricMonoidal mcop}
  {cdop : CD-Category smcop}
  {cdaop : CDAffine-Category cdop}
  {cartop : Cartesian cdaop}
  (bicart : Bicartesian cart cartop) where

import Lens.Lens as L
import Lens.LensCategory as LC
import Lens.LensAssociativity
import Lens.SimpleLens

private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cdop = CD-Category.CD-Category cdop
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart
  module lenss = L cart
  module lc = LC cart
  module lensassoc = Lens.LensAssociativity cart
  module sl = Lens.SimpleLens cart
  module bc = Bicartesian.Bicartesian bicart

open _Functor_
open Cat.CommutativeSquare
open import Isomorphism
open Cat using (_[_●_])
open cct hiding (_[_●_]; _ᵒᵖ)
open mc
open smc
open cd
open cdop renaming (ε to η; δ to +)
open cda
open cart
open lenss
open lc
open lensassoc using (lensAssoc)
open sl


module slcat = Cat simpleLensCategory
open slcat renaming (id to idᴸ;
                     _●_ to _●ᴸ_;
                     obj to objᴸ;
                     _hom_ to _homᴸ_) hiding (_ᵒᵖ)

module slMonoidal = Monoidal.Monoidal simpleLensMonoidal
open slMonoidal renaming (_⊗ₒ_ to _⊗ₒᴸ_;
                          _⊗ₘ_ to _⊗ₘᴸ_;
                          𝟙 to 𝟙ᴸ;
                          αₘ to αₘᴸ;
                          αₘ' to αₘᴸ';
                          λₘ to λₘᴸ;
                          ρₘ to ρₘᴸ;
                          λₘ' to λₘᴸ';
                          ρₘ' to ρₘᴸ')


record VectorSpace : Set (suc n) where
  field
    𝕍 : Set n
    _+_ : 𝕍 → 𝕍 → 𝕍
    _*_ : 𝕍 → 𝕍 → 𝕍
    𝟘 : 𝕍
    𝟙 : 𝕍


learnerLens : {p x y : obj} → SimpleLens (p ⊗ₒ x) y
learnerLens = {!!}

dataa : {x y : obj} → 𝟙 hom (x ⊗ₒ y)
dataa = {!!}

dataLens : {x y : obj} → SimpleLens 𝟙 (x ⊗ₒ y)
dataLens = MkSimpleLens (Pt dataa)


negate : {r : obj} → SimpleLens r r
negate = MkSimpleLens' {!λ x → -x!} {!derivative!}

sqr : {r : obj} → SimpleLens r r
sqr = MkSimpleLens' {!λ x → x²!} {!derivative!}

-- this will be the monoid operation
sum : {r : obj} → SimpleLens (r ⊗ₒ r) r
sum = MkSimpleLens' {!λ (a, b) → a + b!} {!derivative!}


squaredDifference : {r : obj} → SimpleLens (r ⊗ₒ r) r
squaredDifference {r = r} = (idᴸ ⊗ₘᴸ negate) ●ᴸ sum ●ᴸ sqr

grad : {r : obj} → SimpleLens r 𝟙
grad = MkSimpleLens (CoPt let create : {c : Cat.obj cat} → (Monoidal.𝟙 mcop) hom c
                              create = η
                              destroy = ε
                           in {!!} ● create)

inEnvironment : {x y p : obj}
  → SimpleLens (p ⊗ₒ x) y
  → SimpleLens p 𝟙
inEnvironment l = ρₘᴸ' ●ᴸ (idᴸ ⊗ₘᴸ dataLens) ●ᴸ αₘᴸ' ●ᴸ (l ⊗ₘᴸ idᴸ ) ●ᴸ squaredDifference ●ᴸ grad


sgd : {p : obj} → (p ⊗ₒ p) hom p
sgd = {!!}

updateParams : {p : obj} → SimpleLens p 𝟙 → p hom p
updateParams (MkSimpleLens (MkLens _ p)) = δ ● (id ⊗ₘ (ρₘ' ● p)) ● sgd
