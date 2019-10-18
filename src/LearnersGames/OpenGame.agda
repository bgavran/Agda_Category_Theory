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

module LearnersGames.OpenGame
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  {cart : Cartesian cda}
  where

open import Lens.Lens hiding (Lens; Pt; CoPt; _lensHom_)
private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cart = Cartesian.Cartesian cart
  module ll = Lens.Lens cart

open _Functor_
open _NatTrans_
open Cat.CommutativeSquare
open import Isomorphism
open cct
open mc
open smc
open cart
open ll

record OpenGame {s t a b : obj} (lens : Lens s t a b) : Set (suc (n ⊔ m)) where
  constructor MkOpenGame
  field
    Σₚ : Set n
    G : Σₚ → Lens s t a b
    -- the below is equivalent to X × (Y → R) → Σₚ → Bool
    EqPred : {x y s r : obj}
      → (𝟙 , 𝟙) lensHom (x , s) → (y , r) lensHom (𝟙 , 𝟙) → Σₚ → Bool
