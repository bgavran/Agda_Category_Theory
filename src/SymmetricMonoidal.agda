module SymmetricMonoidal where


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



private
  variable
    n m n' m' n'' m'' : Level
    cat : Cat n m

record SymmetricMonoidal {cat : Cat n m} (mc : Monoidal cat) : (Set (n ⊔ m)) where
  constructor MkSymmMonoidal
  open Cat
  open Cat.Isomorphism
  open _Functor_
  open _NatTrans_
  module M = Monoidal.Monoidal mc
  open M

  field
    σ : Isomorphism (functorCategory (cat X cat) cat) ⊗ (⊗ functorComp swapFunctor)

  σₒ : {a b : obj cat} → cat [ a ⊗ₒ b , b ⊗ₒ a ]
  σₒ = η (forward σ)

  -- TODO coherence
