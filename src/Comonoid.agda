module Comonoid where

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

private
  variable
    n m n' m' n'' m'' : Level

record Comonoid {cat : Cat n m} {mc : Monoidal cat} (smc : SymmetricMonoidal mc) : (Set (n ⊔ m)) where
  constructor MkComonoid
  open _Functor_
  module C = Cat cat
  open C
  module M = Monoidal.Monoidal mc
  open M
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  open S

  field
    δ : {c : obj} → cat [ c , c ⊗ₒ c ] -- multiplication
    ε : {c : obj} → cat [ c , 𝟙 ]       -- counit

    copySwap   : {c : obj} → (_σₒ_ ∘ δ) ≡ δ {c = c}
    copyDelete : {c : obj} → leftUnitorₒ {a = c} ∘ (ε ⊗ₘ id) ∘ δ ≡ id
    copyAssoc  : {c : obj} → αₒ ∘ (δ ⊗ₘ id) ∘ δ {c = c}
                                ≡ (id ⊗ₘ δ) ∘ δ {c = c}
