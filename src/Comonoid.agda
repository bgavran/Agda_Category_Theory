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

record Cartesian
  {cat : Cat n m}
  {mc : Monoidal cat}
  (smc : SymmetricMonoidal mc)
  : (Set (n ⊔ m)) where
  constructor MkComonoid
  module C = Cat cat
  open C
  module M = Monoidal.Monoidal mc
  open M
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  open S

  field
    -- TODO these should actually be monoidal natural transformations?
    δ : {c : obj} → cat [ c , c ⊗ₒ c ] -- multiplication
    ε : {c : obj} → cat [ c , 𝟙 ]       -- counit

    copySwap   : {c : obj} → (σₒ ∘ δ) ≡ δ {c = c}
    copyDelete : {c : obj} → λₒ {a = c} ∘ (ε ⊗ₘ id) ∘ δ ≡ id
    copyAssoc  : {c : obj} → αₒ ∘ (δ ⊗ₘ id) ∘ δ {c = c}
                                 ≡ (id ⊗ₘ δ) ∘ δ {c = c}

    deleteApply : {a b : obj} {f : cat [ a , b ] } → ε ≡ cat [ ε ∘ f ]
    copyApply : {a b : obj} {f : cat [ a , b ] } → cat [ δ  ∘ f ] ≡ cat [ (f ⊗ₘ f) ∘ δ ]

  π₁ : {a b : obj} → cat [ a ⊗ₒ b , a ]
  π₁ = cat [ ρₒ ∘ (id ⊗ₘ ε) ]

  π₂ : {a b : obj} → cat [ a ⊗ₒ b , b ]
  π₂ = cat [ λₒ ∘ (ε ⊗ₘ id) ]

  -- TODO prove universal property of cartesian product?


{-
record ComonoidHom {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  {a b : obj cat}
  (c₁ : Comonoid smc a)
  (c₂ : Comonoid smc b)
  : Set m where
  constructor MkComonoidHom
  module C₁ = Comonoid c₁
  open C₁ renaming (ε to ε₁; δ to δ₁)
  module C₂ = Comonoid c₂
  open C₂ renaming (ε to ε₂; δ to δ₂)
  module mc = Monoidal.Monoidal mc
  open mc

  -- map between objects which preserves comonoid structure
  field
    f : cat [ a , b ]
    deleteApply : ε₁ ≡ cat [ ε₂ ∘ f ]
    copyApply : cat [ δ₂ ∘ f ] ≡ cat [ (f ⊗ₘ f) ∘ δ₁ ]


-- category of commutative comonoids
-- also a cartesian monoidal category?
comm : {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  → Cat n m
comm {cat = cat} {mc = mc} {smc = smc} = MkCat
  (let tt = Comonoid smc
       t = obj cat
       -- ttt = map tt t
   in {!!})
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

  {!!}


-}
