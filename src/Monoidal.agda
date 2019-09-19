module Monoidal where

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation

private
  variable n m n' m' n'' m'' : Level



record Monoidal (cat : Cat n m) : (Set (n ⊔ m)) where
  constructor MkMonoidal
  open Cat
  open _Functor_

  field
    ⊗ : (cat X cat) Functor cat
    𝟙 : obj cat

  x⊗[y⊗z] : (cat X (cat X cat)) Functor cat
  x⊗[y⊗z] = ⊗ functorComp (idFunctor 𝕏 ⊗)

  [x⊗y]⊗z : (cat X (cat X cat)) Functor cat
  [x⊗y]⊗z = ⊗ functorComp ((⊗ 𝕏 idFunctor) functorComp productAssociatorᵣ)

  [𝟙⊗x] : cat Functor cat
  [𝟙⊗x] = ⊗ functorComp (constFunctor 𝟙 /\ idFunctor)

  [x⊗𝟙] : cat Functor cat
  [x⊗𝟙] = ⊗ functorComp (idFunctor /\ constFunctor 𝟙)

  field
    associator  : Isomorphism (functorCategory (cat X (cat X cat)) cat)
      [x⊗y]⊗z x⊗[y⊗z]
    leftUnitor  : Isomorphism (functorCategory cat cat)
      [𝟙⊗x] idFunctor
    rightUnitor : Isomorphism (functorCategory cat cat)
      [x⊗𝟙] idFunctor

   -- TODO coherence conditions
