module Monoidal where

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

private
  variable n m n' m' n'' m'' : Level



record Monoidal (cat : Cat n m) : (Set (n ⊔ m)) where
  constructor MkMonoidal
  open Cat
  open Cat.Isomorphism
  open _Functor_
  open _NatTrans_

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

  _⊗ₒ_ : obj cat → obj cat → obj cat
  _⊗ₒ_ = curry (mapObj ⊗)

  private
    variable
      a b c d : obj cat

  _⊗ₘ_ : cat [ a , b ]
        → cat [ c , d ]
        → cat [ a ⊗ₒ c , b ⊗ₒ d ]
  _⊗ₘ_ = curry (mapMor ⊗)

  λₒ : cat [ 𝟙 ⊗ₒ a ,  a ]
  λₒ = η (forward leftUnitor)

  ρₒ : cat [ a ⊗ₒ 𝟙 ,  a ]
  ρₒ = η (forward rightUnitor)

  αₒ : cat [ (a ⊗ₒ b) ⊗ₒ c , a ⊗ₒ(b ⊗ₒ c) ]
  αₒ = η (forward associator)


   -- TODO coherence conditions
