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
open Cat using (Isomorphism)
open Cat.Isomorphism
open _Functor_
open _NatTrans_

module Monoidal {n m} (cat : Cat n m) where

module cc = Cat cat
open cc hiding (Isomorphism)

private
  variable n' m' n'' m'' : Level

record Monoidal : Set (n ⊔ m) where
  constructor MkMonoidal

  field
    ⊗ : (cat X cat) Functor cat
    𝟙 : obj

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

  _⊗ₒ_ : obj → obj → obj
  _⊗ₒ_ = curry (mapObj ⊗)

  private
    variable
      a b c d : obj

  _⊗ₘ_ : a hom b
        → c hom d
        → (a ⊗ₒ c) hom (b ⊗ₒ d)
  _⊗ₘ_ = curry (mapMor ⊗)

  λₒ : (𝟙 ⊗ₒ a) hom  a
  λₒ = η (forward leftUnitor)

  ρₒ : (a ⊗ₒ 𝟙) hom  a
  ρₒ = η (forward rightUnitor)

  αₒ : ((a ⊗ₒ b) ⊗ₒ c)
     hom (a ⊗ₒ(b ⊗ₒ c))
  αₒ = η (forward associator)

  move⊗ : {a b c d e j : obj}
    → (f : a hom c )
    → (g : b hom d )
    → (h : c hom e )
    → (i : d hom j )
    → (h ∘ f) ⊗ₘ (i ∘ g) ≡ (h ⊗ₘ i) ∘ (f ⊗ₘ g )
  move⊗ f g h i = compLaw ⊗ (f , g) (h , i)


   -- TODO coherence conditions
