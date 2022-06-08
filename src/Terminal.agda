open import Level
open import Function renaming (id to id→; _∘_ to _∘ᶠ_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

import Shapes
open import Category

module Terminal
  {o m}
  {cat : Cat o m} where

module cat = Cat cat
open cat
module terminalshp = Shapes cat
open terminalshp

record Terminal (T : obj) : Set (o ⊔ m) where
  constructor MkTerminal
  field
    ! : (a : obj) → a hom T
    commTr : {a b : obj} {f : a hom b} → CommutativeTriangle f (! b) (! a)




-- catWithOneObjectTerminal : Terminal {}{cat = catOfCats} oneObjectCat
-- catWithOneObjectTerminal = ?

-- terminal in cat is initial in catᵒᵖ
