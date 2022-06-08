open import Level
open import Function renaming (id to id→; _∘_ to _∘ᶠ_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

import Shapes
open import Category

module Initial
  {o m}
  {cat : Cat o m} where

module cat = Cat cat
open cat
module initialshp = Shapes cat
open initialshp

record Initial (I : obj) : Set (o ⊔ m) where
  constructor MkInitial
  field
    ι : (a : obj) → I hom a
    commTr : {a b : obj} {f : a hom b} → CommutativeTriangle (ι a) f (ι b)



-- terminal in cat is initial in catᵒᵖ


-- limit as a natural transformation from the constant functor at 
-- record Initial : Set (n ⊔ m) where
--   constructor MkInitial
--   field
--     0 : obj
--     universality : ∀ a : obj 
