module DependentFunctor where

open import Level
open import Function renaming (id to id→; _∘_ to _∘ᶠ_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Bool.Base

open import Category
open import Functor
open import CategoryOfCategories

private
  variable o n m n' m' n'' m'' : Level

open Cat renaming (_∘_ to _∘₁_)
open _Functor_

record _DepFunctor_ (cat₁ : Cat o m) (G : cat₁ Functor (catOfCats {o = o} {m = m})) : Set (o ⊔ m) where
  constructor MkDepFunctor
  open _Functor_ G renaming (mapObj to G₀; mapMor to G₁) -- G₀ is mapping on objects, G₁ is mapping on morphisms
  field
    mapDObj : (a : obj cat₁) → obj (G₀ a)
    mapDMor : {a b : obj cat₁} → (f : cat₁ [ a , b ]) → (G₀ b) [ (mapObj (G₁ f)) (mapDObj a) , mapDObj b ]

