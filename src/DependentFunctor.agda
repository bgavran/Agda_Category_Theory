module DependentFunctor where

open import Level
open import Function renaming (id to id→; _∘_ to _∘ᶠ_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Bool.Base

open import Category
open import Functor
open import NaturalTransformation
open import CategoryOfCategories

private
  variable o n m n' m' n'' m'' : Level

open Cat renaming (_∘_ to _∘₁_)
open _Functor_
open _NatTrans_

record _DepFunctor_ (cat₁ : Cat o m) (G : cat₁ Functor (ℂ𝕒𝕥 o m)) : Type (o ⊔ m) where
  constructor MkDepFunctor
  open _Functor_ G renaming (mapObj to G₀; mapMor to G₁) -- G₀ is mapping on objects, G₁ is mapping on morphisms
  field
    mapDObj : (a : obj cat₁) → obj (G₀ a)
    mapDMor : {a b : obj cat₁} → (f : cat₁ [ a , b ]) → (G₀ b) [ (mapObj (G₁ f)) (mapDObj a) , mapDObj b ]
    idDLaw : {a : obj cat₁} → id (G₀ a) {mapDObj a} ≡ let t = mapDMor (id cat₁ {a}) in {!t!} -- need to do a idLaw for G rewrite?
    -- compLaw


record _DepNatTrans_ 
  {cat₁ : Cat o m}
  {G G' : cat₁ Functor (ℂ𝕒𝕥 o m)}
  (F : cat₁ DepFunctor G)
  (F' : cat₁ DepFunctor G') : Type (suc (o ⊔ m)) where
  constructor MkDepNatTrans
  open _Functor_ G renaming (mapObj to G₀; mapMor to G₁) -- F₀ is mapping on objects, F₁ is mapping on morphisms
  open _Functor_ G' renaming (mapObj to G'₀; mapMor to G'₁)

  open _DepFunctor_ F renaming (mapDObj to F₀; mapDMor to F₁) -- F₀ is mapping on objects, F₁ is mapping on morphisms
  open _DepFunctor_ F' renaming (mapDObj to F'₀; mapDMor to F'₁)
  field
    nt : G NatTrans G'
    α : (a : obj cat₁) →  G'₀ a [ (mapObj (η nt {a})) (F₀ a),  (F'₀ a) ]

-- let t = id (G₀ a) {mapDObj a}
--                                   w = mapDMor (id cat₁ {a})
--                               in {!!}

