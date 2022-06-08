{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Category
open import Functor
open import Utils
open import CategoryOfCategories
open import SliceOver
open import SetInstance

module Section {n m} {cat : Cat n m} where


module cat = Cat cat
open cat hiding (_[_,_]; _ᵒᵖ)
open Cat using (_[_,_]; _ᵒᵖ)

open SliceObj

record Sec {x y : obj} (p : y hom x) : Set (n ⊔ m) where
  constructor MkSec
  field
    s : x hom y
    rightInverseLaw : s ● p ≡ id

-- record _secHom_ {a b : Cat.obj cat} {p : (cat Cat.hom b) a} (s t : Sec p) : Set (n ⊔ m) where
--   constructor MkSliceHom
--   field
-- secHom : {a b : Cat.obj cat} {p : (cat Cat.hom b) a} → Sec p → Sec p → Set {!!}
-- secHom (MkSec s rₛ) (MkSec t rₜ)= {!!}


-- this actually forms a set, instead of a category. Here we take that set Sec p and consider it as a discrete category
secCat : {a b : obj} (p : b hom a) → Cat (n ⊔ m) (n ⊔ m)
secCat p = disc (Sec p)


secOnMorph : {a : obj} {f g : Cat.obj (cat / a)}
  → (cat / a)  [ f , g ] → 𝕊𝕖𝕥 [ Sec (proj f) , Sec (proj g) ]
secOnMorph (MkSliceHom r cᵣ) = λ (MkSec s rₛ) → MkSec (s ● r) {!!}
  -- where
  -- open sliceovercat
  -- open sliceovershp

-- (C/A)
sec : {a : obj} → (cat / a) Functor 𝕊𝕖𝕥
sec = MkFunctor
  (λ (MkSliceObj y f) → Sec f)
  secOnMorph
  {!!}
  {!!}
