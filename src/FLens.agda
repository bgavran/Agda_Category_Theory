{-# OPTIONS --allow-unsolved-metas #-}
module FLens where

open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base
open import Cubical.Data.Unit.Base using (Unit; tt) -- for the terminal category
open import Cubical.Data.Empty using (⊥) -- for the initial category

open import Category
open import Functor
open import CategoryOfCategories
open import Slice

open import AgdaCategories



open Cat
open _Functor_


FLens : {o m : Level}
  → (c : Cat o m)
  → (c ᵒᵖᶜ) Functor (ℂ𝕒𝕥 o m)
  → Cat o m
FLens _ f = groth (f ●F ᵒᵖ)

DepLens' : {o : Level} → Cat (suc o) o
DepLens' {o} = FLens (𝕋𝕪𝕡𝕖 o) (FamInd {o})

DepAdt' : {o : Level} → Cat (suc o) o
DepAdt' {o} = FLens (𝕋𝕪𝕡𝕖 o) (Fam0Ind {o})

DepLens : Cat (suc 0ℓ) 0ℓ
DepLens = DepLens' {0ℓ}

DepAdt : Cat (suc 0ℓ) 0ℓ
DepAdt = DepAdt' {0ℓ}

Adt' : {o m : Level}
  → (c : Cat o m)
  → (d : Cat o m)
  → Cat o m
Adt' c d = FLens c (constFunctor d)

switch : Bool → Type
switch false = Unit
switch true = Bool

test : DepLens [ MkGrothObj Bool switch , MkGrothObj Bool switch ]
test = MkGrothHom id' λ { false _  → tt
                        ; true b → not b}

-- seems like this is a known bug and will be fixed in the next version?
-- https://github.com/agda/agda/issues/691
hh : DepAdt [ MkGrothObj Bool (λ _ → Bool) , MkGrothObj Bool (λ _ → Bool) ]
hh = MkGrothHom id' λ x b → {!not b!}
