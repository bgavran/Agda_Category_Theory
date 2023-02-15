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

switch : Bool → Type
switch false = Unit
switch true = Bool

dd : obj DepLens
dd = MkGrothObj Bool switch

cc : obj DepLens
cc = MkGrothObj Bool switch


h : DepLens [ MkGrothObj Bool switch , MkGrothObj Bool switch ]
h = MkGrothHom id' λ { false _  → {!!}
                           ; true → {!!}}
