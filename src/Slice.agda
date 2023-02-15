{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Product

open import Category
open import Functor
open import SliceOver
open import CategoryOfCategories
open import AgdaCategories
-- open import NaturalTransformation
import Shapes
open Cat


module Slice {o m} {cat : Cat o m} where
  open Shapes cat
  open SliceObj

  -- precomposition functor
  preComp : {x y : obj cat} (f : cat [ x , y ]) → (cat / x) Functor (cat / y)
  preComp f = MkFunctor
    (λ (MkSliceObj a g) → MkSliceObj a (cat [ g ● f ]))
    (λ (MkSliceHom r comm_r) → MkSliceHom r (extend comm_r f))
    (λ i → MkSliceHom {!!} {!!})
    {!!}


  // : cat Functor (ℂ𝕒𝕥 (o ⊔ m) {!!})
  // = MkFunctor
    (λ x → cat / x)
    (λ f → preComp f)
    {!!}
    {!!}

  -- secNat : {n : Level} → // NatTrans (constFunctor 𝕊𝕖𝕥 {n = n})
  -- secNat = ?
  -- ∫ : (cat Functor ℂ𝕒𝕥) →

  record GrothObj (F : cat Functor ℂ𝕒𝕥 o m) : Set o  where
    constructor MkGrothObj
    open _Functor_ F renaming (mapObj to F₀; mapMor to F₁)
    field
      base : obj cat
      point_over_base : obj (F₀ base)

  record GrothHom {F : cat Functor ℂ𝕒𝕥 o m} (a b : GrothObj F) : Set m where
    constructor MkGrothHom
    private
      module A = GrothObj a
      module B = GrothObj b
      open _Functor_ F renaming (mapObj to F₀; mapMor to F₁)
    field
      fw : cat [ A.base , B.base ]

    F⟨fw⟩ : (F₀ A.base) Functor (F₀ B.base)
    F⟨fw⟩ = F₁ fw

    open _Functor_ F⟨fw⟩ renaming (mapObj to F⟨fw⟩₀; mapMor to F⟨fw⟩₁) -- not using F⟨fw⟩₁ here

    field
      fw# : F₀ B.base  [ F⟨fw⟩₀ A.point_over_base , B.point_over_base ]

  --grothMorph : {F : cat Functor ℂ𝕒𝕥} → GrothObj F → GrothObj F → Set {!!}
  --grothMorph (MkGroth a a') (MkGroth b b') = {!!}

  grothMorph : {F : cat Functor ℂ𝕒𝕥 o m} {a b c : GrothObj F} →
             GrothHom a b → GrothHom b c → GrothHom a c
  grothMorph {F = F} {c = (MkGrothObj c c')} (MkGrothHom f f#) (MkGrothHom g g#) = MkGrothHom (cat [ f ● g ]) {!F₀ c [ mapMor (F₁ g) f# ● g# ]!} -- here we need to use properties as structure! Which means we need 2-categories
    where
    open _Functor_
    open _Functor_ F renaming (mapObj to F₀; mapMor to F₁)
    open GrothObj

  open _Functor_
  -- Grothendieck construction
  -- this functor (F) goes between two categories of different levels
  groth : cat Functor (ℂ𝕒𝕥 o m) → Cat o m
  groth F = MkCat
    (GrothObj F)
    (λ a b → GrothHom a b)
    (λ {a} → MkGrothHom (id cat {base a}) {!id (F₀ (base a)) {point_over_base a}!})
    grothMorph
    {!!}
    {!!}
    {!!}
    {!!}
    where
    open _Functor_ F renaming (mapObj to F₀)
    open GrothObj



  -- IndCatOp : cat Functor (ℂ𝕒𝕥 o m) → cat Functor (ℂ𝕒𝕥 o m)
  -- IndCatOp f = f ●F ᵒᵖ
