open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Data.Product

open import Category
open import Functor
open import SliceOver
open import CategoryOfCategories
open import SetInstance
open import NaturalTransformation
import Shapes


module Slice {o m} {cat : Cat o m} where
  open Cat cat
  open Shapes cat
  open SliceObj

  tt : cat [ ? , ? ] -- why isn't it possible to define this?

  -- precomposition functor
  preComp : {x y : obj} (f : x hom y) → (cat / x) Functor (cat / y)
  preComp f = MkFunctor
    (λ (MkSliceObj a g) → MkSliceObj a (g ● f))
    (λ (MkSliceHom r comm_r) → MkSliceHom r (extend comm_r f))
    (λ i → MkSliceHom {!!} {!!})
    {!!}


  // : cat Functor catOfCats
  // = MkFunctor
    (λ x → cat / x)
    (λ f → preComp f)
    {!!}
    {!!}

  -- secNat : {n : Level} → // NatTrans (constFunctor 𝕊𝕖𝕥 {n = n})
  -- secNat = ?
  -- ∫ : (cat Functor catofCats) →

  record GrothObj (F : cat Functor catOfCats {o} {m}) : Set o  where
    constructor MkGroth
    module fun = _Functor_ F
    open fun renaming (mapObj to F₀; mapMor to F₁)
    field
      base : obj
      point_over_base : Cat.obj (F₀ base)

  record GrothHom {F : cat Functor catOfCats {o} {m}} (a b : GrothObj F) : Set {!!} where
    constructor MkGrothHom
    private
      module A = GrothObj a
      module B = GrothObj b
      open _Functor_ F renaming (mapObj to F₀; mapMor to F₁)
    field
      fw : A.base hom B.base

    F⟨fw⟩ : (F₀ A.base) Functor (F₀ B.base)
    F⟨fw⟩ = F₁ fw

    open _Functor_ F⟨fw⟩ renaming (mapObj to F⟨fw⟩₀; mapMor to F⟨fw⟩₁)
      
    field
      -- fw' : {! ? [ ? , ? ]!}
      --fw' : (F⟨fw⟩₀ A.point_over_base) hom B.point_over_base

  --grothMorph : {F : cat Functor catOfCats} → GrothObj F → GrothObj F → Set {!!}
  --grothMorph (MkGroth a a') (MkGroth b b') = {!!}

  g : (F : cat Functor catOfCats {o} {m}) → Cat o {!!}
  g F = MkCat
    (GrothObj F)
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}


