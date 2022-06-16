{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
import Monoidal
open import MonoidalFunctor

module MonoidalNaturalTransformation
  {n m n' m'}
  {cat1 : Cat n m}
  {cat2 : Cat n' m'}
  {mc1 : Monoidal.Monoidal cat1}
  {mc2 : Monoidal.Monoidal cat2}
  where

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open Isomorphism._≅_
open Cat
open import Shapes
open Shapes.CommutativeSquare
open Shapes.CommutativeTriangle
open _Functor_
open MonoidalFunctor._MonoidalFunctor_
open _NatTrans_
private
  module MC1 = Monoidal.Monoidal mc1
  module MC2 = Monoidal.Monoidal mc2
open MC1 renaming (⊗ to ⊗₁;𝕀 to 𝕀₁)
open MC2 renaming (⊗ to ⊗₂;𝕀 to 𝕀₂)

record _MonoidalNatTrans_ (mf1 mf2 : mc1 MonoidalFunctor mc2) : Set (n ⊔ m ⊔ n' ⊔ m') where
  constructor MkMonoidalNatTrans
  private
    module MF1 = MonoidalFunctor._MonoidalFunctor_ mf1
    module MF2 = MonoidalFunctor._MonoidalFunctor_ mf2


  open MF1 renaming (F to F₁; ϕ to ϕ₁; ψ to ψ₁)
  open MF2 renaming (F to F₂; ϕ to ϕ₂; ψ to ψ₂)
  field
    θ : F₁ NatTrans F₂
    id▵ : cat2 [ ψ₁ ● η θ ] ≡ ψ₂
    commSquareMonoidalTrans :  functorCategory [ ϕ₁ ● (whiskerₗ ⊗₁ θ) ] ≡ functorCategory [ (whiskerᵣ (θ 𝕏ₙ θ) ⊗₂ ) ● ϕ₂ ]


idMonoidalNatTransform : {mf : mc1 MonoidalFunctor mc2}
  → mf MonoidalNatTrans mf
idMonoidalNatTransform {mf = mf} = MkMonoidalNatTrans
  idNatTrans
  (left-id cat2)
  {!!}


-- Composition of natural transformations
_●ᵥₘ_ : {mf mg mh : mc1 MonoidalFunctor mc2}
  → mf MonoidalNatTrans mg
  →            mg MonoidalNatTrans mh
  → mf      MonoidalNatTrans       mh
_●ᵥₘ_ {mf = mf} {mg = mg} {mh = mh} (MkMonoidalNatTrans θ₁ id▵₁ commSq₁) (MkMonoidalNatTrans θ₂ id▵₂ commSq₂) = MkMonoidalNatTrans
  (θ₁ ●ᵥ θ₂)
  (glue▵→' cat2 id▵₁ id▵₂)
  (let t = glue□↓' functorCategory commSq₁  commSq₂ in cong (λ tt@(MkNatTrans η natur) → {!!}) t)
    --begin
    --     functorCategory [ ϕ₁ ● (whiskerᵣ ⊗₁ (θ₁ ●ᵥ θ₂)) ]
    --   ≡⟨  {!!}  ⟩
    --     functorCategory [ (whiskerₗ ⊗₂ ((θ₁ ●ᵥ θ₂) 𝕏ₙ (θ₁ ●ᵥ θ₂))) ● ϕ₃ ]
    --∎)
  where
  private
    module MF1 = MonoidalFunctor._MonoidalFunctor_ mf
    module MF2 = MonoidalFunctor._MonoidalFunctor_ mg
    module MF3 = MonoidalFunctor._MonoidalFunctor_ mh


  open MF1 renaming (F to F₁; ϕ to ϕ₁; ψ to ψ₁)
  open MF2 renaming (F to F₂; ϕ to ϕ₂; ψ to ψ₂)
  open MF3 renaming (F to F₃; ϕ to ϕ₃; ψ to ψ₃)

monoidalFunctorCategory : Cat (n ⊔ m ⊔ n' ⊔ m') (n ⊔ m ⊔ n' ⊔ m')
monoidalFunctorCategory = MkCat
  (mc1 MonoidalFunctor mc2)
  _MonoidalNatTrans_
  idMonoidalNatTransform
  _●ᵥₘ_
  {!!}
  {!!}
  {!!}
  {!!}

monoidalFunctorCategoryIsMonoidal : Monoidal.Monoidal monoidalFunctorCategory
monoidalFunctorCategoryIsMonoidal = Monoidal.MkMonoidal
  (MkFunctor (λ (F , G) → {!? ●F ?!}) {!!} {!!} {!!})
  ({!!})
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
