{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Shapes
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian
open import Lens.Lens using (Lens)
open import Isomorphism
open import MonoidalNaturalTransformation
import Lens.LensAssociativity
import Lens.LensCategory

module Lens.LensMonoidal
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

open Cat using (_[_,_])
open _Functor_
open _NatTrans_
open Shapes.CommutativeSquare
open Cat cat
open Monoidal.Monoidal mc
open SymmetricMonoidal.SymmetricMonoidal smc
open CD-Category.CD-Category cd
open CDAffine-Category.CDAffine-Category cda
open Cartesian.Cartesian cart
open Lens.Lens cart
open Lens.LensAssociativity cart using (lensAssoc)
open Lens.LensCategory cart

⊗ₗ : (lensCategory X lensCategory) Functor lensCategory
⊗ₗ = MkFunctor
  (mapObj swapProd)
  (λ (MkLens gₗ pₗ , MkLens gᵣ pᵣ) → MkLens (gₗ ⊗ₘ gᵣ) (|⇆|⊗ₘ ● (pₗ ⊗ₘ pᵣ)))
  (λ {_} → {!!}) -- cong₂ MkLens (idLaw ⊗) ?) -- (trans ? (sym left-id)))
  λ f@(MkLens gfₗ pfₗ , MkLens gfᵣ pfᵣ) g@(MkLens ggₗ pgₗ , MkLens ggᵣ pgᵣ) → {!!}
    -- cong₂ MkLens distribute⊗
    -- (let (MkLens gfgₗ pgfₗ) , (MkLens gfgᵣ pgfᵣ) = (lensCategory X lensCategory) Cat.[ f ● g ]
    -- in begin
    --     |⇆|⊗ₘ ● (pgfₗ ⊗ₘ pgfᵣ)
    -- ≡⟨   (let t = sym (eqPaths□ |⇆|⊗□) in {!t!} )   ⟩
    --        {!!}
    -- ≡⟨     {!!}   ⟩
    --     (δₘ ⊗ₘ id) ● ((id ⊗ₘ (gfₗ ⊗ₘ gfᵣ)) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ (|⇆|⊗ₘ ● (pgₗ ⊗ₘ pgᵣ))) ● (|⇆|⊗ₘ ● (pfₗ ⊗ₘ pfᵣ))
    -- ∎)


    --     (|⇆|⊗ ● (pgfₗ ⊗ₘ pgfᵣ))
    -- ≡⟨  {!!}  ⟩
    --     lensCategory Cat.[ (MkLens  (|⇆|⊗ ● (pfₗ ⊗ₘ pfᵣ))) ● (MkLens (ggₗ ⊗ₘ ggᵣ) ) ]
    -- ∎)
    --(begin
    --     |⇆|⊗ ● ({!? ● ?!} ⊗ₘ Lens.put (proj₂ ((lensCategory X lensCategory) Cat.[ f ● g ])))
    --≡⟨   {!!}   ⟩
    --     (δₘ ⊗ₘ id) ● ( (id ⊗ₘ  (gfₗ ⊗ₘ gfᵣ)) ⊗ₘ id) ● αₘ ● (id ⊗ₘ (|⇆|⊗ ● (pgₗ ⊗ₘ pgᵣ))) ● (|⇆|⊗ ● (pfₗ ⊗ₘ pfᵣ))
    --∎)
          --let (MkLens gfgₗ pgfₗ) , (MkLens gfgᵣ pgfᵣ) = (lensCategory X lensCategory) Cat.[ f ● g ]
          --in begin
          --    MkLens (gfgₗ ⊗ₘ gfgᵣ) (|⇆|⊗ ● (pgfₗ ⊗ₘ pgfᵣ))
          --≡⟨  {!!}  ⟩
          --    lensCategory Cat.[ (MkLens (gfₗ ⊗ₘ gfᵣ) (|⇆|⊗ ● (pfₗ ⊗ₘ pfᵣ))) ● (MkLens (ggₗ ⊗ₘ ggᵣ) (|⇆|⊗ ● (pgₗ ⊗ₘ pgᵣ))) ]
          --∎

--cfun : (f : cat Functor cat) → (g : cat Functor cat)
--  → f NatTrans g → lensCategory NatTrans lensCategory
--cfun = {!!}


lensMonoidal : Monoidal lensCategory
lensMonoidal = MkMonoidal
  ⊗ₗ
  (𝕀 , 𝕀)
  {!!}
  {!!}
  {!!}
  {!!} -- (cong₂ MkLens (Monoidal.▵-identity mc) {!!})
  {!!} -- (cong₂ MkLens (Monoidal.⬠-identity mc) {!!})
  --(MkIso (MkNatTrans (MkLens αₘ (π₂ ● αₘ')) (Cat.MkCommSq (cong₂ MkLens α□ {!!})))
  --       {!!}
  --       {!!}
  --       {!!})
  --(MkIso (MkNatTrans (MkLens λₘ (π₂ ● λₘ')) (Cat.MkCommSq (cong₂ MkLens λ□ {!!})))
  --       (MkNatTrans (MkLens λₘ' (π₂ ● λₘ)) (Cat.MkCommSq (cong₂ MkLens λ□' {!!})))
  --       {!!}
  --       {!!})
  --(MkIso (MkNatTrans (MkLens ρₘ (π₂ ● ρₘ')) (Cat.MkCommSq (cong₂ MkLens ρ□ {!!})))
  --       (MkNatTrans (MkLens ρₘ' (π₂ ● ρₘ)) (Cat.MkCommSq (cong₂ MkLens ρ□' {!!})))
  --       {!!}
  --       {!!})

-- lensSymmetricMonoidal : SymmetricMonoidal lensMonoidal
-- lensSymmetricMonoidal = MkSymmMonoidal (MkIso
--   {!!}
--   {!!}
--   -- (MkNatTrans (◿ σₘ || σₘ ◺) (Cat.MkCommSq (cong₂ MkLens σ□ {!!})))
--   -- (MkNatTrans (◿ σₘ || σₘ ◺) {!!})
--   {!!}
--   {!!})


-- counitLaw : {x y : obj} {f : x hom y}
--   →
--counitLaw : {x y : obj} {f : x hom y}
--  → (ρₘ' ⊗ₘ id) ● ((◿ f) ⊗ₘ id) ● (ρₘ ⊗ₘ id) ● counit ≡ (id ⊗ₘ λₘ') ● (id ⊗ₘ (f ◺)) ● (id ⊗ₘ λₘ) ● counit
