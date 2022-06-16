open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Shapes
open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian

module Lens.LawfulSimpleLens
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

import Lens.Lens as L
import Lens.LensCategory as LC
import Lens.LensAssociativity
import Lens.SimpleLens

open _Functor_
open Shapes.CommutativeSquare
open Cat cat
open Monoidal.Monoidal mc
open SymmetricMonoidal.SymmetricMonoidal smc
open CD-Category.CD-Category cd
open CDAffine-Category.CDAffine-Category cda
open Cartesian.Cartesian cart
open L cart
open LC cart
open Lens.LensAssociativity cart using (lensAssoc)
open Lens.SimpleLens cart


record LawfulSimpleLens (a b : obj) : (Set m) where
  constructor MkLawfulSimpleLens
  field
    simpleLens : SimpleLens a b
  open SimpleLens simpleLens
  open Lens lens

  field
    putGetLaw : put ● get ≡ π₂
    putPutLaw : (put ⊗ₘ id ) ● put ≡ (π₁ ⊗ₘ id ) ● put
    getPutLaw : δ ● (id ⊗ₘ get) ● put ≡ id

lawfulSimpleLensId : {a : obj} → LawfulSimpleLens a a
lawfulSimpleLensId = MkLawfulSimpleLens
  (Cat.id simpleLensCategory)
  (trans left-id left-id)
  (begin
       ((π₂ ● id) ⊗ₘ id) ● (π₂ ● id)
   ≡⟨  refl⟨●⟩ left-id ⟩
       ((π₂ ● id) ⊗ₘ id) ● π₂
   ≡⟨  π₂law ⟩
       π₂ ● id
   ≡⟨  sym π₂law ⟩
        (π₁ ⊗ₘ id) ● π₂
   ≡⟨  refl⟨●⟩ (sym left-id) ⟩
        (π₁ ⊗ₘ id) ● (π₂ ● id)
   ∎)
  (begin
       δ ● (id ⊗ₘ id) ● (π₂ ● id)
   ≡⟨  (refl⟨●⟩ idLaw ⊗) ⟨●⟩ left-id   ⟩
       δ ● id ● π₂
   ≡⟨  trans (left-id ⟨●⟩refl)  ? ⟩ -- CD-Category.CD-Category.δ●π₂≡id ⟩
       id
   ∎)

-- LawfulSimpleLens composition
_●ₗₛₗ_ : {a b c : obj} →
  LawfulSimpleLens a b → LawfulSimpleLens b c → LawfulSimpleLens a c
_●ₗₛₗ_ (MkLawfulSimpleLens g _ _ _) (MkLawfulSimpleLens f _ _ _) = MkLawfulSimpleLens (g ●ₛₗ f) {!!} {!!} {!!}


lawfulSimpleLensCategory : Cat n m
lawfulSimpleLensCategory = MkCat
  (Cat.obj simpleLensCategory)
  (LawfulSimpleLens)
  lawfulSimpleLensId
  _●ₗₛₗ_
  {!!}
  {!!}
  {!!}
  {!!}

lawfulSimpleLensMonoidal : Monoidal lawfulSimpleLensCategory
lawfulSimpleLensMonoidal = MkMonoidal
  (MkFunctor {!!} {!!} {!!} {!!})
  (Monoidal.𝕀 simpleLensMonoidal)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

-- lawfulSimpleLensCDAffineCategory : CDAffine-Category simpleLensCDCategory
-- lawfulSimpleLensCDAffineCategory = MkCDAffine (λ {a = a} {b = b} {f = f} →
--   let MkSimpleLens (MkLens gf pf) = f
--   in cong MkSimpleLens
--   (begin
--       MkLens ε π₁
--    ≡⟨ cong₂ MkLens deleteApply (
--      begin
--           π₁
--      ≡⟨  {!!} ⟩
--          (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (π₁ ● gf)) ● pf
--      ≡⟨  (refl⟨●⟩ (sym left-id ⟨⊗⟩ sym π₁law)) ⟨●⟩refl ⟩
--          (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ((gf ⊗ₘ id) ● π₁)) ● pf
--      ≡⟨  (refl⟨●⟩ distribute⊗) ⟨●⟩refl ⟩
--          (δ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (gf ⊗ₘ id)) ● (id ⊗ₘ π₁)) ● pf
--      ≡⟨  sym assoc ⟨●⟩refl ⟩
--          (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (gf ⊗ₘ id)) ● (id ⊗ₘ π₁) ● pf
--      ≡⟨  (assocApply (sym α□)) ⟨●⟩refl₂ ⟩
--          (δ ⊗ₘ id) ● ((id ⊗ₘ gf) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ π₁) ● pf
--      ∎) ⟩
--       MkLens (gf ● ε) ((δ ⊗ₘ id) ● ((id ⊗ₘ gf) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ π₁) ● pf)
--    ≡⟨ refl ⟩
--       MkLens gf pf ●ₗ MkLens ε π₁
--     ∎))
