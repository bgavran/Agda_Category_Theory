open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
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

private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart
  module lenss = L cart
  module lc = LC cart
  module ls = Lens.SimpleLens cart
  module lensassoc = Lens.LensAssociativity cart

open _Functor_
open Cat.CommutativeSquare
open import Isomorphism
open cct
open mc
open smc
open cd
open cda
open cart
open lenss
open lc
open lensassoc using (lensAssoc)
open ls

record LawfulSimpleLens (a b : obj) : (Set m) where
  constructor MkLawfulSimpleLens
  field
    simpleLens : SimpleLens a b
  module simpleLens = SimpleLens simpleLens
  open simpleLens
  module lls = Lens lens
  open lls

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
   ≡⟨  trans (left-id ⟨●⟩refl)  δ●π₂≡id ⟩
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
  (Monoidal.𝟙 simpleLensMonoidal)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

lawfulSimpleLensCDAffineCategory : CDAffine-Category simpleLensCDCategory
lawfulSimpleLensCDAffineCategory = MkCDAffine (λ {a = a} {b = b} {f = f} →
  let MkSimpleLens (MkLens gf pf) = f
  in cong MkSimpleLens
  (begin
      MkLens ε π₁
   ≡⟨ cong₂ MkLens deleteApply (
     begin
          π₁
     ≡⟨  {!!} ⟩
         (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (π₁ ● gf)) ● pf
     ≡⟨  (refl⟨●⟩ (sym left-id ⟨⊗⟩ sym π₁law)) ⟨●⟩refl ⟩
         (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ((gf ⊗ₘ id) ● π₁)) ● pf
     ≡⟨  (refl⟨●⟩ distribute⊗) ⟨●⟩refl ⟩
         (δ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (gf ⊗ₘ id)) ● (id ⊗ₘ π₁)) ● pf
     ≡⟨  sym assoc ⟨●⟩refl ⟩
         (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (gf ⊗ₘ id)) ● (id ⊗ₘ π₁) ● pf
     ≡⟨  (assocApply (sym α□)) ⟨●⟩refl₂ ⟩
         (δ ⊗ₘ id) ● ((id ⊗ₘ gf) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ π₁) ● pf
     ∎) ⟩
      MkLens (gf ● ε) ((δ ⊗ₘ id) ● ((id ⊗ₘ gf) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ π₁) ● pf)
   ≡⟨ refl ⟩
      MkLens gf pf ●ₗ MkLens ε π₁
    ∎))
