{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Data.Product
--open import IO
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian
open import Lens.Lens using (Lens)
import Lens.LensAssociativity
open import CategoryOfCategories

module Lens.LensCategory
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

open Cat using (_[_,_])
open _Functor_
import Shapes
open Shapes.CommutativeSquare
open import Isomorphism
open import MonoidalNaturalTransformation
open Cat cat
open Monoidal.Monoidal mc
open SymmetricMonoidal.SymmetricMonoidal smc
open CD-Category.CD-Category cd
open CDAffine-Category.CDAffine-Category cda
open Cartesian.Cartesian cart
open Lens.Lens cart
open Lens.LensAssociativity cart using (lensAssoc)

lensLeftId : {a b : obj × obj} {f : a lensHom b}
  → f ●ₗ lensId ≡ f
lensLeftId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens left-id
   (_ ● put
   ≡⟨
       (
          (δₘ ⊗ₘ id) ● ((id ⊗ₘ get) ⊗ₘ id) ● αₘ ● (id ⊗ₘ (π₂ ● id))
       ≡⟨  refl⟨●⟩ (refl⟨⊗⟩ left-id) ⟩
          (δₘ ⊗ₘ id) ● ((id ⊗ₘ get) ⊗ₘ id) ●  αₘ ● (id ⊗ₘ π₂)
       ≡⟨ ((assocApply α□) ⟨●⟩refl) ∙ assoc ⟩
          (δₘ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (get ⊗ₘ id)) ● (id ⊗ₘ π₂))
       ≡⟨ (refl⟨●⟩ sym distribute⊗) ⟩
          (δₘ ⊗ₘ id) ● αₘ ● (     (id ● id) ⊗ₘ ((get ⊗ₘ id) ● π₂)    )
       ≡⟨ refl⟨●⟩ ( left-id ⟨⊗⟩ (π₂law ∙ left-id)) ⟩
           (δₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ π₂)
       ≡⟨   copyαπ₂≡id   ⟩
           id
       ∎)
         ⟨●⟩refl   ⟩
       id ● put
   ≡⟨  right-id   ⟩
       put
   ∎)


lensRightId : {a b : obj × obj} {f : a lensHom b}
  → lensId ●ₗ f ≡ f
lensRightId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens right-id
  (
      (δₘ ⊗ₘ id) ● ((id ⊗ₘ id) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put) ● (π₂ ● id)
  ≡⟨  refl⟨●⟩ left-id ⟩
      (δₘ ⊗ₘ id) ● ((id ⊗ₘ id) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put) ● π₂
  ≡⟨  assoc  ⟩
      ((δₘ ⊗ₘ id) ● ((id ⊗ₘ id) ⊗ₘ id) ● αₘ) ● ((id ⊗ₘ put) ● π₂)
  ≡⟨   ((refl⟨●⟩ ((idLaw ⊗) ⟨⊗⟩refl) ∙ (idLaw ⊗)) ⟨●⟩refl) ⟨●⟩ π₂law   ⟩
      ((δₘ ⊗ₘ id) ● id ● αₘ) ● (π₂ ● put)
  ≡⟨  (assoc ∙ (refl⟨●⟩ right-id) ⟨●⟩refl) ∙ (sym assoc) ⟩
      (δₘ ⊗ₘ id) ● αₘ ● π₂ ● put
  ≡⟨  assoc ⟨●⟩refl  ⟩
      (δₘ ⊗ₘ id) ● (αₘ ● π₂) ● put
  ≡⟨  (refl⟨●⟩ α●π₂≡π₂⊗id) ⟨●⟩refl  ⟩
      (δₘ ⊗ₘ id) ● (π₂ ⊗ₘ id) ● put
  ≡⟨  sym distribute⊗ ⟨●⟩refl  ⟩
      (δₘ ● π₂) ⊗ₘ (id ● id) ● put
  ≡⟨  ((δₘ●π₂≡id) ⟨⊗⟩ left-id) ⟨●⟩refl  ⟩
      (id ⊗ₘ id) ● put
  ≡⟨  idLaw ⊗ ⟨●⟩refl  ⟩
      id ● put
  ≡⟨  right-id  ⟩
      put
  ∎)

-- agda questions: can I "pattern match on equality of a product-like thing"?
-- can I tell agda to display goals in a certain form? - SPC-u?
-- is there any way to improve my agda writing process, i.e. fill in boilerplate parts of the code? begin ≡⟨ ⟩ ∎
-- get type under cursor?
-- can I get rid of this import boilerplate at top of every file?
●ₗ-resp-≡ : {a b c : obj × obj} {f g : a lensHom b} {h i : b lensHom c}
  → f ≡ g → h ≡ i → (f ●ₗ h) ≡ (g ●ₗ i)
●ₗ-resp-≡ {f = (MkLens getf putf)} {g = (MkLens getg putg)} {h = (MkLens geth puth)} {i = (MkLens geti puti)} l r
  = cong₂ MkLens (cong Lens.get l ⟨●⟩ cong Lens.get r)
  (
    (δₘ ⊗ₘ id) ● ((id ⊗ₘ getf) ⊗ₘ id) ● αₘ ● (id ⊗ₘ puth) ● putf
  ≡⟨   (((refl⟨●⟩ ((refl⟨⊗⟩ (cong Lens.get l)) ⟨⊗⟩refl)) ⟨●⟩refl) ⟨●⟩ (refl⟨⊗⟩ (cong Lens.put r))) ⟨●⟩ (cong Lens.put l)   ⟩
    (δₘ ⊗ₘ id) ● ((id ⊗ₘ getg) ⊗ₘ id) ● αₘ ● (id ⊗ₘ puti) ● putg
  ∎)


lensCategory : Cat n m
lensCategory = MkCat
  (obj × obj)
  _lensHom_
  lensId
  _●ₗ_
  lensLeftId
  lensRightId
  lensAssoc
  ●ₗ-resp-≡


-- Notion of computation, given two morphisms X -> Y and R -> S we can think of them as lenses
proLens : ((cat ᵒᵖᶜ) X cat) Functor lensCategory
proLens = swapFunctor ●F MkFunctor
  id'
  (uncurry ◿_||_◺)
  refl
  λ (fₗ , fᵣ) (gₗ , gᵣ) → cong₂ MkLens refl (
           π₂ ● (gᵣ ● fᵣ)
      ≡⟨   sym assoc   ⟩
           (π₂ ● gᵣ) ● fᵣ
      ≡⟨   (sym π₂law ⟨●⟩refl) ∙ assoc ⟩
            (id ⊗ₘ gᵣ) ● (π₂ ● fᵣ)
      ≡⟨   (
                (id ⊗ₘ gᵣ)
            ≡⟨  sym right-id   ⟩
                id ● (id ⊗ₘ gᵣ)
            ≡⟨  sym copyαπ₂≡id ⟨●⟩refl   ⟩
                (δₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ π₂) ● (id ⊗ₘ gᵣ)
            ≡⟨  assoc ∙ (refl⟨●⟩ sym distribute⊗)    ⟩
                (δₘ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ (π₂ ● gᵣ))
            ≡⟨  refl⟨●⟩ (refl⟨⊗⟩ (((sym left-id) ∙ (sym π₂law) )⟨●⟩refl))   ⟩
                (δₘ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ((fₗ ⊗ₘ id) ● π₂ ● gᵣ))
            ≡⟨  refl⟨●⟩ (refl⟨⊗⟩ assoc)   ⟩
                (δₘ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ((fₗ ⊗ₘ id) ● (π₂ ● gᵣ)))
            ≡⟨  refl⟨●⟩ distribute⊗   ⟩
                (δₘ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (fₗ ⊗ₘ id)) ● (id ⊗ₘ (π₂ ● gᵣ)))
            ≡⟨  sym assoc   ⟩
                (δₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (fₗ ⊗ₘ id)) ● (id ⊗ₘ (π₂ ● gᵣ))
            ≡⟨  assocApply (sym α□) ⟨●⟩refl   ⟩
                (δₘ ⊗ₘ id) ● ((id ⊗ₘ fₗ) ⊗ₘ id) ● αₘ ● (id ⊗ₘ (π₂ ● gᵣ))
            ∎) ⟨●⟩refl   ⟩
           (δₘ ⊗ₘ id) ● ((id ⊗ₘ fₗ) ⊗ₘ id) ● αₘ ● (id ⊗ₘ (π₂ ● gᵣ)) ● (π₂ ● fᵣ)
      ∎)
