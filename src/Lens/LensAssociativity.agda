{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Function using (flip)
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

module Lens.LensAssociativity
    {n m}
    {cat : Cat n m}
    {mc : Monoidal cat}
    {smc : SymmetricMonoidal mc}
    {cd : CD-Category smc}
    {cda : CDAffine-Category cd}
    (cart : Cartesian cda) where

private
  variable
    n' m' n'' m'' : Level
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cart = Cartesian.Cartesian cart
  module lens = Lens.Lens cart

open _Functor_
open _NatTrans_
import Shapes
open Shapes.CommutativeSquare
open import Isomorphism
open cct
open mc
open smc
open cd
open cart
open lens


-- total 129 lines
lensAssoc : {a b c d : obj × obj}
  {f : a lensHom b}
  {g :           b lensHom c}
  {h :                     c lensHom d}
  → ((f ●ₗ g) ●ₗ h) ≡ (f ●ₗ (g ●ₗ h))
lensAssoc {f = (MkLens get₁ put₁)} {g = (MkLens get₂ put₂)} {h = (MkLens get₃ put₃)} = cong₂ MkLens assoc ? -- λ i → MkLens {!!} {!!} -- cong₂ MkLens assoc
   -- (
   --      ((δₘ ⊗ₘ id) ● (id ⊗ₘ (get₁ ● get₂) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put₃)) ● (((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₂)) ● put₁)
   --  ≡⟨  sym assoc  ⟩
   --      _ ● put₁
   --  ≡⟨
   --       (-- TODO already here can start factoring out the bottom wire?
   --         ((δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put₃)) ● ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₂))
   --        ≡⟨ sym assoc  ⟩
   --           _ ● (id ⊗ₘ put₂)
   --        ≡⟨ (
   --              ((δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put₃)) ● ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ)
   --            ≡⟨  assoc  ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (id ⊗ₘ put₃) ● ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ)  )
   --            ≡⟨   refl⟨●⟩ (sym assoc) ∙ (sym assoc ⟨●⟩refl)   ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((id ⊗ₘ put₃) ● (δₘ ⊗ₘ id)) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ  )
   --            ≡⟨   refl⟨●⟩ (⇆ ⟨●⟩refl₂)   ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((δₘ ⊗ₘ id) ● (id ⊗ₘ put₃)) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ  )
   --            ≡⟨   refl⟨●⟩ (assoc ⟨●⟩refl)   ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (δₘ ⊗ₘ id) ● ((id ⊗ₘ put₃) ● ((id ⊗ₘ get₁) ⊗ₘ id )) ● αₘ  )
   --            ≡⟨   refl⟨●⟩ ((refl⟨●⟩ ⇆) ⟨●⟩refl)   ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (δₘ ⊗ₘ id) ● (((id ⊗ₘ get₁) ⊗ₘ id) ● (id ⊗ₘ put₃)) ● αₘ  )
   --            ≡⟨  refl⟨●⟩ ( (refl⟨●⟩ (refl⟨●⟩ ((sym (idLaw ⊗)) ⟨⊗⟩refl) )) ⟨●⟩refl) ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (δₘ ⊗ₘ id) ● (((id ⊗ₘ get₁) ⊗ₘ id) ● ((id ⊗ₘ id) ⊗ₘ put₃)) ● αₘ  )
   --            ≡⟨  refl⟨●⟩ (sym assoc ⟨●⟩refl) ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● ((id ⊗ₘ id) ⊗ₘ put₃) ● αₘ  )
   --            ≡⟨  refl⟨●⟩ (assoc ∙ (refl⟨●⟩ α□)) ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● (αₘ ● (id ⊗ₘ (id ⊗ₘ put₃)))  )
   --            ≡⟨  (refl⟨●⟩ (sym assoc)) ∙ (sym assoc) ⟩
   --              (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ) ● (id ⊗ₘ (id ⊗ₘ put₃))
   --            ≡⟨ (
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ)
   --               ≡⟨  sym assoc ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● αₘ
   --               ≡⟨  (refl⟨●⟩ ((refl⟨⊗⟩ (sym (idLaw ⊗))) ⟨●⟩ (refl⟨⊗⟩ ((sym (idLaw ⊗)))))) ⟨●⟩refl ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δₘ ⊗ₘ (id ⊗ₘ id)) ● ((id ⊗ₘ get₁) ⊗ₘ (id ⊗ₘ id))) ● αₘ
   --               ≡⟨  (sym assoc) ⟨●⟩refl ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (δₘ ⊗ₘ (id ⊗ₘ id)) ● ((id ⊗ₘ get₁) ⊗ₘ (id ⊗ₘ id)) ● αₘ
   --               ≡⟨  (assocApply (sym α□) ) ⟨●⟩refl₂ ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● ((δₘ ⊗ₘ id) ⊗ₘ id) ● αₘ ● ((id ⊗ₘ get₁) ⊗ₘ (id ⊗ₘ id)) ● αₘ
   --               ≡⟨  (assocApply (sym α□) ) ⟨●⟩refl ⟩
   --                  ((δₘ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● ((δₘ ⊗ₘ id) ⊗ₘ id) ● (((id ⊗ₘ get₁) ⊗ₘ id) ⊗ₘ id)) ● αₘ ● αₘ
   --               ≡⟨  assoc ∙ ((factorId₄) ⟨●⟩ ⬠-identity) ⟩
   --                  ( (δₘ ● (id ⊗ₘ (get₁ ● get₂)) ● (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id))      ⊗ₘ id)  ● ((αₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ αₘ))
   --               ≡⟨   (sym assoc)  ∙ (sym assoc ⟨●⟩refl)  ⟩
   --                  ( (δₘ ● (id ⊗ₘ (get₁ ● get₂)) ● (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id))      ⊗ₘ id)  ● (αₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ αₘ)
   --               ≡⟨   factorId ⟨●⟩refl₂  ⟩
   --                  ( (δₘ ● (id ⊗ₘ (get₁ ● get₂)) ● (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ) ⊗ₘ id) ● αₘ ● (id ⊗ₘ αₘ)
   --                  -- now factoring our the identity wire on the bottom
   --                  -- This is the meat of this proof, using two facts: associativity of copy and the fact that get can slide through copy
   --                  -- everything before this was just so we can factor out the repeated parts
   --               ≡⟨             (
   --                                   δₘ ● (id ⊗ₘ (get₁ ● get₂)) ● (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ
   --                                 ≡⟨  (assoc ⟨●⟩refl) ∙ assoc ⟨●⟩refl  ⟩
   --                                   δₘ ● ((id ⊗ₘ (get₁ ● get₂)) ● (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● αₘ
   --                                 ≡⟨  (refl⟨●⟩ (
   --                                                 (id ⊗ₘ (get₁ ● get₂)) ● (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)
   --                                              ≡⟨   sym distribute⊗₃   ⟩
   --                                                 (id ● δₘ ● (id ⊗ₘ get₁)) ⊗ₘ ((get₁ ● get₂) ● id ● id)
   --                                              ≡⟨   ((right-id ⟨●⟩refl) ∙ (sym left-id)) ⟨⊗⟩ (left-id ∙ left-id)   ⟩
   --                                                 (δₘ ● (id ⊗ₘ get₁) ● id) ⊗ₘ (get₁ ● get₂)
   --                                              ≡⟨   (refl⟨●⟩ (sym (idLaw ⊗))) ⟨⊗⟩ ((sym right-id) ∙ (sym assoc))   ⟩
   --                                                 (δₘ ● (id ⊗ₘ get₁) ● (id ⊗ₘ id)) ⊗ₘ (id ● get₁ ● get₂)
   --                                              ≡⟨   distribute⊗₃   ⟩
   --                                                 (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ get₁) ● ((id ⊗ₘ id) ⊗ₘ get₂)
   --                                              ∎)) ⟨●⟩refl  ⟩
   --                                   δₘ ● ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ get₁) ● ((id ⊗ₘ id) ⊗ₘ get₂)) ● αₘ
   --                                 ≡⟨  (sym assoc) ∙ ((sym assoc) ⟨●⟩refl) ⟨●⟩refl  ⟩
   --                                   δₘ ● (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ get₁) ● ((id ⊗ₘ id) ⊗ₘ get₂) ● αₘ
   --                                 ≡⟨  (assocApply α□) ∙ (assocApply α□ ⟨●⟩refl)  ⟩
   --                                   δₘ ● (δₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (get₁ ⊗ₘ get₁)) ● (id ⊗ₘ (id ⊗ₘ get₂))
   --                                 ≡⟨  copyAssoc ⟨●⟩refl₂  ⟩
   --                                   (δₘ ● (id ⊗ₘ δₘ)) ● (id ⊗ₘ (get₁ ⊗ₘ get₁)) ● (id ⊗ₘ (id ⊗ₘ get₂))
   --                                ≡⟨  assoc ⟨●⟩refl  ⟩
   --                                   δₘ ● ((id ⊗ₘ δₘ) ● (id ⊗ₘ (get₁ ⊗ₘ get₁))) ● (id ⊗ₘ (id ⊗ₘ get₂))
   --                                ≡⟨  (refl⟨●⟩ (sym distribute⊗)) ⟨●⟩refl  ⟩
   --                                   δₘ ● ((id ● id) ⊗ₘ (δₘ ● (get₁ ⊗ₘ get₁))) ● (id ⊗ₘ (id ⊗ₘ get₂))
   --                                ≡⟨  (refl⟨●⟩ (refl⟨⊗⟩ (sym copyApply))) ⟨●⟩refl  ⟩
   --                                   δₘ ● ((id ● id) ⊗ₘ (get₁ ● δₘ)) ● (id ⊗ₘ (id ⊗ₘ get₂))
   --                                ≡⟨  (refl⟨●⟩ distribute⊗) ∙ (sym assoc) ⟨●⟩refl  ⟩
   --                                   δₘ ● (id ⊗ₘ get₁) ● (id ⊗ₘ δₘ) ● (id ⊗ₘ (id ⊗ₘ get₂))
   --                                ∎) ⟨⊗⟩refl ⟨●⟩refl₂   ⟩
   --                     -- this is the end of the meat of the proof
   --                  ((δₘ ● (id ⊗ₘ get₁) ● (id ⊗ₘ δₘ) ● (id ⊗ₘ (id ⊗ₘ get₂))) ⊗ₘ id  ) ● αₘ ● (id ⊗ₘ αₘ)
   --               ≡⟨    sym factorId₄ ⟨●⟩refl₂   ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● ((id ⊗ₘ δₘ) ⊗ₘ id) ● ((id ⊗ₘ (id ⊗ₘ get₂)) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ αₘ)
   --               ≡⟨     assocApply α□ ⟨●⟩refl   ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● ((id ⊗ₘ δₘ) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((id ⊗ₘ get₂) ⊗ₘ id )) ● (id ⊗ₘ αₘ)
   --               ≡⟨     assocApply α□ ⟨●⟩refl₂   ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ (δₘ ⊗ₘ id)) ● (id ⊗ₘ ((id ⊗ₘ get₂) ⊗ₘ id )) ● (id ⊗ₘ αₘ)
   --               ≡⟨     (assoc ⟨●⟩refl) ∙ assoc   ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (((id ⊗ₘ (δₘ ⊗ₘ id)) ● (id ⊗ₘ ((id ⊗ₘ get₂) ⊗ₘ id ))) ● (id ⊗ₘ αₘ))
   --               ≡⟨     refl⟨●⟩ ((sym distribute⊗) ∙ (left-id ⟨⊗⟩refl) ⟨●⟩refl)   ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ))) ● (id ⊗ₘ αₘ))
   --               ≡⟨     refl⟨●⟩ ((sym distribute⊗) ∙ (left-id ⟨⊗⟩refl))   ⟩
   --                  (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ))
   --               ∎)

   --                  ⟨●⟩refl  ⟩
   --               ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ))) ● (id ⊗ₘ (id ⊗ₘ put₃))
   --            ≡⟨  assoc ∙ (refl⟨●⟩ sym distribute⊗)  ⟩
   --               (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ (((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ) ● (id ⊗ₘ put₃)))
   --            ≡⟨   refl⟨●⟩ (left-id ⟨⊗⟩refl)  ⟩
   --               (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃)))
   --            ∎)

   --        ⟨●⟩refl  ⟩
   --           (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃))) ● (id ⊗ₘ put₂)
   --        ≡⟨ assoc ∙ (refl⟨●⟩ sym distribute⊗) ⟩
   --           (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃) ● put₂))
   --        ≡⟨  refl⟨●⟩ (left-id ⟨⊗⟩refl)  ⟩
   --           (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃) ● put₂))
   --        ∎ )

   --  ⟨●⟩refl  ⟩
   --     (δₘ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δₘ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃) ● put₂)) ● put₁
   --  ∎)
   -- it's remarkable that we somehow au
