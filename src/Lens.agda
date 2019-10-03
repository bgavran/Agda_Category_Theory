{-# OPTIONS --allow-unsolved-metas #-}

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
open import Comonoid

module Lens
  {n m }
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  (cart : Cartesian smc) where

private
  variable
    n' m' n'' m'' : Level
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cart = Comonoid.Cartesian cart

open _Functor_
open _NatTrans_
open Cat.CommutativeSquare
open import Isomorphism
open cct
open mc
open smc
open cart



-- TODO just get's should be morphisms in cart,not puts also?
-- for this I need the notion of a subcategory
record Lens (s t a b : obj) : (Set m) where
  constructor MkLens

  field
    get :    s      hom a
    put : (s ⊗ₒ b) hom t

_lensHom_ : (obj × obj) → (obj × obj) → Set m
_lensHom_ (s , t) (a , b) = Lens s t a b

lensId : {a : obj × obj} → a lensHom a
lensId = MkLens id π₂


-- ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₂) ● put₁)
_●ₗ_ : {a b c : obj × obj}
  → a lensHom b
  →           b lensHom c
  → a      lensHom      c
_●ₗ_ {a = (a , a')} {b = (b , b')} {c = (c , c')}
  (MkLens get₁ put₁) (MkLens get₂ put₂)
  = MkLens
    (get₁ ● get₂)
    (                  begin→⟨     a      ⊗ₒ c'    ⟩
        δ ⊗ₘ id            →⟨ (a ⊗ₒ a) ⊗ₒ c'    ⟩
      (id ⊗ₘ get₁) ⊗ₘ id  →⟨ (a ⊗ₒ b) ⊗ₒ c'    ⟩
         αₘ                 →⟨  a ⊗ₒ (b ⊗ₒ c')   ⟩
       id ⊗ₘ put₂          →⟨  a ⊗ₒ     b'       ⟩
       put₁                 →⟨  a'                 ⟩end )

lensLeftId : {a b : obj × obj} {f : a lensHom b}
  → f ●ₗ lensId ≡ f
lensLeftId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens left-id
   (begin
       _ ● put
   ≡⟨
       (begin
          (δ ⊗ₘ id) ● ((id ⊗ₘ get) ⊗ₘ id) ●  αₘ ● _
       ≡⟨   (assocApply α□) ⟨●⟩refl ⟩
          ((δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (get ⊗ₘ id))) ● _
       ≡⟨   assoc  ⟩
          (δ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (get ⊗ₘ id)) ● (id ⊗ₘ π₂))
       ≡⟨   (refl⟨●⟩ sym distribute⊗) ⟩
          (δ ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ( (get ⊗ₘ id) ● π₂))
       ≡⟨  refl⟨●⟩ ( ⊗-resp-≡ left-id π₂law ) ⟩
          (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ π₂)
       ≡⟨   copyαπ₂≡id   ⟩
          id
       ∎ )

        ⟨●⟩refl   ⟩
       id ● put
   ≡⟨  right-id   ⟩
       put
   ∎)




lensAssoc : {a b c d : obj × obj}
  {f : a lensHom b}
  {g :           b lensHom c}
  {h :                     c lensHom d}
  → ((f ●ₗ g) ●ₗ h) ≡ (f ●ₗ (g ●ₗ h))
lensAssoc {f = (MkLens get₁ put₁)} {g = (MkLens get₂ put₂)} {h = (MkLens get₃ put₃)} = cong₂ MkLens assoc
  (begin
       ((δ ⊗ₘ id) ● (id ⊗ₘ (get₁ ● get₂) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put₃)) ● (((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₂)) ● put₁)
   ≡⟨  sym assoc  ⟩
       _ ● put₁
   ≡⟨
        (begin -- TODO already here can start factoring out the bottom wire?
          ((δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put₃)) ● ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₂))
         ≡⟨ sym assoc  ⟩
            _ ● (id ⊗ₘ put₂)
         ≡⟨ (begin
               ((δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put₃)) ● ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ)
             ≡⟨  assoc  ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (id ⊗ₘ put₃) ● ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ)  )
             ≡⟨   refl⟨●⟩ trans (sym assoc) (sym assoc ⟨●⟩refl)   ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((id ⊗ₘ put₃) ● (δ ⊗ₘ id)) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ  )
             ≡⟨   refl⟨●⟩ (⇆ ⟨●⟩refl₂)   ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((δ ⊗ₘ id) ● (id ⊗ₘ put₃)) ● ((id ⊗ₘ get₁) ⊗ₘ id ) ● αₘ  )
             ≡⟨   refl⟨●⟩ (assoc ⟨●⟩refl)   ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (δ ⊗ₘ id) ● ((id ⊗ₘ put₃) ● ((id ⊗ₘ get₁) ⊗ₘ id )) ● αₘ  )
             ≡⟨   refl⟨●⟩ ((refl⟨●⟩ ⇆) ⟨●⟩refl)   ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (δ ⊗ₘ id) ● (((id ⊗ₘ get₁) ⊗ₘ id) ● (id ⊗ₘ put₃)) ● αₘ  )
             ≡⟨  refl⟨●⟩ ( (refl⟨●⟩ (refl⟨●⟩ ⊗-resp-≡ₗ (sym (idLaw ⊗)))) ⟨●⟩refl) ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  (δ ⊗ₘ id) ● (((id ⊗ₘ get₁) ⊗ₘ id) ● ((id ⊗ₘ id) ⊗ₘ put₃)) ● αₘ  )
             ≡⟨  refl⟨●⟩ (sym assoc ⟨●⟩refl) ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● ((id ⊗ₘ id) ⊗ₘ put₃) ● αₘ  )
             ≡⟨  refl⟨●⟩ (trans assoc (refl⟨●⟩ α□)) ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (  ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● (αₘ ● (id ⊗ₘ (id ⊗ₘ put₃)))  )
             ≡⟨  trans (refl⟨●⟩ (sym assoc)) (sym assoc) ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ) ● (id ⊗ₘ (id ⊗ₘ put₃))
             ≡⟨ (begin
                   (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ)
                ≡⟨  sym assoc ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● αₘ
                ≡⟨  (refl⟨●⟩ (⊗-resp-≡ᵣ (sym (idLaw ⊗)) ⟨●⟩ (⊗-resp-≡ᵣ ((sym (idLaw ⊗)))))) ⟨●⟩refl ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● ((δ ⊗ₘ (id ⊗ₘ id)) ● ((id ⊗ₘ get₁) ⊗ₘ (id ⊗ₘ id))) ● αₘ
                ≡⟨  (sym assoc) ⟨●⟩refl ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● αₘ ● (δ ⊗ₘ (id ⊗ₘ id)) ● ((id ⊗ₘ get₁) ⊗ₘ (id ⊗ₘ id)) ● αₘ
                ≡⟨  (assocApply (sym α□) ) ⟨●⟩refl₂ ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● ((δ ⊗ₘ id) ⊗ₘ id) ● αₘ ● ((id ⊗ₘ get₁) ⊗ₘ (id ⊗ₘ id)) ● αₘ
                ≡⟨  (assocApply (sym α□) ) ⟨●⟩refl ⟩
                   ((δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● ((δ ⊗ₘ id) ⊗ₘ id) ● (((id ⊗ₘ get₁) ⊗ₘ id) ⊗ₘ id)) ● αₘ ● αₘ
                ≡⟨  assoc  ⟩
                   ((δ ⊗ₘ id) ● ((id ⊗ₘ (get₁ ● get₂)) ⊗ₘ id) ● ((δ ⊗ₘ id) ⊗ₘ id) ● (((id ⊗ₘ get₁) ⊗ₘ id) ⊗ₘ id)) ● (αₘ ● αₘ)
                ≡⟨ (factorId₄) ⟨●⟩ ⬠-identity   ⟩
                   ( (δ ● (id ⊗ₘ (get₁ ● get₂)) ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id))      ⊗ₘ id)  ● ((αₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ αₘ))
                ≡⟨   trans (sym assoc)  (sym assoc ⟨●⟩refl)  ⟩
                   ( (δ ● (id ⊗ₘ (get₁ ● get₂)) ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id))      ⊗ₘ id)  ● (αₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ αₘ)
                ≡⟨   factorId ⟨●⟩refl₂  ⟩
                   ( (δ ● (id ⊗ₘ (get₁ ● get₂)) ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ) ⊗ₘ id) ● αₘ ● (id ⊗ₘ αₘ)
                   -- now factoring our the identity wire on the bottom
                ≡⟨   ⊗-resp-≡ₗ (begin
                                    δ ● (id ⊗ₘ (get₁ ● get₂)) ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ
                                  ≡⟨  trans (assoc ⟨●⟩refl) assoc ⟨●⟩refl  ⟩
                                    δ ● ((id ⊗ₘ (get₁ ● get₂)) ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)) ● αₘ
                                  ≡⟨  (refl⟨●⟩ (begin
                                                  (id ⊗ₘ (get₁ ● get₂)) ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id)
                                               ≡⟨   sym distribute⊗₃   ⟩
                                                  (id ● δ ● (id ⊗ₘ get₁)) ⊗ₘ ((get₁ ● get₂) ● id ● id)
                                               ≡⟨   ⊗-resp-≡ (trans (right-id ⟨●⟩refl) (sym left-id)) (trans left-id left-id)   ⟩
                                                  (δ ● (id ⊗ₘ get₁) ● id) ⊗ₘ (get₁ ● get₂)
                                               ≡⟨   ⊗-resp-≡ (refl⟨●⟩ (sym (idLaw ⊗))) (trans (sym right-id) (sym assoc))   ⟩
                                                  (δ ● (id ⊗ₘ get₁) ● (id ⊗ₘ id)) ⊗ₘ (id ● get₁ ● get₂)
                                               ≡⟨   distribute⊗₃   ⟩
                                                  (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ get₁) ● ((id ⊗ₘ id) ⊗ₘ get₂)
                                               ∎)) ⟨●⟩refl  ⟩
                                    δ ● ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ get₁) ● ((id ⊗ₘ id) ⊗ₘ get₂)) ● αₘ
                                  ≡⟨  trans (sym assoc) ((sym assoc) ⟨●⟩refl) ⟨●⟩refl  ⟩
                                    δ ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ get₁) ● ((id ⊗ₘ id) ⊗ₘ get₂) ● αₘ
                                  ≡⟨  assocApply α□  ⟩
                                    δ ● (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ get₁) ● αₘ ● (id ⊗ₘ (id ⊗ₘ get₂))
                                  ≡⟨  assocApply α□ ⟨●⟩refl  ⟩
                                    δ ● (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (get₁ ⊗ₘ get₁)) ● (id ⊗ₘ (id ⊗ₘ get₂))
                                  ≡⟨  copyAssoc ⟨●⟩refl₂  ⟩
                                    (δ ● (id ⊗ₘ δ)) ● (id ⊗ₘ (get₁ ⊗ₘ get₁)) ● (id ⊗ₘ (id ⊗ₘ get₂))
                                 ≡⟨  assoc ⟨●⟩refl  ⟩
                                    δ ● ((id ⊗ₘ δ) ● (id ⊗ₘ (get₁ ⊗ₘ get₁))) ● (id ⊗ₘ (id ⊗ₘ get₂))
                                 ≡⟨  (refl⟨●⟩ (sym distribute⊗)) ⟨●⟩refl  ⟩
                                    δ ● ((id ● id) ⊗ₘ (δ ● (get₁ ⊗ₘ get₁))) ● (id ⊗ₘ (id ⊗ₘ get₂))
                                 ≡⟨  (refl⟨●⟩ (⊗-resp-≡ᵣ (sym copyApply))) ⟨●⟩refl  ⟩
                                    δ ● ((id ● id) ⊗ₘ (get₁ ● δ)) ● (id ⊗ₘ (id ⊗ₘ get₂))
                                 ≡⟨  (refl⟨●⟩ distribute⊗) ⟨●⟩refl  ⟩
                                    δ ● ((id ⊗ₘ get₁) ● (id ⊗ₘ δ)) ● (id ⊗ₘ (id ⊗ₘ get₂))
                                  ≡⟨  sym assoc ⟨●⟩refl  ⟩
                                    δ ● (id ⊗ₘ get₁) ● (id ⊗ₘ δ) ● (id ⊗ₘ (id ⊗ₘ get₂))
                                 ∎) ⟨●⟩refl₂   ⟩

                   ((δ ● (id ⊗ₘ get₁) ● (id ⊗ₘ δ) ● (id ⊗ₘ (id ⊗ₘ get₂))) ⊗ₘ id  ) ● αₘ ● (id ⊗ₘ αₘ)
                ≡⟨    sym factorId₄ ⟨●⟩refl₂   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● ((id ⊗ₘ δ) ⊗ₘ id) ● ((id ⊗ₘ (id ⊗ₘ get₂)) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ αₘ)
                ≡⟨     assocApply α□ ⟨●⟩refl   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● ((id ⊗ₘ δ) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((id ⊗ₘ get₂) ⊗ₘ id )) ● (id ⊗ₘ αₘ)
                ≡⟨     assocApply α□ ⟨●⟩refl₂   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ (δ ⊗ₘ id)) ● (id ⊗ₘ ((id ⊗ₘ get₂) ⊗ₘ id )) ● (id ⊗ₘ αₘ)
                ≡⟨     assoc ⟨●⟩refl   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (δ ⊗ₘ id)) ● (id ⊗ₘ ((id ⊗ₘ get₂) ⊗ₘ id ))) ● (id ⊗ₘ αₘ)
                ≡⟨     assoc   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (((id ⊗ₘ (δ ⊗ₘ id)) ● (id ⊗ₘ ((id ⊗ₘ get₂) ⊗ₘ id ))) ● (id ⊗ₘ αₘ))
                ≡⟨     refl⟨●⟩ (sym distribute⊗ ⟨●⟩refl)   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (((id ● id) ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ))) ● (id ⊗ₘ αₘ))
                ≡⟨     refl⟨●⟩ (⊗-resp-≡ₗ left-id ⟨●⟩refl)   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ))) ● (id ⊗ₘ αₘ))
                ≡⟨     refl⟨●⟩ sym distribute⊗   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ))
                ≡⟨     refl⟨●⟩ ⊗-resp-≡ₗ (left-id)   ⟩
                   (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ))
                ∎)


                   ⟨●⟩refl  ⟩
                ((δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ))) ● (id ⊗ₘ (id ⊗ₘ put₃))
             ≡⟨  assoc   ⟩
               (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ)) ● (id ⊗ₘ (id ⊗ₘ put₃)))
             ≡⟨   refl⟨●⟩ sym distribute⊗  ⟩
                (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ (((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ) ● (id ⊗ₘ put₃)))
             ≡⟨   refl⟨●⟩ ⊗-resp-≡ₗ (left-id)  ⟩
                (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃)))
             ∎)

         ⟨●⟩refl  ⟩
            (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃))) ● (id ⊗ₘ put₂)
         ≡⟨ assoc  ⟩
            (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃))) ● (id ⊗ₘ put₂))
         ≡⟨  refl⟨●⟩ sym distribute⊗   ⟩
            (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● ((id ● id) ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃) ● put₂))
         ≡⟨  refl⟨●⟩ ⊗-resp-≡ₗ left-id   ⟩
            (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃) ● put₂))
         ∎ )

   ⟨●⟩refl  ⟩
      (δ ⊗ₘ id) ● ((id ⊗ₘ get₁) ⊗ₘ id) ● αₘ ● (id ⊗ₘ ((δ ⊗ₘ id) ● ((id ⊗ₘ get₂) ⊗ₘ id ) ● αₘ ● (id ⊗ₘ put₃) ● put₂)) ● put₁
   ∎)
   -- we somehow automatically compute this with our brain

lensCategory : Cat n m
lensCategory = MkCat
  (obj × obj)
  _lensHom_
  (MkLens id π₂)
  _●ₗ_
  lensLeftId
  {!!}
  lensAssoc
  {!!}
