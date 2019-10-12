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
open import Lens.Lens using (Lens)
import Lens.LensAssociativity

module Lens.LensCategory
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where

private
  module cct = Cat cat
  module mc = Monoidal.Monoidal mc
  module smc = SymmetricMonoidal.SymmetricMonoidal smc
  module cd = CD-Category.CD-Category cd
  module cda = CDAffine-Category.CDAffine-Category cda
  module cart = Cartesian.Cartesian cart
  module lens = Lens.Lens cart
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
open lens
open lensassoc using (lensAssoc)

lensId : {a : obj × obj} → a lensHom a
lensId = MkLens id π₂

lensLeftId : {a b : obj × obj} {f : a lensHom b}
  → f ●ₗ lensId ≡ f
lensLeftId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens left-id
   (begin
      _ ● put
   ≡⟨
       (begin
          (δ ⊗ₘ id) ● ((id ⊗ₘ get) ⊗ₘ id) ●  αₘ ● (id ⊗ₘ π₂)
       ≡⟨ trans ((assocApply α□) ⟨●⟩refl) assoc ⟩
          (δ ⊗ₘ id) ● αₘ ● ((id ⊗ₘ (get ⊗ₘ id)) ● (id ⊗ₘ π₂))
       ≡⟨ (refl⟨●⟩ sym distribute⊗) ⟩
          (δ ⊗ₘ id) ● αₘ ● (     (id ● id) ⊗ₘ ((get ⊗ₘ id) ● π₂)    )
       ≡⟨ refl⟨●⟩ ( left-id ⟨⊗⟩ (trans π₂law left-id)) ⟩
           (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ π₂)
       ≡⟨   copyαπ₂≡id   ⟩
          id
       ∎ )

        ⟨●⟩refl   ⟩
       id ● put
   ≡⟨  right-id   ⟩
       put
   ∎)


lensRightId : {a b : obj × obj} {f : a lensHom b}
  → lensId ●ₗ f ≡ f
lensRightId {a = (a , a')} {b = (b , b')} {MkLens get put} = cong₂ MkLens right-id
  (begin
       (δ ⊗ₘ id) ● ((id ⊗ₘ id) ⊗ₘ id) ● αₘ ● (id ⊗ₘ put) ● π₂
   ≡⟨  assoc  ⟩
       ((δ ⊗ₘ id) ● ((id ⊗ₘ id) ⊗ₘ id) ● αₘ) ● ((id ⊗ₘ put) ● π₂)
   ≡⟨   ((refl⟨●⟩ trans ((idLaw ⊗) ⟨⊗⟩refl) (idLaw ⊗)) ⟨●⟩refl) ⟨●⟩ π₂law   ⟩
       ((δ ⊗ₘ id) ● id ● αₘ) ● (π₂ ● put)
   ≡⟨  trans (trans assoc (refl⟨●⟩ right-id) ⟨●⟩refl) (sym assoc) ⟩
       (δ ⊗ₘ id) ● αₘ ● π₂ ● put
   ≡⟨  assoc ⟨●⟩refl  ⟩
       (δ ⊗ₘ id) ● (αₘ ● π₂) ● put
   ≡⟨  (refl⟨●⟩ α●π₂≡π₂⊗id) ⟨●⟩refl  ⟩
       (δ ⊗ₘ id) ● (π₂ ⊗ₘ id) ● put
   ≡⟨  sym distribute⊗ ⟨●⟩refl  ⟩
       (δ ● π₂) ⊗ₘ (id ● id) ● put
   ≡⟨  ((δ●π₂≡id) ⟨⊗⟩ left-id) ⟨●⟩refl  ⟩
       (id ⊗ₘ id) ● put
   ≡⟨  idLaw ⊗ ⟨●⟩refl  ⟩
       id ● put
   ≡⟨  right-id  ⟩
       put
   ∎)

-- agda questions: can I "pattern match on equality of a product-like thing"?
-- can I tell agda to display goals in a certain form?
-- is there any way to improve my agda writing process, i.e. fill in boilerplate parts of the code? begin ≡⟨ ⟩ ∎
-- get type under cursor?
●ₗ-resp-≡ : {a b c : obj × obj} {f g : a lensHom b} {h i : b lensHom c}
  → f ≡ g → h ≡ i → (f ●ₗ h) ≡ (g ●ₗ i)
●ₗ-resp-≡ {f = (MkLens getf putf)} {g = (MkLens getg putg)} {h = (MkLens geth puth)} {i = (MkLens geti puti)} l r
  = cong₂ MkLens (cong Lens.get l ⟨●⟩ cong Lens.get r)
  (begin
    (δ ⊗ₘ id) ● ((id ⊗ₘ getf) ⊗ₘ id) ● αₘ ● (id ⊗ₘ puth) ● putf
  ≡⟨   (((refl⟨●⟩ ((refl⟨⊗⟩ (cong Lens.get l)) ⟨⊗⟩refl)) ⟨●⟩refl) ⟨●⟩ (refl⟨⊗⟩ (cong Lens.put r))) ⟨●⟩ (cong Lens.put l)   ⟩
    (δ ⊗ₘ id) ● ((id ⊗ₘ getg) ⊗ₘ id) ● αₘ ● (id ⊗ₘ puti) ● putg
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

⊗ₗ : (lensCategory X lensCategory) Functor lensCategory
⊗ₗ = MkFunctor
  (λ x → let (a , c) = proj₁ x
             (e , g) = proj₂ x
         in a ⊗ₒ e , c ⊗ₒ g)
  (λ l → {!!})
  {!!}
  {!!}

lensMonoidal : Monoidal lensCategory
lensMonoidal = MkMonoidal
  ⊗ₗ
  (𝟙 , 𝟙)
  {!!}
  {!!}
  {!!}
