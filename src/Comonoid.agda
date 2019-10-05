open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal

module Comonoid
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  (smc : SymmetricMonoidal mc)where

private
  variable
    n' m' n'' m'' : Level
  module C = Cat cat
  module M = Monoidal.Monoidal mc
  module S = SymmetricMonoidal.SymmetricMonoidal smc

open _Functor_
open C
open M
open S

record Cartesian : (Set (n ⊔ m)) where
  constructor MkComonoid

  field
    -- TODO these should actually be monoidal natural transformations?
    δ : {c : obj} → c hom (c ⊗ₒ c) -- multiplication
    ε : {c : obj} → c hom 𝟙         -- counit

    copySwap   : {c : obj} → (δ ● σₘ)
                           ≡ δ {c = c}
    copyDeleteλ : {c : obj} → δ {c = c} ● (ε ⊗ₘ id) ● λₘ
                           ≡ id
    copyAssoc  : {c : obj} → δ {c = c} ● (δ ⊗ₘ id) ● αₘ
                           ≡ δ {c = c} ● (id ⊗ₘ δ)
    deleteApply : {a b : obj} {f : a hom b} → ε ≡ f ● ε
    copyApply   : {a b : obj} {f : a hom b} → f ● δ ≡ δ ● (f ⊗ₘ f)

  copyDeleteρ : {c : obj} → δ {c = c} ● (id ⊗ₘ ε) ● ρₘ ≡ id
  copyDeleteρ =
    begin
       δ  ● (id ⊗ₘ ε) ● ρₘ
    ≡⟨  (sym copySwap ⟨●⟩refl) ⟨●⟩refl  ⟩
      (δ ● σₘ)  ● (id ⊗ₘ ε) ● ρₘ
    ≡⟨  assoc ⟨●⟩refl  ⟩
       δ ● (σₘ ● (id ⊗ₘ ε)) ● ρₘ
    ≡⟨  (refl⟨●⟩ sym σ□) ⟨●⟩refl  ⟩
       δ ● ((ε ⊗ₘ id) ● σₘ) ● ρₘ
    ≡⟨  assocApply assoc  ⟩
       δ ● (ε ⊗ₘ id) ● (σₘ ● ρₘ)
    ≡⟨  refl⟨●⟩ (sym λ≡σ●ρ)  ⟩
       δ ● (ε ⊗ₘ id) ● λₘ
    ≡⟨ copyDeleteλ  ⟩
        id
    ∎

  π₁ : {a b : obj} → (a ⊗ₒ b) hom a
  π₁ = (id ⊗ₘ ε) ● ρₘ

  π₂ : {a b : obj} → (a ⊗ₒ b) hom b
  π₂ = (ε ⊗ₘ id) ● λₘ

  π₂law : {a b c d : obj} {f : a hom b} {g : c hom d}
    → (f ⊗ₘ g) ● π₂ ≡ π₂ ● g
  π₂law {f = f} {g = g} =
    begin
      (f ⊗ₘ g) ● π₂
    ≡⟨⟩
      (f ⊗ₘ g) ● ((ε ⊗ₘ id) ● λₘ)
    ≡⟨ sym assoc ⟩
      (f ⊗ₘ g) ● (ε ⊗ₘ id) ● λₘ
    ≡⟨ sym distribute⊗ ⟨●⟩refl ⟩
      (f ● ε) ⊗ₘ (g ● id) ● λₘ
    ≡⟨ ⊗-resp-≡  (sym deleteApply) left-id ⟨●⟩refl ⟩
      (ε ⊗ₘ g) ● λₘ
    ≡⟨ ⊗-resp-≡ (sym left-id) (sym right-id) ⟨●⟩refl   ⟩
      ((ε ● id) ⊗ₘ  (id ● g)) ● λₘ
    ≡⟨ distribute⊗ ⟨●⟩refl   ⟩
      (ε ⊗ₘ id) ●  (id ⊗ₘ g) ● λₘ
    ≡⟨ trans assoc (refl⟨●⟩ λ□)  ⟩
      (ε ⊗ₘ id) ● (λₘ ● g)
    ≡⟨ sym assoc  ⟩
      (ε ⊗ₘ id) ● λₘ ● g
    ≡⟨⟩
       π₂ ● g
    ∎

  α●π₂≡π₂⊗id : {a b c : obj}
    → αₘ {a = a} {b = b} {c = c} ● π₂ ≡ π₂ ⊗ₘ id
  α●π₂≡π₂⊗id =
     begin
        αₘ ● π₂
     ≡⟨⟩
        αₘ ● ((ε ⊗ₘ id) ● λₘ)
     ≡⟨    sym assoc   ⟩
        αₘ ● (ε ⊗ₘ id) ● λₘ
     ≡⟨   (refl⟨●⟩ ⊗-resp-≡ᵣ (sym (idLaw ⊗))) ⟨●⟩refl   ⟩
        αₘ ● (ε ⊗ₘ (id ⊗ₘ id)) ● λₘ
     ≡⟨   sym α□ ⟨●⟩refl   ⟩
       ((ε ⊗ₘ id) ⊗ₘ id) ● αₘ ● λₘ
     ≡⟨   assoc   ⟩
       ((ε ⊗ₘ id) ⊗ₘ id) ● (αₘ ● λₘ)
     ≡⟨   refl⟨●⟩ sym λ⊗id≡α●λ  ⟩
       ((ε ⊗ₘ id) ⊗ₘ id) ● (λₘ ⊗ₘ id)
     ≡⟨   sym distribute⊗   ⟩
       ((ε ⊗ₘ id) ● λₘ) ⊗ₘ (id ● id)
     ≡⟨  ⊗-resp-≡ᵣ(left-id)  ⟩
       ((ε ⊗ₘ id) ● λₘ) ⊗ₘ id
     ≡⟨⟩
        π₂ ⊗ₘ id
     ∎

  σ●π₁≡π₂ : {a b : obj}
    → σₘ ● π₁ ≡ π₂ {a = a} {b = b}
  σ●π₁≡π₂ =
    begin
       σₘ ● ((id ⊗ₘ ε) ● ρₘ)
    ≡⟨  sym assoc  ⟩
       σₘ ● (id ⊗ₘ ε) ● ρₘ
    ≡⟨    (sym σ□) ⟨●⟩refl   ⟩
       (ε ⊗ₘ id) ● σₘ ● ρₘ
    ≡⟨    assoc   ⟩
       (ε ⊗ₘ id) ● (σₘ ● ρₘ)
    ≡⟨    refl⟨●⟩ (sym λ≡σ●ρ )   ⟩
       (ε ⊗ₘ id) ● λₘ
    ∎

  ▵-identityπ : {a b c : obj}
    → αₘ {a = a} {b = b} {c = c} ● (id ⊗ₘ π₂) ≡ π₁ ⊗ₘ id
  ▵-identityπ =
    begin
        αₘ ● (id ⊗ₘ π₂)
    ≡⟨⟩
        αₘ ● (    id    ⊗ₘ ((ε ⊗ₘ id) ● λₘ))
    ≡⟨   refl⟨●⟩ ⊗-resp-≡ₗ(sym left-id)   ⟩
        αₘ ● ((id ● id) ⊗ₘ ((ε ⊗ₘ id) ● λₘ))
    ≡⟨  refl⟨●⟩ distribute⊗  ⟩
        αₘ ● ((id ⊗ₘ (ε ⊗ₘ id)) ● (id ⊗ₘ λₘ))
    ≡⟨  sym assoc  ⟩
        (αₘ ● (id ⊗ₘ (ε ⊗ₘ id))) ● (id ⊗ₘ λₘ)
    ≡⟨      sym α□ ⟨●⟩refl     ⟩
        ((id ⊗ₘ ε) ⊗ₘ id) ● αₘ ● (id ⊗ₘ λₘ)
    ≡⟨  assoc ⟩
        ((id ⊗ₘ ε) ⊗ₘ id) ● (αₘ ● (id ⊗ₘ λₘ))
    ≡⟨  refl⟨●⟩ ▵-identity  ⟩
        ((id ⊗ₘ ε) ⊗ₘ id) ● (ρₘ ⊗ₘ id)
    ≡⟨  sym distribute⊗  ⟩
        ((id ⊗ₘ ε) ● ρₘ) ⊗ₘ (id ● id)
    ≡⟨  ⊗-resp-≡ᵣ left-id    ⟩
        π₁ ⊗ₘ id
    ∎

  copyαπ₂≡id : {a b : obj}
    → (δ {c = a} ⊗ₘ id {a = b}) ● αₘ ● (id ⊗ₘ π₂) ≡ id
  copyαπ₂≡id =
    begin
       (δ ⊗ₘ id) ● αₘ ● (id ⊗ₘ π₂)
    ≡⟨  assoc  ⟩
       (δ ⊗ₘ id) ● (αₘ ● (id ⊗ₘ π₂))
    ≡⟨  refl⟨●⟩ ▵-identityπ  ⟩
       (δ ⊗ₘ id) ● (π₁ ⊗ₘ id)
    ≡⟨⟩
       (δ ⊗ₘ id) ● (((id ⊗ₘ ε) ● ρₘ) ⊗ₘ id)
    ≡⟨  sym distribute⊗  ⟩
       (δ ● ((id ⊗ₘ ε) ● ρₘ)) ⊗ₘ (id ● id)
    ≡⟨  ⊗-resp-≡ (sym assoc) left-id  ⟩
       (δ ● (id ⊗ₘ ε) ● ρₘ) ⊗ₘ id
    ≡⟨  ⊗-resp-≡ₗ copyDeleteρ ⟩
         id ⊗ₘ id
    ≡⟨  idLaw ⊗    ⟩
        id
    ∎

  δ●π₂≡id : {c : obj}
    → δ {c = c} ● π₂ ≡ id
  δ●π₂≡id =
    begin
      δ ● π₂
    ≡⟨⟩
      δ ● ((ε ⊗ₘ id) ● λₘ)
    ≡⟨  sym assoc  ⟩
      δ ● (ε ⊗ₘ id) ● λₘ
    ≡⟨  copyDeleteλ  ⟩
       id
    ∎


  --strangeLaw : {a b : obj}
  --  → (δ {c = a} ⊗ₘ id {a = b}) ● αₘ ●  (id ⊗ₘ (ε ⊗ₘ id)) ● (id ⊗ₘ λₘ) ≡ id
  --strangeLaw {b = b} =
  --  begin
  --      (δ ⊗ₘ id) ● αₘ ●  (id ⊗ₘ (ε ⊗ₘ id)) ● (id ⊗ₘ λₘ)
  --  ≡⟨    (sym (assocApply (α□ {c = b})) ⟨●⟩refl)     ⟩
  --      (δ ⊗ₘ id) ● ((id ⊗ₘ ε) ⊗ₘ id) ● αₘ ● (id ⊗ₘ λₘ)
  --  ≡⟨    assoc  ⟩
  --      (δ ⊗ₘ id) ● ((id ⊗ₘ ε) ⊗ₘ id) ● (αₘ ● (id ⊗ₘ λₘ))
  --  ≡⟨    refl⟨●⟩ ▵-identity  ⟩
  --      (δ ⊗ₘ id) ● ((id ⊗ₘ ε) ⊗ₘ id) ● (ρₘ ⊗ₘ id)
  --  ≡⟨  sym distribute⊗₃   ⟩
  --      (δ ● (id ⊗ₘ ε) ● ρₘ) ⊗ₘ ((id ● id) ● id)
  --  ≡⟨  ⊗-resp-≡ copyDeleteρ left-id   ⟩
  --      id ⊗ₘ (id ● id)
  --  ≡⟨  ⊗-resp-≡ᵣ left-id   ⟩
  --      id ⊗ₘ id
  --  ≡⟨  idLaw ⊗   ⟩
  --     id
  --  ∎


-- Did I define this to be a category actually?
  -- TODO prove universal property of cartesian product?


{-
record ComonoidHom {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  {a b : obj cat}
  (c₁ : Comonoid smc a)
  (c₂ : Comonoid smc b)
  : Set m where
  constructor MkComonoidHom
  module C₁ = Comonoid c₁
  open C₁ renaming (ε to ε₁; δ to δ₁)
  module C₂ = Comonoid c₂
  open C₂ renaming (ε to ε₂; δ to δ₂)
  module mc = Monoidal.Monoidal mc
  open mc

  -- map between objects which preserves comonoid structure
  field
    f : cat [ a , b ]
    deleteApply : ε₁ ≡ cat [ ε₂ ∘ f ]
    copyApply : cat [ δ₂ ∘ f ] ≡ cat [ (f ⊗ₘ f) ∘ δ₁ ]


-- category of commutative comonoids
-- also a cartesian monoidal category?
comm : {cat : Cat n m} {mc : Monoidal cat} {smc : SymmetricMonoidal mc}
  → Cat n m
comm {cat = cat} {mc = mc} {smc = smc} = MkCat
  (let tt = Comonoid smc
       t = obj cat
       -- ttt = map tt t
   in {!!})
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

  {!!}


-}
