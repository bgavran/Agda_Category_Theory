{-# OPTIONS --allow-unsolved-metas #-}

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
open C
module LM = Monoidal.Monoidal mc
open LM
module S = SymmetricMonoidal.SymmetricMonoidal smc
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

  strangeLaw : {a b : obj}
    → (δ {c = a} ⊗ₘ id {a = b}) ● αₘ ●  (id ⊗ₘ (ε ⊗ₘ id)) ● (id ⊗ₘ λₘ) ≡ id
  strangeLaw {b = b} =
    begin
      (δ ⊗ₘ id) ● αₘ ●  (id ⊗ₘ (ε ⊗ₘ id)) ● (id ⊗ₘ λₘ)
    ≡⟨    (sym (assocApply (α□ {c = b})) ⟨●⟩refl)     ⟩
      (δ ⊗ₘ id) ● ((id ⊗ₘ ε) ⊗ₘ id) ● αₘ ● (id ⊗ₘ λₘ)
    ≡⟨    assoc  ⟩
      (δ ⊗ₘ id) ● ((id ⊗ₘ ε) ⊗ₘ id) ● (αₘ ● (id ⊗ₘ λₘ))
    ≡⟨    refl⟨●⟩ ▵-identity  ⟩
      (δ ⊗ₘ id) ● ((id ⊗ₘ ε) ⊗ₘ id) ● (ρₘ ⊗ₘ id)
    ≡⟨  sym distribute⊗₃   ⟩
      (δ ● (id ⊗ₘ ε) ● ρₘ) ⊗ₘ ((id ● id) ● id)
    ≡⟨  ⊗-resp-≡ {!!} left-id   ⟩
      (δ ● (id ⊗ₘ ε) ● ρₘ) ⊗ₘ (id ● id)
    ≡⟨  {!!}   ⟩
      id
    ∎


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
