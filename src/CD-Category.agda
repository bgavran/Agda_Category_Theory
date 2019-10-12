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

-- CD-category is defined in https://arxiv.org/abs/1709.00322 , Definition 2.2
-- CD stands for Copy/Discard
-- It is like a Cartesian category except the morphisms aren't natural w.r.t copy and delete
module CD-Category
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  (smc : SymmetricMonoidal mc) where

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

record CD-Category : (Set (n ⊔ m)) where
  constructor MkCD-Category

  field
    -- TODO these should actually be natural transformations?
    -- even stronger - monoidal natural transformations!
    -- this requires adding a notion of a monoidal functor
    δ : {c : obj} → c hom (c ⊗ₒ c) -- multiplication
    ε : {c : obj} → c hom 𝟙         -- counit

    copySwap   : {c : obj} → (δ ● σₘ)
                           ≡ δ {c = c}
    copyDeleteλ : {c : obj} → δ {c = c} ● (ε ⊗ₘ id) ● λₘ
                           ≡ id
    copyAssoc  : {c : obj} → δ {c = c} ● (δ ⊗ₘ id) ● αₘ
                           ≡ δ {c = c} ● (id ⊗ₘ δ)

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

  α●π₂≡π₂⊗id : {a b c : obj}
    → αₘ {a = a} {b = b} {c = c} ● π₂ ≡ π₂ ⊗ₘ id
  α●π₂≡π₂⊗id =
     begin
        αₘ ● π₂
     ≡⟨⟩
        αₘ ● ((ε ⊗ₘ id) ● λₘ)
     ≡⟨    sym assoc   ⟩
        αₘ ● (ε ⊗ₘ id) ● λₘ
     ≡⟨   (refl⟨●⟩ refl⟨⊗⟩ (sym (idLaw ⊗))) ⟨●⟩refl   ⟩
        αₘ ● (ε ⊗ₘ (id ⊗ₘ id)) ● λₘ
     ≡⟨   sym α□ ⟨●⟩refl   ⟩
       ((ε ⊗ₘ id) ⊗ₘ id) ● αₘ ● λₘ
     ≡⟨   assoc   ⟩
       ((ε ⊗ₘ id) ⊗ₘ id) ● (αₘ ● λₘ)
     ≡⟨   refl⟨●⟩ sym λ⊗id≡α●λ  ⟩
       ((ε ⊗ₘ id) ⊗ₘ id) ● (λₘ ⊗ₘ id)
     ≡⟨   sym distribute⊗   ⟩
       ((ε ⊗ₘ id) ● λₘ) ⊗ₘ (id ● id)
     ≡⟨  refl⟨⊗⟩ left-id  ⟩
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
    ≡⟨   refl⟨●⟩ ((sym left-id) ⟨⊗⟩refl)   ⟩
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
    ≡⟨  refl⟨⊗⟩  left-id    ⟩
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
    ≡⟨  (sym assoc) ⟨⊗⟩ left-id  ⟩
       (δ ● (id ⊗ₘ ε) ● ρₘ) ⊗ₘ id
    ≡⟨  copyDeleteρ ⟨⊗⟩refl ⟩
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
