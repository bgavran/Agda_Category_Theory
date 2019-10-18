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

-- CD-category is defined in https://arxiv.org/abs/1709.00322 , Definition 2.2
-- CD stands for Copy/Discard
-- It is like a Cartesian category except the morphisms aren't natural w.r.t copy and delete
module CD-Category
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  (smc : SymmetricMonoidal mc) where

open import MonoidalFunctor
open import MonoidalNaturalTransformation
private
  variable
    n' m' n'' m'' : Level
  module C = Cat cat
  module M = Monoidal.Monoidal mc
  module S = SymmetricMonoidal.SymmetricMonoidal smc

--open Cat using (_[_●_])
open _Functor_
open _NatTrans_
open _MonoidalFunctor_ hiding (ε)
open _MonoidalNatTrans_
open C
open M
open S

-- if we remove this then an implicit arugment annotation is needed for constFunctor everywhere
constFunctor𝟙 : cat Functor cat
constFunctor𝟙 = constFunctor 𝟙

constMonoidalFunctor𝟙 : mc MonoidalFunctor mc
constMonoidalFunctor𝟙 = MkMonoidalFunctor (constFunctor 𝟙) (MkNatTrans {!!} {!!}) id

monoidal⃤⊗ : mc MonoidalFunctor mc
monoidal⃤⊗ = MkMonoidalFunctor ⃤⊗ {!!} {!!}

record CD-Category : (Set (n ⊔ m)) where
  constructor MkCD-Category




  field
    δ : idFunctorMonoidal MonoidalNatTrans monoidal⃤⊗
    ε : idFunctorMonoidal MonoidalNatTrans constMonoidalFunctor𝟙

  δₘ : {c : obj} → c hom (c ⊗ₒ c) -- multiplication
  δₘ = η (θ δ)

  εₘ : {c : obj} → c hom 𝟙         -- counit
  εₘ = η (θ ε)

  δ□ : {a b : obj} {f : a hom b}
    → CommutativeSquare f δₘ δₘ (mapMor ⃤⊗ f)
  δ□ = naturality (θ δ)

  ε□ : {a b : obj} {f : a hom b}
    → CommutativeSquare f εₘ εₘ (mapMor (constFunctor𝟙) f)
  ε□ = naturality (θ ε)

  ε▵ : εₘ ≡ id {a = 𝟙}
  ε▵ = trans (sym right-id) (identityTriangle ε)

  field
    copySwap   : {c : obj} → (δₘ ● σₘ)
                           ≡ δₘ {c = c}
    copyDeleteλ : {c : obj} → δₘ {c = c} ● (εₘ ⊗ₘ id) ● λₘ
                           ≡ id
    copyAssoc  : {c : obj} → δₘ {c = c} ● (δₘ ⊗ₘ id) ● αₘ
                           ≡ δₘ {c = c} ● (id ⊗ₘ δₘ)

  copyDeleteρ : {c : obj} → δₘ {c = c} ● (id ⊗ₘ εₘ) ● ρₘ ≡ id
  copyDeleteρ =
    begin
       δₘ  ● (id ⊗ₘ εₘ) ● ρₘ
    ≡⟨  (sym copySwap ⟨●⟩refl) ⟨●⟩refl  ⟩
      (δₘ ● σₘ)  ● (id ⊗ₘ εₘ) ● ρₘ
    ≡⟨  assoc ⟨●⟩refl  ⟩
       δₘ ● (σₘ ● (id ⊗ₘ εₘ)) ● ρₘ
    ≡⟨  (refl⟨●⟩ sym σ□) ⟨●⟩refl  ⟩
       δₘ ● ((εₘ ⊗ₘ id) ● σₘ) ● ρₘ
    ≡⟨  assocApply assoc  ⟩
       δₘ ● (εₘ ⊗ₘ id) ● (σₘ ● ρₘ)
    ≡⟨  refl⟨●⟩ (sym λ≡σ●ρ)  ⟩
       δₘ ● (εₘ ⊗ₘ id) ● λₘ
    ≡⟨ copyDeleteλ  ⟩
        id
    ∎

  π₁ : {a b : obj} → (a ⊗ₒ b) hom a
  π₁ = (id ⊗ₘ εₘ) ● ρₘ

  π₂ : {a b : obj} → (a ⊗ₒ b) hom b
  π₂ = (εₘ ⊗ₘ id) ● λₘ


  swapProject≡project : {a b c d : obj}
    → |⇆|⊗ {a = a} {b = b} {c = c} {d = d} ● ((π₂ ● id) ⊗ₘ (π₂ ● id)) ≡ π₂
  swapProject≡project {a = a} {b = b} {c = c} {d = d}=
    begin
      |⇆|⊗ ● ((π₂ ● id) ⊗ₘ (π₂ ● id))
    ≡⟨   refl⟨●⟩ (left-id ⟨⊗⟩ left-id)  ⟩
      |⇆|⊗ ● (π₂ ⊗ₘ π₂)
    ≡⟨⟩
       αₘ ● (id ⊗ₘ αₘ' ) ● (id ⊗ₘ (σₘ ⊗ₘ id)) ● (id ⊗ₘ αₘ) ● αₘ' ● (((εₘ ⊗ₘ id) ● λₘ) ⊗ₘ ((εₘ ⊗ₘ id) ● λₘ))
    ≡⟨  refl⟨●⟩ distribute⊗ ⟩
       αₘ ● (id ⊗ₘ αₘ' ) ● (id ⊗ₘ (σₘ ⊗ₘ id)) ● (id ⊗ₘ αₘ) ● αₘ' ● (((εₘ ⊗ₘ id) ⊗ₘ (εₘ ⊗ₘ id)) ● (λₘ ⊗ₘ λₘ))
    ≡⟨  trans (sym assoc) (assoc ⟨●⟩refl)⟩
       αₘ ● (id ⊗ₘ αₘ' ) ● (id ⊗ₘ (σₘ ⊗ₘ id)) ● (id ⊗ₘ αₘ) ● (αₘ' ● ((εₘ ⊗ₘ id) ⊗ₘ (εₘ ⊗ₘ id))) ● (λₘ ⊗ₘ λₘ)
    ≡⟨  (trans (refl⟨●⟩ sym α□') (sym assoc)) ⟨●⟩refl ⟩
       αₘ ● (id ⊗ₘ αₘ' ) ● (id ⊗ₘ (σₘ ⊗ₘ id)) ● (id ⊗ₘ αₘ) ● (εₘ ⊗ₘ (id ⊗ₘ (εₘ ⊗ₘ id))) ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  assoc₃ ⟨●⟩refl₂ ⟩
       αₘ ● ((id ⊗ₘ αₘ' ) ● ((id ⊗ₘ (σₘ ⊗ₘ id)) ● ((id ⊗ₘ αₘ) ● ((εₘ ⊗ₘ (id ⊗ₘ (εₘ ⊗ₘ id))) )))) ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  (refl⟨●⟩ sym assoc₂) ⟨●⟩refl₂ ⟩
       αₘ ● ((id ⊗ₘ αₘ' ) ● (id ⊗ₘ (σₘ ⊗ₘ id)) ● (id ⊗ₘ αₘ) ● ((εₘ ⊗ₘ (id ⊗ₘ (εₘ ⊗ₘ id))))) ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  (refl⟨●⟩ sym distribute⊗₄) ⟨●⟩refl₂ ⟩
       αₘ ● ((id ● id ● id ● εₘ) ⊗ₘ (αₘ' ● (σₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ (εₘ ⊗ₘ id))))              ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  (refl⟨●⟩ (((trans (left-id ⟨●⟩refl) left-id) ⟨●⟩refl) ⟨⊗⟩ assocApply (sym α□))) ⟨●⟩refl₂ ⟩
       αₘ ● ((id ● εₘ)           ⊗ₘ (αₘ' ● (σₘ ⊗ₘ id) ● ((id ⊗ₘ εₘ) ⊗ₘ id) ● αₘ  ))              ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  (refl⟨●⟩ (right-id ⟨⊗⟩ (assoc ⟨●⟩refl))) ⟨●⟩refl₂ ⟩
       αₘ ● (εₘ           ⊗ₘ (αₘ' ● ((σₘ ⊗ₘ id) ● ((id ⊗ₘ εₘ) ⊗ₘ id)) ● αₘ  ))              ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  (refl⟨●⟩ (refl⟨⊗⟩ ((refl⟨●⟩ sym distribute⊗) ⟨●⟩refl))) ⟨●⟩refl₂ ⟩
       αₘ ● (εₘ ⊗ₘ (αₘ' ● ((σₘ ● (id ⊗ₘ εₘ)) ⊗ₘ (id ● id)) ● αₘ  )) ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  (refl⟨●⟩ (refl⟨⊗⟩ ((refl⟨●⟩ (sym σ□ ⟨⊗⟩refl) ) ⟨●⟩refl))) ⟨●⟩refl₂ ⟩
       αₘ ● (εₘ ⊗ₘ (αₘ' ● (((εₘ ⊗ₘ id) ● σₘ) ⊗ₘ (id ● id)) ● αₘ  )) ● αₘ' ● (λₘ ⊗ₘ λₘ)
    ≡⟨  {!!} ⟩
      αₘ' ●  αₘ ⊗ₘ id ● ((εₘ ⊗ₘ (εₘ ⊗ₘ id)) ⊗ₘ id) ● ((id ⊗ₘ λₘ) ⊗ₘ id) ● λₘ ⊗ₘ id
    ≡⟨  {!!}  ⟩
      (εₘ ⊗ₘ id) ● λₘ
    ∎

  α●π₂≡π₂⊗id : {a b c : obj}
    → αₘ {a = a} {b = b} {c = c} ● π₂ ≡ π₂ ⊗ₘ id
  α●π₂≡π₂⊗id =
     begin
        αₘ ● π₂
     ≡⟨⟩
        αₘ ● ((εₘ ⊗ₘ id) ● λₘ)
     ≡⟨    sym assoc   ⟩
        αₘ ● (εₘ ⊗ₘ id) ● λₘ
     ≡⟨   (refl⟨●⟩ refl⟨⊗⟩ (sym (idLaw ⊗))) ⟨●⟩refl   ⟩
        αₘ ● (εₘ ⊗ₘ (id ⊗ₘ id)) ● λₘ
     ≡⟨   sym α□ ⟨●⟩refl   ⟩
       ((εₘ ⊗ₘ id) ⊗ₘ id) ● αₘ ● λₘ
     ≡⟨   assoc   ⟩
       ((εₘ ⊗ₘ id) ⊗ₘ id) ● (αₘ ● λₘ)
     ≡⟨   refl⟨●⟩ sym λ⊗id≡α●λ  ⟩
       ((εₘ ⊗ₘ id) ⊗ₘ id) ● (λₘ ⊗ₘ id)
     ≡⟨   sym distribute⊗   ⟩
       ((εₘ ⊗ₘ id) ● λₘ) ⊗ₘ (id ● id)
     ≡⟨  refl⟨⊗⟩ left-id  ⟩
       ((εₘ ⊗ₘ id) ● λₘ) ⊗ₘ id
     ≡⟨⟩
        π₂ ⊗ₘ id
     ∎

  σ●π₁≡π₂ : {a b : obj}
    → σₘ ● π₁ ≡ π₂ {a = a} {b = b}
  σ●π₁≡π₂ =
    begin
       σₘ ● ((id ⊗ₘ εₘ) ● ρₘ)
    ≡⟨  sym assoc  ⟩
       σₘ ● (id ⊗ₘ εₘ) ● ρₘ
    ≡⟨    (sym σ□) ⟨●⟩refl   ⟩
       (εₘ ⊗ₘ id) ● σₘ ● ρₘ
    ≡⟨    assoc   ⟩
       (εₘ ⊗ₘ id) ● (σₘ ● ρₘ)
    ≡⟨    refl⟨●⟩ (sym λ≡σ●ρ )   ⟩
       (εₘ ⊗ₘ id) ● λₘ
    ∎

  σ●π₂≡π₁ : {a b : obj}
    → σₘ ● π₂ ≡ π₁ {a = a} {b = b}
  σ●π₂≡π₁ =
    begin
       σₘ ● ((εₘ ⊗ₘ id) ● λₘ)
    ≡⟨  sym assoc  ⟩
       (σₘ ● (εₘ ⊗ₘ id)) ● λₘ
    ≡⟨  (sym σ□) ⟨●⟩refl   ⟩
       (id ⊗ₘ εₘ) ● σₘ ● λₘ
    ≡⟨    assoc   ⟩
       (id ⊗ₘ εₘ) ● (σₘ ● λₘ)
    ≡⟨    refl⟨●⟩ (sym ρ≡σ●λ)   ⟩
       (id ⊗ₘ εₘ) ● ρₘ
    ∎

  ▵-identityπ : {a b c : obj}
    → αₘ {a = a} {b = b} {c = c} ● (id ⊗ₘ π₂) ≡ π₁ ⊗ₘ id
  ▵-identityπ =
    begin
        αₘ ● (id ⊗ₘ π₂)
    ≡⟨⟩
        αₘ ● (    id    ⊗ₘ ((εₘ ⊗ₘ id) ● λₘ))
    ≡⟨   refl⟨●⟩ ((sym left-id) ⟨⊗⟩refl)   ⟩
        αₘ ● ((id ● id) ⊗ₘ ((εₘ ⊗ₘ id) ● λₘ))
    ≡⟨  refl⟨●⟩ distribute⊗  ⟩
        αₘ ● ((id ⊗ₘ (εₘ ⊗ₘ id)) ● (id ⊗ₘ λₘ))
    ≡⟨  sym assoc  ⟩
        (αₘ ● (id ⊗ₘ (εₘ ⊗ₘ id))) ● (id ⊗ₘ λₘ)
    ≡⟨      sym α□ ⟨●⟩refl     ⟩
        ((id ⊗ₘ εₘ) ⊗ₘ id) ● αₘ ● (id ⊗ₘ λₘ)
    ≡⟨  assoc ⟩
        ((id ⊗ₘ εₘ) ⊗ₘ id) ● (αₘ ● (id ⊗ₘ λₘ))
    ≡⟨  refl⟨●⟩ ▵-identity  ⟩
        ((id ⊗ₘ εₘ) ⊗ₘ id) ● (ρₘ ⊗ₘ id)
    ≡⟨  sym distribute⊗  ⟩
        ((id ⊗ₘ εₘ) ● ρₘ) ⊗ₘ (id ● id)
    ≡⟨  refl⟨⊗⟩  left-id    ⟩
        π₁ ⊗ₘ id
    ∎

  copyαπ₂≡id : {a b : obj}
    → (δₘ {c = a} ⊗ₘ id {a = b}) ● αₘ ● (id ⊗ₘ π₂) ≡ id
  copyαπ₂≡id =
    begin
       (δₘ ⊗ₘ id) ● αₘ ● (id ⊗ₘ π₂)
    ≡⟨  assoc  ⟩
       (δₘ ⊗ₘ id) ● (αₘ ● (id ⊗ₘ π₂))
    ≡⟨  refl⟨●⟩ ▵-identityπ  ⟩
       (δₘ ⊗ₘ id) ● (π₁ ⊗ₘ id)
    ≡⟨⟩
       (δₘ ⊗ₘ id) ● (((id ⊗ₘ εₘ) ● ρₘ) ⊗ₘ id)
    ≡⟨  sym distribute⊗  ⟩
       (δₘ ● ((id ⊗ₘ εₘ) ● ρₘ)) ⊗ₘ (id ● id)
    ≡⟨  (sym assoc) ⟨⊗⟩ left-id  ⟩
       (δₘ ● (id ⊗ₘ εₘ) ● ρₘ) ⊗ₘ id
    ≡⟨  copyDeleteρ ⟨⊗⟩refl ⟩
         id ⊗ₘ id
    ≡⟨  idLaw ⊗    ⟩
        id
    ∎

  δₘ●π₂≡id : {c : obj}
    → δₘ {c = c} ● π₂ ≡ id
  δₘ●π₂≡id =
    begin
      δₘ ● π₂
    ≡⟨⟩
      δₘ ● ((εₘ ⊗ₘ id) ● λₘ)
    ≡⟨  sym assoc  ⟩
      δₘ ● (εₘ ⊗ₘ id) ● λₘ
    ≡⟨  copyDeleteλ  ⟩
       id
    ∎
