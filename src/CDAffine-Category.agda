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
open import CD-Category
open import Isomorphism

-- CDAffine-category is defined in https://arxiv.org/abs/1709.00322 , Definition 2.3
-- CD stands for Copy/Discard
-- It is like a Cartesian category except the morphisms aren't natural w.r.t copy (but are natural w.r.t delete)
-- It also means the unit object in the monoidal category is terminal
module CDAffine-Category
  {n m}
  {cat : Cat n m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  (cd : CD-Category smc) where

private
  variable
    n' m' n'' m'' : Level
  module C = Cat cat
  module M = Monoidal.Monoidal mc
  module S = SymmetricMonoidal.SymmetricMonoidal smc
  module CD = CD-Category.CD-Category cd

open _Functor_
open C
open M
open S
open CD
open Isomorphism._≅_
open _NatTrans_

record CDAffine-Category : (Set (n ⊔ m)) where
  constructor MkCDAffine

  field
    -- Naturality w.r.t. deletion
    deleteApply : {a b : obj} {f : a hom b} → εₘ ≡ f ● εₘ


  idmorphismon𝟙≡εₘ : id {a = 𝟙} ≡ εₘ
  idmorphismon𝟙≡εₘ =
     begin
         id
     ≡⟨  sym left-id  ⟩
         id ● id
     ≡⟨  {!!}  ⟩
         εₘ ● εₘ
     ≡⟨  sym deleteApply  ⟩
         εₘ
     ∎

  𝟙terminal : {a : obj} → {f : a hom 𝟙} → f ≡ εₘ
  𝟙terminal {f = f} =
    begin
       f
    ≡⟨ {!!} ⟩
       {!εₘ ● id!}
    ≡⟨  {!!} ⟩
       f ● εₘ
    ≡⟨  sym deleteApply ⟩
       εₘ
    ∎


  π₂law : {a b c d : obj} {f : a hom b} {g : c hom d}
    → (f ⊗ₘ g) ● π₂ ≡ π₂ ● g
  π₂law {f = f} {g = g} =
    begin
      (f ⊗ₘ g) ● π₂
    ≡⟨⟩
      (f ⊗ₘ g) ● ((εₘ ⊗ₘ id) ● λₘ)
    ≡⟨ sym assoc ⟩
      (f ⊗ₘ g) ● (εₘ ⊗ₘ id) ● λₘ
    ≡⟨ sym distribute⊗ ⟨●⟩refl ⟩
      (f ● εₘ) ⊗ₘ (g ● id) ● λₘ
    ≡⟨ ((sym deleteApply) ⟨⊗⟩ left-id) ⟨●⟩refl ⟩
      (εₘ ⊗ₘ g) ● λₘ
    ≡⟨ ((sym left-id) ⟨⊗⟩ (sym right-id)) ⟨●⟩refl   ⟩
      ((εₘ ● id) ⊗ₘ  (id ● g)) ● λₘ
    ≡⟨ distribute⊗ ⟨●⟩refl   ⟩
      (εₘ ⊗ₘ id) ●  (id ⊗ₘ g) ● λₘ
    ≡⟨ trans assoc (refl⟨●⟩ λ□)  ⟩
      (εₘ ⊗ₘ id) ● (λₘ ● g)
    ≡⟨ sym assoc  ⟩
      (εₘ ⊗ₘ id) ● λₘ ● g
    ≡⟨⟩
      π₂ ● g
    ∎

  π₁law : {a b c d : obj} {f : a hom b} {g : c hom d}
    → (f ⊗ₘ g) ● π₁ ≡ π₁ ● f
  π₁law {b = b} {d = d} {f = f} {g = g} =
    begin
      (f ⊗ₘ g) ● π₁
    ≡⟨  sym left-id ⟨●⟩refl  ⟩
      (f ⊗ₘ g) ● id ● π₁
    ≡⟨  (refl⟨●⟩ id≡σσ) ⟨●⟩refl  ⟩
      (f ⊗ₘ g) ● (σₘ ● σₘ) ● π₁
    ≡⟨  trans assoc (refl⟨●⟩ assoc) ⟩
      (f ⊗ₘ g) ● (σₘ ● (σₘ ● π₁))
    ≡⟨  refl⟨●⟩ (refl⟨●⟩ σ●π₁≡π₂) ⟩
      (f ⊗ₘ g) ● (σₘ ● π₂)
    ≡⟨  sym assoc ⟩
      ((f ⊗ₘ g) ● σₘ) ● π₂
    ≡⟨  σ□ ⟨●⟩refl ⟩
      (σₘ ● (g ⊗ₘ f)) ● π₂
    ≡⟨  assoc ⟩
      σₘ ● ((g ⊗ₘ f) ● π₂)
    ≡⟨  refl⟨●⟩ π₂law ⟩
      σₘ ● (π₂ ● f)
    ≡⟨  trans (sym assoc) (σ●π₂≡π₁ ⟨●⟩refl) ⟩
       π₁ ● f
    ∎
