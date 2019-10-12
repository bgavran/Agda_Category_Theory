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

-- CDAffine-category is defined in https://arxiv.org/abs/1709.00322 , Definition 2.3
-- CD stands for Copy/Discard
-- It is like a Cartesian category except the morphisms aren't natural w.r.t copy (but are natural w.r.t delete)
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

-- It also means the unit object in the monoidal category is terminal
record CDAffine-Category : (Set (n ⊔ m)) where
  constructor MkCDAffine

  field
    -- Naturality w.r.t. deletion
    deleteApply : {a b : obj} {f : a hom b} → ε ≡ f ● ε


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
    ≡⟨ ((sym deleteApply) ⟨⊗⟩ left-id) ⟨●⟩refl ⟩
      (ε ⊗ₘ g) ● λₘ
    ≡⟨ ((sym left-id) ⟨⊗⟩ (sym right-id)) ⟨●⟩refl   ⟩
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
