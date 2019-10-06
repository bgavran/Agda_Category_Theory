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

module Cartesian
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

record Cartesian : (Set (n ⊔ m)) where
  constructor MkCartesian

  field
    deleteApply : {a b : obj} {f : a hom b} → ε ≡ f ● ε
    copyApply   : {a b : obj} {f : a hom b} → f ● δ ≡ δ ● (f ⊗ₘ f)

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
