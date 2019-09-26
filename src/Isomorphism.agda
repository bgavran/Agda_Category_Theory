open import Level
open import Function using (flip)
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Category

module Isomorphism {n m} {cat : Cat n m} where

module cat = Cat cat
open cat
-- TODO
-- monoidal product of isomorphisms

record _≅_ (a : obj) (b : obj) : Set (n ⊔ m) where
  constructor MkIso
  field
    forward : a hom b
    inverse : b hom a
    leftInverseLaw  : inverse ● forward ≡ id
    rightInverseLaw : forward ● inverse ≡ id

open _≅_

_●≅_ : {a b c : obj}
  → a ≅ b → b ≅ c → a ≅ c
f ●≅ g = MkIso
  (forward f ● forward g)
  (inverse g ● inverse f)
  (begin
    (inverse g ● inverse f) ● (forward f ● forward g)
   ≡⟨ sym assoc  ⟩
    ((inverse g ● inverse f) ● forward f) ● forward g
   ≡⟨ assoc ⟨●⟩refl  ⟩
    (inverse g ● (inverse f ● forward f)) ● forward g
   ≡⟨ (refl⟨●⟩ leftInverseLaw f) ⟨●⟩refl ⟩
    (inverse g ● id) ● forward g
   ≡⟨ left-id ⟨●⟩refl  ⟩
    inverse g ● forward g
   ≡⟨ leftInverseLaw g  ⟩
    id
   ∎ )
   (begin
      (forward f ● forward g) ● (inverse g ● inverse f)
   ≡⟨ sym assoc  ⟩
      ((forward f ● forward g) ● inverse g) ● inverse f
   ≡⟨ assoc ⟨●⟩refl  ⟩
      (forward f ● (forward g ● inverse g)) ● inverse f
   ≡⟨ (refl⟨●⟩ rightInverseLaw g) ⟨●⟩refl ⟩
      (forward f ● id) ● inverse f
   ≡⟨ left-id ⟨●⟩refl  ⟩
      forward f ● inverse f
   ≡⟨ rightInverseLaw f   ⟩
      id
   ∎ )
