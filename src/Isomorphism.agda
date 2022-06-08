{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Utils

module Isomorphism {o m} {cat : Cat o m} where

open Cat cat
-- TODO
-- monoidal product of isomorphisms

record _≅_ (a : obj) (b : obj) : Set (o ⊔ m) where
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
  ((inverse g ● inverse f) ● (forward f ● forward g)
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
   (
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


idIso : {a : obj} → (a ≅ a)
idIso = MkIso id id left-id left-id


leftIsoId : {a b : Cat.obj cat} {f : a ≅ b} → (f ●≅ idIso) ≡ f
leftIsoId {f = (MkIso f b s r)} = λ i → MkIso {!!} {!!} {!!} {!!}

isoCategory : Cat o (o ⊔ m)
isoCategory = MkCat
  obj
  _≅_
  idIso
  _●≅_
  leftIsoId
  {!!}
  {!!}
  {!!}
