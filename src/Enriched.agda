open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Monoidal

module Enriched
  {n m o}
  (v : Cat n m)
  (mc : Monoidal v) where

open Cat using (_[_,_]; _[_●_])
open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open Isomorphism._≅_
open _Functor_
open _NatTrans_
module vv = Cat v
open vv hiding (_[_,_]; _[_●_]; _●_)

record Enriched : Set ((suc o) ⊔ m ⊔ n) where
  constructor MkEnriched
  open Monoidal.Monoidal mc
  field
    obj : Set o
    _homᵥ_ : obj → obj → Cat.obj v
    id⃯ : {a : obj} → v [ 𝟙 ,  (a homᵥ a) ]
    ●⃯ : (a b c : obj)
      → v [ ((a homᵥ b) ⊗ₒ (b homᵥ c)) , (a homᵥ c) ]

    left-id : {a b : obj}
      → (v [ (id⃯ ⊗ₘ id) ● (●⃯ a a b) ]) ≡ λₘ

    right-id : {a b : obj}
      → (v [ (id ⊗ₘ id⃯ ) ● (●⃯ a b b) ]) ≡ ρₘ

    assoc : {a b c d : obj}
      → (              begin→⟨ ((a homᵥ b) ⊗ₒ (b homᵥ c)) ⊗ₒ (c homᵥ d) ⟩
           {!!}                →⟨ (a homᵥ b) ⊗ₒ ((b homᵥ c) ⊗ₒ (c homᵥ d)) ⟩
           (id ⊗ₘ {!!})       →⟨ (a homᵥ b) ⊗ₒ (b       homᵥ            d)  ⟩
           ●⃯ a b d            →⟨ (a          homᵥ                         d)                  ⟩end)
      ≡ (v [ (●⃯ a b c) ⊗ₘ id ● (●⃯ a c d) ])
