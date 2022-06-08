{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Monoidal
open import SymmetricMonoidal

module Enriched
  {n m}
  {v : Cat n m}
  {mc : Monoidal v}
  (smc : SymmetricMonoidal mc) where

open Cat using (_[_,_]; _[_●_])
open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open Isomorphism._≅_
open _Functor_
open _NatTrans_
module vv = Cat v
open vv hiding (_[_,_];
                _[_●_];
                _ᵒᵖ;
                obj;
                right-id;
                left-id)

-- should enrichedCat have as a argument mc : Monoidal v?
record EnrichedCat (o : Level) : Set ((suc o) ⊔ m ⊔ n) where
  constructor MkEnriched
  open Monoidal.Monoidal mc
  open SymmetricMonoidal.SymmetricMonoidal smc
  field
    obj : Set o
    _homᵥ_ : obj → obj → Cat.obj v
    id↗ : {a : obj} → v [ 𝟙 ,  (a homᵥ a) ]
    ●↗ : (a b c : obj)
      → v [ ((a homᵥ b) ⊗ₒ (b homᵥ c)) , (a homᵥ c) ]


  field
    left-id : (a b : obj)
      → (v [ (id↗ ⊗ₘ id) ● (●↗ a a b) ]) ≡ λₘ
    right-id : {a b : obj}
      → (v [ (id ⊗ₘ id↗ ) ● (●↗ a b b) ]) ≡ ρₘ

    assoc : {a b c d : obj}
      → (                     begin→⟨ ((a homᵥ b) ⊗ₒ (b homᵥ c)) ⊗ₒ (c homᵥ d) ⟩
           αₘ                     →⟨ (a homᵥ b) ⊗ₒ ((b homᵥ c) ⊗ₒ (c homᵥ d)) ⟩
            (id ⊗ₘ (●↗ b c d))   →⟨ (a homᵥ b) ⊗ₒ (b       homᵥ            d)  ⟩
           ●↗ a b d               →⟨ (a          homᵥ                         d)                  ⟩end)
      ≡ (v [ ((●↗ a b c) ⊗ₘ id) ● (●↗ a c d) ])

  _[_,↗_] : obj → obj → Cat.obj v
  _[_,↗_] = _homᵥ_


  -- We need symmetry to define the opposite enriched category
  _ᵒᵖ : EnrichedCat o
  _ᵒᵖ = record
          { obj = obj
          ; _homᵥ_ = flip _homᵥ_
          ; id↗ = id↗
          ; ●↗ = λ c b a → σₘ ● (●↗ a b c)
          ; left-id = let l = left-id
                          r = right-id
                      in {!!} -- need to use the hexagon here?
          ; right-id = {!!}
          ; assoc = {!!}
          }
