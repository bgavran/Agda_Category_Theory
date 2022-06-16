{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Monoidal
open import SymmetricMonoidal

-- levels are called m and m' since they represents 1-cells and 2-cells, respectively
module Enriched
  {m m' : Level}
  {v : Cat m m'}
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
open vv hiding (_[_,_]; _[_●_]; obj; right-id; left-id)

private
  variable o o' : Level

record EnrichedCat {o : Level} : Set ((suc o) ⊔ m ⊔ m') where
  constructor MkEnriched
  open Monoidal.Monoidal mc
  open SymmetricMonoidal.SymmetricMonoidal smc
  field
    obj : Set o
    _homᵥ_ : obj → obj → Cat.obj v
    id↗ : {a : obj} → v [ 𝕀 ,  (a homᵥ a) ]
    ●↗ : (a b c : obj)
      → v [ ((a homᵥ b) ⊗ₒ (b homᵥ c)) , (a homᵥ c) ]


  field
    left-id : (a b : obj)
      → (v [ (id↗ ⊗ₘ id) ● (●↗ a a b) ]) ≡ λₘ
    right-id : {a b : obj}
      → (v [ (id ⊗ₘ id↗ ) ● (●↗ a b b) ]) ≡ ρₘ

    assoc : {a b c d : obj}
      → (v [ v [ αₘ ● (id ⊗ₘ (●↗ b c d)) ] ● (●↗ a b d) ] ≡ v [ ((●↗ a b c) ⊗ₘ id) ● (●↗ a c d)  ])
      -- → (                     begin→⟨ ((a homᵥ b) ⊗ₒ (b homᵥ c)) ⊗ₒ (c homᵥ d) ⟩
      --      αₘ                     →⟨ (a homᵥ b) ⊗ₒ ((b homᵥ c) ⊗ₒ (c homᵥ d)) ⟩
      --       (id ⊗ₘ (●↗ b c d))   →⟨ (a homᵥ b) ⊗ₒ (b       homᵥ            d)  ⟩
      --      ●↗ a b d               →⟨ (a          homᵥ                         d)                  ⟩end)
      -- ≡ (v [ ((●↗ a b c) ⊗ₘ id) ● (●↗ a c d) ])

  _[_,↗_] : obj → obj → Cat.obj v
  _[_,↗_] = _homᵥ_


  -- We need symmetry (or maybe just braiding?) to define the opposite enriched category
  _ᵒᵖ : EnrichedCat {o}
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


open EnrichedCat

-- This gives us a strict 2-functor when v = Cat. What about an (op)lax functor?
record _EnrichedFunctor_ {o o' : Level} (vcat₁ : EnrichedCat {o}) (vcat₂ : EnrichedCat {o'}) : Set (o ⊔ o' ⊔ m') where
  constructor MkEnrichedFunctor
  open Monoidal.Monoidal mc
  field
     mapObj : obj vcat₁ → obj vcat₂
     mapMor : {a b : obj vcat₁} → v [ vcat₁ [ a ,↗ b ] , vcat₂ [ mapObj a ,↗ mapObj b ] ]
     idLaw : {a : obj vcat₁}
       → v [ id↗ vcat₁ {a} ● mapMor {a} {a} ] ≡ id↗ vcat₂ {mapObj a}
     compLaw : {a b c : obj vcat₁}
       → v [ ●↗ vcat₁ a b c ● mapMor {a} {c} ] ≡ v [ ((mapMor {a} {b}) ⊗ₘ (mapMor {b} {c})) ● ●↗ vcat₂ (mapObj a) (mapObj b) (mapObj c) ]

