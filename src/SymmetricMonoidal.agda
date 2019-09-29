{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal


module SymmetricMonoidal {n m} {cat : Cat n m} (mc : Monoidal cat) where

private
  module scc = Cat cat
  module M = Monoidal.Monoidal mc
  variable
    n' m' n'' m'' : Level

open scc hiding (_[_,_])
open Isomorphism._≅_
open Cat using (_[_,_])
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_
open M


record SymmetricMonoidal : (Set (n ⊔ m)) where
  constructor MkSymmMonoidal

  field
    σ : _≅_ {cat = functorCategory} ⊗ (swapFunctor ●F ⊗)

  σₘ : {a b : obj} → (a ⊗ₒ b) hom (b ⊗ₒ a)
  σₘ = η (forward σ)

  σₘ' : {a b : obj} → (a ⊗ₒ b) hom (b ⊗ₒ a)
  σₘ' = η (inverse σ)

  σ□ : {a b c d : obj} → ∀ {f : (cat X cat) [ (a , b) , (c , d) ]}
    -- → {g : cat [ ? , ? ]}
    → (mapMor ⊗ f) ● σₘ ≡ σₘ ● (mapMor (swapFunctor ●F ⊗) f)
  σ□ = eqPaths (naturality (forward σ))
  -- TODO coherence


  -- TODO this follows from hexagon, pentagon and triangle but is surprisingly hard to prove
  -- https://www.sciencedirect.com/science/article/pii/0021869364900183
  λ≡σ●ρ : {x : obj}
    → λₘ {a = x} ≡ σₘ ● ρₘ
  λ≡σ●ρ = {!!}
