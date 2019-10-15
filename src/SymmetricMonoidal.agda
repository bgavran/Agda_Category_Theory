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

  -- σₘ == σₘ'
  -- σₘ' : {a b : obj} → (a ⊗ₒ b) hom (b ⊗ₒ a)
  -- σₘ' = η (inverse σ)

  σ□ : {a b c d : obj} → ∀ {f : (cat X cat) [ (a , b) , (c , d) ]}
    → (mapMor ⊗ f) ● σₘ ≡ σₘ ● (mapMor (swapFunctor ●F ⊗) f)
  σ□ = eqPaths (naturality (forward σ))

  id≡σσ : {a b : obj} → id {a = (a ⊗ₒ b)} ≡ σₘ ● σₘ
  id≡σσ {a = a} {b = b} =
    begin
        id
    ≡⟨  (let t = sym (rightInverseLaw σ)
             tt = cong (η ) t
         in {!!}) ⟩
       σₘ ● σₘ
    ∎

  -- σ□' : {a b c d : obj} → ∀ {f : (cat X cat) [ (a , b) , (c , d) ]}
  --   → mapMor (swapFunctor ●F ⊗) f ● σₘ' ≡ σₘ' ● ({!!} ⊗ₘ {!f!})
  -- σ□' = eqPaths (naturality (inverse σ))
  -- TODO coherence


  -- TODO this follows from hexagon, pentagon and triangle but is surprisingly hard to prove
  -- https://www.sciencedirect.com/science/article/pii/0021869364900183
  λ≡σ●ρ : {x : obj}
    → λₘ {a = x} ≡ σₘ ● ρₘ
  λ≡σ●ρ = {!!}

  ρ≡σ●λ : {x : obj}
    → ρₘ {a = x} ≡ σₘ ● λₘ
  ρ≡σ●λ = begin
       ρₘ
   ≡⟨  sym right-id ⟩
       id ● ρₘ
   ≡⟨  id≡σσ ⟨●⟩refl ⟩
       (σₘ ● σₘ) ● ρₘ
   ≡⟨  assoc ⟩
       σₘ ● (σₘ ● ρₘ)
   ≡⟨  refl⟨●⟩ sym λ≡σ●ρ ⟩
       σₘ ● λₘ
   ∎

  |⇆|⊗ : {a b c d : obj}
    → (a ⊗ₒ b) ⊗ₒ (c ⊗ₒ d) hom
      (a ⊗ₒ c) ⊗ₒ (b ⊗ₒ d)
  |⇆|⊗ = αₘ
    ● (id ⊗ₘ αₘ' )
    ● id ⊗ₘ (σₘ ⊗ₘ id)
    ● (id ⊗ₘ αₘ)
    ● αₘ'
