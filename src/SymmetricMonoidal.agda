{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

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
open import Shapes
open Shapes.CommutativeSquare
open _Functor_
open _NatTrans_
open M


record SymmetricMonoidal : (Set (n ⊔ m)) where
  constructor MkSymmMonoidal

  field
    σX : _≅_ {cat = functorCategory} idFunctor swapFunctor

  -- ideally, I'd show whiskering is defined for groupoids too...
  σ : _≅_ {cat = functorCategory} (idFunctor ●F ⊗) (swapFunctor ●F ⊗)
  σ = MkIso
    (whiskerᵣ (forward σX) ⊗)
    (whiskerᵣ (inverse σX) ⊗)
    {!!}
    {!!}

  σₘ : {a b : obj} → (a ⊗ₒ b) hom (b ⊗ₒ a)
  σₘ {_} = η (forward σ)

  -- σₘ == σₘ'
  σₘ' : {a b : obj} → (a ⊗ₒ b) hom (b ⊗ₒ a)
  σₘ' {_} = η (inverse σ)

  σ□ : {a b c d : obj} → ∀ {f : (cat X cat) [ (a , b) , (c , d) ]}
    → (mapMor ⊗ f) ● σₘ ≡ σₘ ● (mapMor (swapFunctor ●F ⊗) f)
  σ□ {_} = eqPaths□ (naturality (forward σ))

  -- this identity is actually a natural isomorphism
  field
    ⬡-identity : {x y z : obj}
      → (σₘ {a = x} {b = y} ⊗ₘ id {a = z}) ● αₘ ● (id ⊗ₘ σₘ)
      ≡ αₘ ● σₘ {a = x} {b = (y ⊗ₒ z)} ● αₘ

  id≡σσ : {a b : obj} → id {a = (a ⊗ₒ b)} ≡ σₘ ● σₘ'
  id≡σσ {a = a} {b = b} =
    
        id
    ≡⟨  {!!}  ⟩
         {!!}
    ≡⟨  (let t = cong η (sym (rightInverseLaw σ))
         in {!t!}) ⟩
         {!!}
    ≡⟨  {!!}  ⟩
       σₘ ● σₘ'
    ∎

  σ'≡σ : {a b : obj} → σₘ' {a = a} {b = b} ≡ σₘ
  σ'≡σ =
      
          σₘ'
    ≡⟨   {!!}  ⟩
         σₘ
      ∎
  -- σ□' : {a b c d : obj} → ∀ {f : (cat X cat) [ (a , b) , (c , d) ]}
  --   → mapMor (swapFunctor ●F ⊗) f ● σₘ' ≡ σₘ' ● ({!!} ⊗ₘ {!f!})
  -- σ□' = eqPaths□ (naturality (inverse σ))


  -- TODO this follows from hexagon, pentagon and triangle but is surprisingly hard to prove
  -- https://www.sciencedirect.com/science/article/pii/0021869364900183
  λ≡σ●ρ : {x : obj}
    → λₘ {a = x} ≡ σₘ ● ρₘ
  λ≡σ●ρ = {!!}

  λ≡σ'●ρ : {x : obj}
    → λₘ {a = x} ≡ σₘ' ● ρₘ
  λ≡σ'●ρ = {!!}

  ρ≡σ●λ : {x : obj}
    → ρₘ {a = x} ≡ σₘ ● λₘ
  ρ≡σ●λ = 
       ρₘ
   ≡⟨  sym right-id ⟩
       id ● ρₘ
   ≡⟨  id≡σσ ⟨●⟩refl ⟩
       (σₘ ● σₘ') ● ρₘ
   ≡⟨  assoc ⟩
       σₘ ● (σₘ' ● ρₘ)
   ≡⟨  refl⟨●⟩ sym λ≡σ'●ρ ⟩
       σₘ ● λₘ
   ∎

  swapProd :  ((cat X cat) X (cat X cat)) Functor (cat X cat)
  swapProd = (|⇆|𝕏 ●F (⊗ 𝕏 ⊗))

  -- |⇆|⊗' : (idFunctor {cat = ((cat X cat) X (cat X cat))}) NatTrans (|⇆|𝕏 {c₁ = cat} {c₂ = cat} {c₃ = cat} {c₄ = cat})
  -- |⇆|⊗' = let x = (idNatTrans 𝕏ₙ (forward σX)) 𝕏ₙ idNatTrans
  --          -- we tensor the natural transformation from left and right side and then whisker it correspondingly to the right and to the left
  --          in whiskerₗ (productAssociatorᵣ ●F (productAssociatorₗ 𝕏 idFunctor )) (whiskerᵣ x ((productAssociatorᵣ 𝕏 idFunctor ) ●F productAssociatorₗ))

  -- -- it's easier to understand this natural transformation in terms of the morphism it associates to each object
  -- |⇆|⊗ : (idFunctor ●F ((⊗ 𝕏 ⊗) ●F ⊗)) NatTrans (|⇆|𝕏 ●F ((⊗ 𝕏 ⊗) ●F ⊗))
  -- |⇆|⊗ = whiskerᵣ |⇆|⊗' ((⊗ 𝕏 ⊗) ●F ⊗)

  -- |⇆|⊗ₘ : {a b c d : obj}
  --   → (a ⊗ₒ b) ⊗ₒ (c ⊗ₒ d) hom
  --     (a ⊗ₒ c) ⊗ₒ (b ⊗ₒ d)
  -- |⇆|⊗ₘ = η |⇆|⊗

  -- |⇆|⊗□ : _
  -- |⇆|⊗□ = naturality |⇆|⊗
