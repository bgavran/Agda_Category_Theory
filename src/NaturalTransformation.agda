{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor

module NaturalTransformation
  {n m n' m'}
  {cat1 : Cat n m}
  {cat2 : Cat n' m'}
  where

open Cat

record _NatTrans_ (fun1 fun2 : cat1 Functor cat2) : Set (n ⊔ m ⊔ n' ⊔ m') where
  constructor MkNatTrans
  module fun1 = _Functor_ fun1
  module fun2 = _Functor_ fun2
  open fun1 renaming (mapObj to mapObj₁; mapMor to mapMor₁)
  open fun2 renaming (mapObj to mapObj₂; mapMor to mapMor₂)
  field
    η : {a : obj cat1} → cat2 [ mapObj₁ a , mapObj₂ a ]
    naturality : {a b : obj cat1} {f : cat1 [ a , b ]}
      → CommutativeSquare cat2 (mapMor₁ f) η η (mapMor₂ f)

idNatTrans : {fun1 : cat1 Functor cat2}
  → fun1 NatTrans fun1
idNatTrans {fun1 = fun1}
  = MkNatTrans (id cat2) naturalityId'
  where
  module fun1 = _Functor_ fun1
  open fun1
  naturalityId' : {a b : obj cat1} {f : cat1 [ a , b ]}
    → CommutativeSquare cat2 (mapMor f) (id cat2) (id cat2) (mapMor f)
  naturalityId' {f = f} = MkCommSq (
    begin
      cat2 [ mapMor f ● id cat2 ]
    ≡⟨ left-id cat2  ⟩
       mapMor f
    ≡⟨ sym (right-id cat2) ⟩
      cat2 [ id cat2 ● mapMor f ]
    ∎)

_●ᵥ_ : {f g h : cat1 Functor cat2}
  → f NatTrans g
  →            g NatTrans h
  → f      NatTrans       h
_●ᵥ_ (MkNatTrans η₁ naturality₁) (MkNatTrans η₂ naturality₂)
  = MkNatTrans (cat2 [ η₁ ● η₂ ]) (Cat.glue cat2 naturality₁ naturality₂)



natTransLeftId : {f g : cat1 Functor cat2} {α : f NatTrans g}
  → α ●ᵥ idNatTrans ≡ α
natTransLeftId {f = f} {g = g} {α  = (MkNatTrans ηₗ naturalityₗ)} = {!!}
  -- (begin
  --     (α ●ᵥ idNatTrans)
  -- ≡⟨  {!!}  ⟩
  --     α
  -- ∎)

-- TODO figure out how to do this also (taken from agda-categories)
-- -- The reason the proofs below are so easy is that _∘ᵥ_ 'computes' all the way down into
-- -- expressions in D, from which the properties follow.

-- actually should be called naturalTransformation category
functorCategory : Cat (n ⊔ n' ⊔ m ⊔ m') (n ⊔ n' ⊔ m ⊔ m')
functorCategory = MkCat
  (cat1 Functor cat2)
  _NatTrans_
  idNatTrans
  _●ᵥ_
  (let t = left-id cat2 in {!!})
  {!!}
  {!!}
  {!!}
