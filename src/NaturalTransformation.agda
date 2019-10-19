{-# OPTIONS --allow-unsolved-metas #-}

module NaturalTransformation where

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category
open import Functor

open Cat


record _NatTrans_
  {n m n' m'}
  {cat1 : Cat n m}
  {cat2 : Cat n' m'}
  (fun1 fun2 : cat1 Functor cat2) : Set (n ⊔ m ⊔ n' ⊔ m') where
  constructor MkNatTrans
  module fun1 = _Functor_ fun1
  module fun2 = _Functor_ fun2
  open fun1 renaming (mapObj to mapObj₁; mapMor to mapMor₁)
  open fun2 renaming (mapObj to mapObj₂; mapMor to mapMor₂)
  field
    η : {a : obj cat1} → cat2 [ mapObj₁ a , mapObj₂ a ]
    naturality : {a b : obj cat1} {f : cat1 [ a , b ]}
      → CommutativeSquare cat2 (mapMor₁ f) η η (mapMor₂ f)

private
  variable
    n m n' m' n'' m'' : Level
    cat1 cat2 cat3 : Cat n m

idNatTrans : {cat1 : Cat n m} {cat2 : Cat n' m'} {fun1 : cat1 Functor cat2}
  → fun1 NatTrans fun1
idNatTrans {cat1 = cat1} {cat2 = cat2} {fun1 = fun1} = MkNatTrans
  (id cat2)
  (λ {a b : obj cat1} {f : cat1 [ a , b ] } → MkCommSq (
    begin
      cat2 [ mapMor f ● id cat2 ]
    ≡⟨ left-id cat2  ⟩
       mapMor f
    ≡⟨ sym (right-id cat2) ⟩
      cat2 [ id cat2 ● mapMor f ]
    ∎))
  where
  module fun1 = _Functor_ fun1
  open fun1

-- vertical
_●ᵥ_ : {cat1 : Cat n m} {cat2 : Cat n' m'} {f g h : cat1 Functor cat2}
  → f NatTrans g
  →            g NatTrans h
  → f      NatTrans       h
_●ᵥ_ {cat2 = cat2} (MkNatTrans η₁ naturality₁) (MkNatTrans η₂ naturality₂)
  = MkNatTrans (cat2 [ η₁ ● η₂ ]) (Cat.glue cat2 naturality₁ naturality₂)



natTransLeftId : {f g : cat1 Functor cat2} {α : f NatTrans g}
  → α ●ᵥ idNatTrans ≡ α
natTransLeftId {f = f} {g = g} {α  = (MkNatTrans ηₗ naturalityₗ)} = {!!}
  -- (begin
  --     (α ●ᵥ idNatTrans)
  -- ≡⟨  {!!}  ⟩
  --     α
  -- ∎)

-- TODO figure out how to do this: (taken from agda-categories)
-- -- The reason the proofs below are so easy is that _∘ᵥ_ 'computes' all the way down into
-- -- expressions in D, from which the properties follow.

-- actually should be called naturalTransformation category
functorCategory : {cat1 : Cat n m} {cat2 : Cat n' m'}
  → Cat (n ⊔ n' ⊔ m ⊔ m') (n ⊔ n' ⊔ m ⊔ m')
functorCategory {cat1 = cat1} {cat2 = cat2}= MkCat
  (cat1 Functor cat2)
  _NatTrans_
  idNatTrans
  _●ᵥ_
  (let t = left-id cat2 in {!!})
  {!!}
  {!!}
  {!!}

whiskerₗ : {F G : cat1 Functor cat2} (H : cat2 Functor cat3) (α : F NatTrans G)
  → (F ●F H) NatTrans (G ●F H)
whiskerₗ H (MkNatTrans η naturality) = MkNatTrans
  (λ {a} → mapMor (η {a}))
  {!!}
  where
  module hfun = _Functor_ H
  open hfun

whiskerᵣ : {F G : cat2 Functor cat3} (H : cat1 Functor cat2) (α : F NatTrans G)
  → (H ●F F) NatTrans (H ●F G)
whiskerᵣ H (MkNatTrans η naturality) = MkNatTrans
  (λ {a} → η {mapObj a})
  {!!}
  where
  module hfun = _Functor_ H
  open hfun
