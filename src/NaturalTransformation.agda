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

private
  variable
    n'' m'' : Level

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

_∘ᵥ_ : {f g h : cat1 Functor cat2}
  →            g NatTrans h
  → f NatTrans g
  → f      NatTrans       h
_∘ᵥ_ (MkNatTrans η₂ naturality₂) (MkNatTrans η₁ naturality₁)
  = MkNatTrans (cat2 [ η₁ ● η₂ ] ) (Cat.glue cat2 naturality₁ naturality₂)



-- actually should be called naturalTransformation category
functorCategory : Cat (n ⊔ n' ⊔ m ⊔ m') (n ⊔ n' ⊔ m ⊔ m')
functorCategory = MkCat
  (cat1 Functor cat2)
  _NatTrans_
  idNatTrans
  _∘ᵥ_
  (let gg = Cat.left-id cat2 in {!!})
  {!!}
  {!!}
  {!!}
  where
  open Cat
  module cat2 = Cat cat2
  open cat2

-- Goal: {a b : cat1 Functor cat2} {f : a NatTrans b} →
-- (idNatTrans ∘ₕ f) ≡ f
