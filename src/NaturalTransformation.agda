{-# OPTIONS --allow-unsolved-metas #-}

module NaturalTransformation where

open import Level
open import Data.Product
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import Shapes

open Cat


record _NatTrans_
  {o₁ m₁ o₂ m₂}
  {cat1 : Cat o₁ m₁}
  {cat2 : Cat o₂ m₂}
  (F G : cat1 Functor cat2) : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  constructor MkNatTrans
  open _Functor_ F renaming (mapObj to F₀; mapMor to F₁) -- F₀ is mapping on objects, F₁ is mapping on morphisms
  open _Functor_ G renaming (mapObj to G₀; mapMor to G₁)
  field
    η : {a : obj cat1} → cat2 [ F₀ a , G₀ a ]
    naturality : {a b : obj cat1} {f : cat1 [ a , b ]}
      → CommutativeSquare cat2 (F₁ f) η η (G₁ f)

private
  variable
    n m n' m' n'' m'' : Level
    cat1 cat2 cat3 cat4 : Cat n m

idNatTrans : {cat1 : Cat n m} {cat2 : Cat n' m'} {fun1 : cat1 Functor cat2}
  → fun1 NatTrans fun1
idNatTrans {cat1 = cat1} {cat2 = cat2} {fun1 = fun1} = MkNatTrans
  (id cat2)
  -- λ { a b : obj cat1} {f = f} → MkCommSq {!!} 
  (λ {a b : obj cat1} {f = f} → MkCommSq (
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
  = MkNatTrans (cat2 [ η₁ ● η₂ ]) (Shapes.glue□↓ cat2 naturality₁ naturality₂)

_●ₕ_ : {cat1 : Cat n m} {cat2 : Cat n' m'} {cat3 : Cat n'' m''}
  {F G : cat1 Functor cat2}
  {H I : cat2 Functor cat3}
  → F NatTrans G
  → H NatTrans I
  → (F ●F H) NatTrans (G ●F I)
_●ₕ_ {cat3 = cat3} {F = F} {G = G} {H = H} {I = I} (MkNatTrans η₁ naturality₁) (MkNatTrans η₂ naturality₂) = MkNatTrans
  (cat3 [ η₂ ● mapMori η₁  ])
  (MkCommSq {!!})
  where
  module ffun = _Functor_ F
  module gfun = _Functor_ G
  module hfun = _Functor_ H
  module ifun = _Functor_ I
  open ffun renaming (mapObj to mapObjf; mapMor to mapMorf)
  open gfun renaming (mapObj to mapObjg; mapMor to mapMorg)
  open hfun renaming (mapObj to mapObjh; mapMor to mapMorh)
  open ifun renaming (mapObj to mapObji; mapMor to mapMori)


natTransLeftId : {f g : cat1 Functor cat2} {α : f NatTrans g}
  → α ●ᵥ idNatTrans ≡ α
natTransLeftId {f = f} {g = g} {α  = (MkNatTrans ηₗ naturalityₗ)} = {!!} -- cong₂ MkNatTrans ? ?
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

-- whisker on left and right side
→⇓→ : (F : cat1 Functor cat2) {G H : cat2 Functor cat3} (α : G NatTrans H) (I : cat3 Functor cat4)
  → (F ●F G ●F I) NatTrans (F ●F H ●F I)
→⇓→ F (MkNatTrans η naturality) I = MkNatTrans
  (λ {a} → mapMorᵣ η)
  (MkCommSq {!!})
  where
  module ffun = _Functor_ F
  module ifun = _Functor_ I
  open ffun renaming (mapObj to mapObjₗ; mapMor to mapMorₗ)
  open ifun renaming (mapObj to mapObjᵣ; mapMor to mapMorᵣ)

whiskerᵣ : {F G : cat1 Functor cat2} (α : F NatTrans G) (H : cat2 Functor cat3)
  → (F ●F H) NatTrans (G ●F H)
whiskerᵣ (MkNatTrans η naturality) H = MkNatTrans
  (λ {a} → mapMor (η {a}))
  {!!}
  where
  module hfun = _Functor_ H
  open hfun

whiskerₗ : {F G : cat2 Functor cat3} (H : cat1 Functor cat2) (α : F NatTrans G)
  → (H ●F F) NatTrans (H ●F G)
whiskerₗ H (MkNatTrans η naturality) = MkNatTrans
  (λ {a} → η {mapObj a})
  {!!}
  where
  module hfun = _Functor_ H
  open hfun

-- this is just a comma category...
fff : (c : Cat n m) → (D : c Functor c) → Cat _ _
fff c D = MkCat
  (Σ (obj c) (λ x → c [ x , mapObj x ] ))
  (λ a b → {!!})
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  where
  module fun = _Functor_ D
  open fun
