{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (Lift)
open import Data.Unit using (⊤; tt) -- for the terminal category
open import Data.Empty using (⊥) -- for the initial category
open import Data.Product
open import Agda.Builtin.Bool
open import Function renaming (id to idff)
open import Data.Empty

open import Utils
open import Category
open import Functor
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import MonoidalNaturalTransformation
open import Shapes

open import SetInstance

-- open import Terminal -- probably should move this proof of terminality of oneObjectCat to a different file

open Cat
open _Functor_

module CategoryOfCategories where

leftIdFunctor : {n m : Level} → {a b : Cat n m} {f : a Functor b} → (f ●F idFunctor) ≡ f
leftIdFunctor {f = f} = λ i → MkFunctor (mapObj f) (mapMor f) {!!} {!!}

catOfCats : {o m : Level} → Cat (suc o ⊔ suc m) (o ⊔ m)
catOfCats {o = o} {m = m} = MkCat
  (Cat o m)
  _Functor_
  idFunctor
  _●F_
  leftIdFunctor
  {!!}
  {!!}
  {!!}


ᵒᵖ : catOfCats Functor catOfCats
ᵒᵖ = MkFunctor
  (λ cat → Cat._ᵒᵖ cat)
  (λ F → MkFunctor (mapObj F) (mapMor F) (idLaw F) λ f g → compLaw F g f)
  (λ i → MkFunctor (λ x → x) (λ x → x) (λ i → {!!}) {!!})
  λ f g → λ i → {!!}


-- need the kronecker below δ : Set × Set → 2 ↦ ((a, a) ↦ 1 | (a, _) ↦ 0)
kron : {n : Level} {s : Set n} → s → s → Set n
kron a b = a ≡ b

disc : {n : Level} → Set n → Cat n n
disc {n = n} s = MkCat
  s
  kron
  (λ {a} → refl)
  (λ f g → {!?!})
  {!!}
  {!!}
  {!!}
  {!!}

disc' : {o : Level} → 𝕊𝕖𝕥 {o = o} Functor catOfCats {o = o}
disc' = MkFunctor
  disc
  {!!}
  {!!}
  {!!}



-- terminal category
oneObjectCat : {o m : Level} → Cat o m
oneObjectCat {o = o} {m = m} = MkCat
  (Lift o ⊤)
  (λ a b → Lift m ⊤)
  (lift tt)
  (λ _ _ → lift tt)
  refl
  refl
  refl
  λ _ _ → refl


-- oneObjectCatTerminal : {o m : Level} → Terminal {cat = catOfCats} oneObjectCat
-- oneObjectCatTerminal =
--   MkTerminal (λ anyCat → MkFunctor (λ x → lift tt) (λ x → lift tt) refl λ f g → refl)
--   (MkCommTr {!!})


-- name : {o m : Level} → Cat o m → oneObjectCat {o = o} {m = m} Functor catOfCats {o = o} {m = m}
-- name cat = MkFunctor (λ x → cat) (λ x → idFunctor) refl λ f g → refl

emptyCat : {o m : Level} → Cat o m
emptyCat {o = o} {m = m} = MkCat
  (Lift o ⊥)
  (λ a b → Lift m ⊥)
  (lift {!()!})  -- ??
  -- λ { { lift () } }
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}


catOfCatsMonoidal : Monoidal catOfCats
catOfCatsMonoidal = MkMonoidal
  {!!}
  oneObjectCat
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}

-- CatSymmetricMonoidal : SymmetricMonoidal catOfCatsMonoidal
-- CatSymmetricMonoidal = MkSymmMonoidal {!!}

-- CatCDCategory : CD-Category CatSymmetricMonoidal
-- CatCDCategory = MkCD-Category
--   --                                               should × go there?
--   (MkMonoidalNatTrans (MkNatTrans (MkFunctor (λ x → {!!} × {!!}) {!!} {!!} {!!}) {!!}) {!!} {!!})
--   (MkMonoidalNatTrans (MkNatTrans (MkFunctor (λ _ → lift tt) {!!} {!!} {!!}) {!!}) {!!} {!!})
--   {!!}
--   {!!}
--   {!!}


cc : {n m : Level} → {cat : Cat n m} → {mc : Monoidal cat} → Set (n ⊔ m)
cc {cat = cat} {mc = mc} = SymmetricMonoidal mc

-- category of cd-affine categories?
-- category of monoidal categories
catOfSMC : {n m : Level} → Cat {!!} {!!}
catOfSMC {n = n} {m = m} = MkCat
  cc
  {!!} -- monoidal functor
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
