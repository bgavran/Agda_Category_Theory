{-# OPTIONS --allow-unsolved-metas #-}
module SetInstance where

open import Data.Product
open import Level
open import Function using (flip; _∘′_) renaming (id to id')
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category

𝕊𝕖𝕥 : {o : Level} → Cat (suc o) o
𝕊𝕖𝕥 {o = o} = MkCat
  (Set o)
  (λ a b → a → b)
  id'
  (flip _∘′_)
  refl
  refl
  refl
  λ f≡g h≡i → {!!}


oo : {o m : Level} → Cat o o → Cat o m
oo cat = {!cat!}



open import Data.Product
open import Data.List
open Data.List
open import Data.Vec
open import Data.Nat

concreteOptic : {P A B A' B' : Set }
  → Σ Set (λ M → (
                   (P × A → M × B)
                 × (M × B' → P × A')
                 )
          )
concreteOptic = {!!}

record oneOptic {j k : Level} (P A B A' B' : Set j) : Set ((Level.suc j) Level.⊔ (Level.suc k)) where
  constructor MkOptic
  field
    M : Set j
    l : P × A → M × B
    r : M × B' → P × A'

ttt : {k : Level} → Set k → Set k → Vec (Set k) 2
ttt X Y = X ∷ Y ∷ []

buildOptic' : {j k : Level} {P A B A' B' : Set j}
  → oneOptic {j = j} {k = k} P A B A' B'
  → (n : ℕ)
  → oneOptic {j = j} {k = k} P (Vec A n) (Vec B n) (Vec A' n) (Vec B' n)
buildOptic' {k = k} {P = P} optic ℕ.zero = MkOptic P ((λ {(p , []) → p , []})) (λ {(p , []) → p , []})
buildOptic'         optic (ℕ.suc n) = let (MkOptic MS ls rs) = buildOptic' optic n
                                      in MkOptic {!!}
                                          (λ { (p , a ∷ as) → let (ms , bs) = ls (p , as)
                                                              in {!!}})
                                          (λ { (m , b' ∷ b's) → let t = rs
                                                                in {!!}})

-- record OpticN {j : Level} (P A B A' B' : Set j) (n : ℕ): Set (Level.suc j) where
-- constructor MkOpticN
-- field
-- MS : Set j
-- ls : P × (Vec A n) → Vec MS n × (Vec B n)
-- rs : (Vec MS (n + 1)) × (Vec B' n) → P × (Vec A' n)


--buildOptic : {j : Level} {P A B A' B' : Set j}
--  → oneOptic P A B A' B' → (n : ℕ) → OpticN P A B A' B' n
--buildOptic {P = P} optic ℕ.zero = MkOpticN P ((λ { (p      , []) → p ∷ [] , []})) (λ { (p ∷ [] , []) → p , []})
--buildOptic optic@(MkOptic M l r) (ℕ.suc n) = let (MkOpticN MS ls rs) = buildOptic optic n
--                                              in MkOpticN M
--                                                 (λ { (p , a ∷ as) → let (ms , bs) = ls (p , as)
--                                                                     in {!!}})
--                                                 (λ { (m ∷ ms , b' ∷ b's) → let t = rs
--                                                                            in {!!}})
