{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import Algebra.Bundles

open import Cubical.Core.Everything
-- open import Cubical.Foundations.Prelude

open import Category

module IndexedContainers {n m : Level} where

record IndexedContainer (I O : Set n) : Set (suc n) where
  constructor MkIndCont
  field
    S : O -> Set n
    P : (o : O) → S o → Set n
    r : (o : O) → (s : S o) → (p : P o s) → I

module reindexSemiring
  (semiring : Semiring n m)
  where

  open Semiring semiring renaming (Carrier to R)

  ⊗ : {X : Set n} → (X → R) → R
  ⊗ f = {!!}  -- using semiring *

  ⊕ : {X : Set n} → (X → R) → R
  ⊕ f = {!!}  -- using semiring +

  reindex : {I O : Set n}  → IndexedContainer I O → (f : I → R) → (O → R)
  reindex {I} {O} (MkIndCont S P r) f = S₊ (Pₓ (r* f))
    where
    r* : (f : I → R) → (o : O) → (s : S o) (p : P o s) → R
    r* f o s p = f (r o s p)

    Pₓ : ((o : O) → (s : S o) (p : P o s) → R) → (o : O) → (s : S o) → R
    Pₓ g o s = ⊗ {X = (P o s)} (g o s)

    S₊ : ((o : O) → (s : S o) → R) → (O → R)
    S₊ h o = ⊕ {X = (S o)} (h o)

record ReflexiveGraph : Set (suc n) where
  constructor MkRflxGraph
  field
    V : Set n
    dir : V → Set n
    tgt : (v : V) → (d : dir v) → V
    id : (v : V) → dir v
    eqq : (v : V) → v ≡ tgt v (id v)

GNN : (G : ReflexiveGraph n) → ?
