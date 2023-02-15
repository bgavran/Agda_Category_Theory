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
    pos : Set n
    dir : pos → Set n
    tgt : (v : pos) → (d : dir v) → pos
    id : (v : pos) → dir v
    eqq : (v : pos) → v ≡ tgt v (id v)


{-
Set → Cat
-- GNN : (G : ReflexiveGraph n) → IndexedContainer (V G) (V G)

{-
BF
E+E--∇_e ---> E
 |            |
 src + E      π
 v            v
V + E         V

-}


Things you can do to a question:
* Generalise it (the kind of thinking the answer to that particular question induces has nothing to do with that particular question; it applies in a more general setting)


The coend of a functor F:Cᵒᵖ×C→Set is the same as its colimit weighted by Hom_c.
But we also know that ∫F is the same as colim π;F, where π:El(Hom_c)→Cᵒᵖ×C.

Are you saying this works in general - a weighted co


Category of elements of F:C→Set? Oh you mean the colimit of F weighted by X↦X\C

Ah, so the adjunction π₀ ⊣ discr between Cat and Set via the enriched base change gives to a local adjunction π₀* ⊣* discr* between 2-Cat and Cat?

l:X×Y→ℝ

(A, A') → (B, B') → (C, C')
[C', B'] ⊗ [B', A']
C' → A'

∘ : [C', B'] ⊗ [B', A'] → [C', A']


-}
