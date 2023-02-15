module Test where

open import Level
open import Function using (flip)
open import Data.Bool.Base
open import Data.Nat.Base hiding (suc)
open import Data.Integer.Base hiding (suc)
open import Data.Unit.Base
-- open import Data.Fin.Base
open import Data.List.Base
open import Data.Product
open import Agda.Builtin.Int
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

-- if n >= 1 then ℕ else Bool
-- t : Int  → Set
-- t n = if (n ≤ᵇ (pos 5)) then Int else Int × Int

-- f : (n : ℕ) → t n
-- f n with (suc n ≤ᵇ n)
-- f n    | true = n
-- f n    | false = pos n

--f n = if (suc n ≤ᵇ n) then {!!} else {!!} 

B : Set → Set
B X = List X

g : (@0 x : Set) → B x
g _ = []

-- record Cont {n : Level} (a : Set n) : Set (suc n) where
--   field
--     o : a → Set n
--     -- m : (a b : o) → Set n

-- ff : {n m : Level} (a : Set n)
--   → (a' : (a → Set n))
--   → (b' : (a → Set n)) → Set n
-- ff a a' b' = (@0 x : a) → b' x → a' x
  -- (@0 x : a) → b' x → a' x)

-- f false = []
-- f true = true ∷ false ∷ []

-- f : {A C : Set} → {B : A → Set} →
--   (f : (a : A) → B a → C) → ((a a' : A) → B a ≡ B a' → (b : B a) → f a b ≡ f a' b) → ((@0 a : A) → B a → C)
-- f = {!!}

{-
Can monad D : C → C be made dependent?

We need F:C→Cat and a dependent functor D : (c : C) → F c. To show that D truly gives us a dependent monad, we need corresponding unit and join maps.
The unit would be a map from the identity dependent natural transformation into (D, F).
And the join would be a map from the composition of (how do dependent functors compose)?

Function : A → B
Dependent function : (a : A) → B(a) (for some B(a))


-----

Functor F : C → D maps
an object (c : C) to an object F(c) of the category D

                C   C                         D      D
a morphism (f : c → c') to a morphism F(f) : F(c) → F(c') in D

A dependent functor F : (c : C) → G(c) (for some G:C→Cat) maps
an object (c : C) to an object F(c) of the category G(c)
a morphism (f : c → c') to a morphism G(f)(F(c)) → F(c') in G(c')

Nat transf. α between functors F ⇒ F' : A → A
∀ a : A  . αₐ :  F(a) → F'(a) (F(a) : A, F'(a) : A)

Dep functors F : (a : A) → D (a) and F' : (a : A) → D' (a)

Dep. nat transf between dep. functors (D : A → Cat, F : (a : A) → D(a)) ⇒ (D' : A → Cat, F' : (a : A) → D'(a))
includes a natural transformation δ:D⇒D' (which to every object a:A assigns a functor δₐ : D(a) → D'(a))
it includes a mapping which to every a:A assigns a morphism  αₐ : δₐ(F(a)) → F'(a) in D'(a)
for every a→a' 

(where F(a) : D(a), F'(a) : D(a'))



A natural transformation δ:D ⇒ D':A → Cat 

This functor maps
an object F(a):D(a) to an object δₐ(F(a)):D(a')


Function | dependent function
Functor | dependent functor

- | -
Nat transf. | dep nat. transf.

(d : D) → F c
In Set₁
D:X → Set₀
Σ_{x : X}D(x)

element of x plus a distribution
-- f : {A C : Set} → {B : A → Set} → (f : (@0 a : A) → B a → C) → Bool --(a a' : A) → f a ≡ f a'

-- f a = f a'

-- f : (@0 n : ℕ) → Σ ℕ (λ m → m ≡ n) → ℕ
-- f n (m , eqq) = {!m!}

-}
