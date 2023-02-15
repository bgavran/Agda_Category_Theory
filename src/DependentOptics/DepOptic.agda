open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import DependentOptics.DepLens

module DependentOptics.DepOptic {o m r : Level} where


-- We're working here outside of the ambient Agda library

-- record Unerase (A : Set) (@0 a : A) : Set where
--   field
--     b : A
--     @0 p : a ≡ b

-- with axiom K I can define this, since K includes extra info that equality is always refl
-- f : {A : Set} → (a a' : A) → (@0 _ : a ≡ a') → a ≡ a'
-- f a a' p = {!!}

-- record Test (A : Set) (B : (@0 a : A) → Set) : Set where
--   field
--     f : (@0 a : A) → B a

record DepOptic {r : Level} (Inp Out : Cont0 {o} {m}) : Set (suc (o ⊔ m ⊔ r)) where
  constructor MkDepOptic
  open Cont0 Inp renaming (pos0 to A; dir0 to A')
  open Cont0 Out renaming (pos0 to B; dir0 to B')
  field
    res : (@0 _ : A) → (@0 _ : B) → Set r
    fwd : (a : A) → Σ B (λ b → res a b)
    bwd : {@0 a : A} → {@0 b : B} → res a b → B' b → A' a

i : Cont0 {o} {m} → Cont {o} {m}
i (MkCont0 A A') = MkCont A (\a → A' a)

record ResidualProof {l : Level} (A B : Set l) (f : A → B) (@0 a : A) (@0 b : B) : Set l where
  constructor MkResidualProof
  field
    a₀ : A
    @0 p : a ≡ a₀
    @0 q : b ≡ f a


-- depLens2DepOptic : (Inp Out : Cont0 {o} {m}) → DepLens (i Inp) (i Out) → DepOptic Inp Out
-- depLens2DepOptic (MkCont0 A A') (MkCont0 B B') (MkDepLens f f') = MkDepOptic
--    (λ a b → ResidualProof A B f a b )
--    (λ a → (f a , MkResidualProof a refl refl))
--    (λ (MkResidualProof a₀ p q) b' → let t = f' {a = a₀}
--                                         g = cong {!!} {!!} -- (  {!!} ≡⟨ {!!} ⟩ {!!} ∎)
--                                     in {!!})



-- i : {A B : Set} {B : A → Set} → (f : (@0 a : A) → B a) → ((a : A) → B a)
-- i f a = f a

-- j : {A : Set} → (@0 a : A) → A
-- j a = a
