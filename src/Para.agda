open import Category
open import Monoidal
module Para {n m} {cat : Cat n m} {mc : Monoidal cat} where

open import Level
open import Function using (flip)
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Functor
open import Product
open import NaturalTransformation
open import SymmetricMonoidal

--private
--  variable
--    n' m' n'' m'' : Level


open _Functor_
open _NatTrans_
-- open Cat.Isomorphism

module cat = Cat cat
open cat
module mc = Monoidal.Monoidal mc
open mc

_●ₚ'_ : {a b c p q : obj}
  → (p ⊗ₒ a) hom b
  → (q ⊗ₒ b) hom c
  → ((q ⊗ₒ p) ⊗ₒ a) hom c
_●ₚ'_ {a = a} {b = b} {c = c} {p = p} {q = q} f g
  =               begin→⟨ ((q ⊗ₒ p) ⊗ₒ a) ⟩
     αₘ                →⟨ (q ⊗ₒ(p ⊗ₒ a)) ⟩
  id ⊗ₘ f             →⟨ (q ⊗ₒ    b)     ⟩
  g                    →⟨    c              ⟩end

-- This should be a category?
_●ₚ_ :  {a b c : obj}
  → Σ obj (λ p → (p ⊗ₒ a) hom b)
  → Σ obj (λ q → (q ⊗ₒ b) hom c)
  → Σ obj (λ r → (r ⊗ₒ a) hom c)
_●ₚ_ {a = a} {b = b} {c = c} (p , f) (q , g) = (q ⊗ₒ p) , f ●ₚ' g


-- make operators for reasoning in Para?

paraLeftId : {a b : obj} {f : Σ obj (λ p → (p ⊗ₒ a) hom b)}
  → (𝕀 , λₘ) ●ₚ f ≡ f
paraLeftId {a = a} {b = b} {f = p , f} =
  begin
    (𝕀 , λₘ) ●ₚ (p , f)
  ≡⟨⟩
    (p ⊗ₒ 𝕀) , αₘ ● (id ⊗ₘ λₘ) ● f
  ≡⟨     {!!}     ⟩
      p , f
  ∎

-- TODO this should be bicat, or quotients should be figured out?
para : (v : SymmetricMonoidal mc) → Cat n (n ⊔ m)
Cat.obj (para v)      = obj
Cat._hom_ (para v)    = λ a b → Σ obj (λ p → (p ⊗ₒ a) hom b )
Cat.id (para v)       = 𝕀 , λₘ
Cat._●_ (para v)      = _●ₚ_
Cat.left-id (para v)  = {!!} -- paraLeftId
Cat.right-id (para v) = {!!}
Cat.assoc (para v)    = {!!}
Cat.●-resp-≡ (para v) = {!!}
