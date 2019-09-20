open import Category
open import Monoidal
module Para {n m} {cat : Cat n m} {mc : Monoidal cat} where

open import Level
open import Function using (flip)
open import Data.Product
open import IO
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
open Cat.Isomorphism

module cat = Cat cat
open cat
module mc = Monoidal.Monoidal mc
open mc

_∘ₚ'_ : {a b c p q : obj}
  → (q ⊗ₒ b) hom c
  → (p ⊗ₒ a) hom b
  → ((q ⊗ₒ p) ⊗ₒ a) hom c
_∘ₚ'_ {a = a} {b = b} {c = c} {p = p} {q = q} g f
  =               begin→⟨ ((q ⊗ₒ p) ⊗ₒ a) ⟩
  αₒ                  →⟨ (q ⊗ₒ(p ⊗ₒ a)) ⟩
  id ⊗ₘ f            →⟨ (q ⊗ₒ    b)     ⟩
  g                   →⟨    c              ⟩end

_∘ₚ_ :  {a b c : obj}
  → Σ obj (λ q → (q ⊗ₒ b) hom c)
  → Σ obj (λ p → (p ⊗ₒ a) hom b)
  → Σ obj (λ r → (r ⊗ₒ a) hom c)
_∘ₚ_ {a = a} {b = b} {c = c} (q , g) (p , f) = (q ⊗ₒ p) , g ∘ₚ' f


-- make operators for reasoning in Para?

paraLeftId : {a b : obj} {f : Σ obj (λ p → (p ⊗ₒ a) hom b)}
  → (𝟙 , λₒ) ∘ₚ f ≡ f
paraLeftId {a = a} {b = b} {f = p , f} =
  begin
    (𝟙 , λₒ) ∘ₚ (p , f)
  ≡⟨     {!!}     ⟩
      p , f
  ∎

-- TODO quotients?
para : (v : SymmetricMonoidal mc) → Cat n (n ⊔ m)
Cat.obj (para v)      = obj
Cat._hom_ (para v)    = λ a b → Σ obj (λ p → (p ⊗ₒ a) hom b )
Cat.id (para v)       = 𝟙 , λₒ
Cat._∘_ (para v)      = _∘ₚ_
Cat.left-id (para v)  = paraLeftId
Cat.right-id (para v) = {!!}
Cat.assoc (para v)    = {!!}
