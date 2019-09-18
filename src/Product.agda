module Product where

open import Data.Product
open import Level
open import Function using (flip) renaming (_∘_ to _∙_)
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Category
open import Functor

open Cat

private
  variable n m n' m' : Level

_X_ : (Cat n m) → (Cat n' m') → (Cat (n ⊔ n') (m ⊔ m'))
obj (c₁ X c₂) = (obj c₁ × obj c₂)
_hom_ (c₁ X c₂) (a₁ , a₂) (b₁ , b₂) = (a₁ hom₁ b₁) × (a₂ hom₂ b₂)
  where _hom₁_ = _hom_ c₁
        _hom₂_ = _hom_ c₂
id (c₁ X c₂) = id c₁ , id c₂
_∘_ (c₁ X c₂) = zip (_∘_ c₁) (_∘_ c₂)
left-id (c₁ X c₂) = cong₂ _,_ (left-id c₁) (left-id c₂)
right-id (c₁ X c₂) = cong₂ _,_ (right-id c₁) (right-id c₂)
assoc (c₁ X c₂) = cong₂ _,_ (assoc c₁) (assoc c₂)

productAssociator : {cat1 : Cat n m} → {cat2 : Cat n m} → {cat3 : Cat n m}
  → ((cat1 X cat2) X cat3) Functor (cat1 X (cat2 X cat3))
productAssociator = MkFunctor
  (< proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > > )
  (< proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > > )
  refl
  λ _ _ → refl
