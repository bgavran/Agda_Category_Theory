module Product where

open import Data.Product
open import Level
open import Function using (flip) renaming (_∘_ to _∙_)
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Category
open import Functor


private
  variable n m n' m' n'' m'' : Level

_X_ : (Cat n m) → (Cat n' m') → (Cat (n ⊔ n') (m ⊔ m'))
_X_ (MkCat obj₁ _hom₁_ id₁ _∘₁_ left-id₁ right-id₁ assoc₁)
        (MkCat obj₂ _hom₂_ id₂ _∘₂_ left-id₂ right-id₂ assoc₂)
  = MkCat
  (obj₁ × obj₂)
  (λ a b → (proj₁ a) hom₁ (proj₁ b) × (proj₂ a) hom₂ (proj₂ b))
  (λ {a} → id₁ {proj₁ a} , id₂ {proj₂ a} )
  (zip _∘₁_ _∘₂_)
  (λ {a} {b} {f} → cong₂ _,_ (left-id₁ {f = proj₁ f}) (left-id₂ {f = proj₂ f}))
  (λ {a} {b} {f} → cong₂ _,_ (right-id₁ {f = proj₁ f}) (right-id₂ {f = proj₂ f}))
  (λ {a} {b} {c} {d} {f = f} {g = g} {h = h}
  → cong₂ _,_ (assoc₁ {f = proj₁ f} {g = proj₁ g} {h = proj₁ h})
              (assoc₂ {f = proj₂ f} {g = proj₂ g} {h = proj₂ h}))


productAssociator : {cat1 : Cat n m} → {cat2 : Cat n m} → {cat3 : Cat n m}
  → ((cat1 X cat2) X cat3) Functor (cat1 X (cat2 X cat3))
productAssociator = MkFunctor
  (< proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > > )
  (< proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > > )
  refl
  λ _ _ → refl
