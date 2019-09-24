{-# OPTIONS --allow-unsolved-metas #-}
module Product where

open import Data.Product
open import Level
open import Function using (flip) renaming (_∘_ to _∙_)
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor

open Cat
open _Functor_

private
  variable
    n m n' m' : Level
    c₁ c₂ d₁ d₂ : Cat n m

-- ee : ∀ {a b c d} → (a × b) ≡ (c × d) → (a ≡ c × b ≡ d)
-- ee lr = {!!} , {!!}


_X_ : (Cat n m) → (Cat n' m') → Cat (n ⊔ n') (m ⊔ m')
obj (c₁ X c₂) = (obj c₁ × obj c₂)
_hom_ (c₁ X c₂) (a₁ , a₂) (b₁ , b₂) = (a₁ hom₁ b₁) × (a₂ hom₂ b₂)
  where _hom₁_ = _hom_ c₁
        _hom₂_ = _hom_ c₂
id (c₁ X c₂) = id c₁ , id c₂
_∘_ (c₁ X c₂) = zip (_∘_ c₁) (_∘_ c₂)
left-id (c₁ X c₂) = cong₂ _,_ (left-id c₁) (left-id c₂)
right-id (c₁ X c₂) = cong₂ _,_ (right-id c₁) (right-id c₂)
assoc (c₁ X c₂) = cong₂ _,_ (assoc c₁) (assoc c₂)
∘-resp-≡ (c₁ X c₂) = {!!}
-- ∘-resp-≡ (c₁ X c₂) {h = h , h'} {i = i , i'} {f = f , f'} {g = g , g'} x y
--   = let t1 = ∘-resp-≡ c₁ {h = h} {i = i} {f = f} {g = g}
--         t2 = ∘-resp-≡ c₂ {h = h'} {i = i'} {f = f'} {g = g'}
--         tt = (zip t1 t2) x y
--     in {! !}

productAssociatorₗ : {cat1 : Cat n m} → {cat2 : Cat n m} → {cat3 : Cat n m}
  → ((cat1 X cat2) X cat3) Functor (cat1 X (cat2 X cat3))
productAssociatorₗ = MkFunctor
  (< proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > > )
  (< proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > > )
  refl
  λ _ _ → refl

productAssociatorᵣ : {cat1 : Cat n m} → {cat2 : Cat n m} → {cat3 : Cat n m}
  → (cat1 X (cat2 X cat3)) Functor ((cat1 X cat2) X cat3)
productAssociatorᵣ = MkFunctor
  < < proj₁ , proj₁ ∙ proj₂ > , proj₂ ∙ proj₂ >
  < < proj₁ , proj₁ ∙ proj₂ > , proj₂ ∙ proj₂ >
  refl
  λ _ _ → refl


_𝕏_ : (c₁ Functor d₁) → (c₂ Functor d₂) → (c₁ X c₂) Functor (d₁ X d₂)
mapObj (F 𝕏 G) (a , a') = mapObj F a , mapObj G a'
mapMor (F 𝕏 G) (f , g) = mapMor F f , mapMor G g
idLaw (F 𝕏 G) = cong₂ _,_ (idLaw F) (idLaw G)
compLaw (F 𝕏 G) (f₁ , f₂) (g₁ , g₂) = cong₂ _,_ (compLaw F f₁ g₁) (compLaw G f₂ g₂)



_/\_ : {cat1 cat2 cat3 : Cat n m}
  → cat1 Functor  cat2
  → cat1 Functor         cat3
  → cat1 Functor (cat2 X cat3)
mapObj (F /\ G) = λ a → mapObj F a , mapObj G a
mapMor (F /\ G) = λ f → mapMor F f , mapMor G f
idLaw (F /\ G) = cong₂ _,_ (idLaw F) (idLaw G)
compLaw (F /\ G) f g = cong₂ _,_ (compLaw F f g) (compLaw G f g)


swapFunctor : {cat1 cat2 : Cat n m} → (cat1 X cat2) Functor (cat2 X cat1)
mapObj swapFunctor = swap
mapMor swapFunctor = swap
idLaw swapFunctor = refl
compLaw swapFunctor = λ _ _ → refl
