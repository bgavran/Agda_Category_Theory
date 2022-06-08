{-# OPTIONS --allow-unsolved-metas #-}

module Product where

open import Data.Product
open import Level
open import Function using (flip) renaming (_∘_ to _∙_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import NaturalTransformation

open Cat
open import Shapes
open Shapes.CommutativeSquare
open _Functor_
open _NatTrans_

private
  variable
    n m n' m' n'' m'' n''' m''' : Level
    c₁ c₂ c₃ c₄ d₁ d₂ : Cat n m

_X_ : (Cat n m) → (Cat n' m') → Cat (n ⊔ n') (m ⊔ m')
obj (c₁ X c₂) = (obj c₁ × obj c₂)
_hom_ (c₁ X c₂) (a₁ , a₂) (b₁ , b₂) = (a₁ hom₁ b₁) × (a₂ hom₂ b₂)
  where _hom₁_ = _hom_ c₁
        _hom₂_ = _hom_ c₂
id (c₁ X c₂) = id c₁ , id c₂
_●_ (c₁ X c₂) = zip (_●_ c₁) (_●_ c₂)
left-id (c₁ X c₂) = cong₂ _,_ (left-id c₁) (left-id c₂)
right-id (c₁ X c₂) = cong₂ _,_ (right-id c₁) (right-id c₂)
assoc (c₁ X c₂) = cong₂ _,_ (assoc c₁) (assoc c₂)
●-resp-≡ (c₁ X c₂) = {!!} -- x y = cong₂ (_,_) -- (●-resp-≡ c₁ (cong proj₁ x) (cong proj₁ y))
                                            -- (●-resp-≡ c₂ (cong proj₂ x) (cong proj₂ y))

Π₁ : (c₁ X c₂) Functor c₁
Π₁ = MkFunctor
  (λ (a , b) → a)
  (λ (a , b) → a)
  refl
  λ _ _ → refl

Π₂ : (c₁ X c₂) Functor c₂
Π₂ = MkFunctor
  (λ (a , b) → b)
  (λ (a , b) → b)
  refl
  λ _ _ → refl

productAssociatorₗ : ((c₁ X c₂) X c₃) Functor (c₁ X (c₂ X c₃))
productAssociatorₗ = MkFunctor
  (λ ((a , b) , c) → (a , (b , c)) )
  (λ ((f , g) , h) → (f , (g , h)) )
  refl
  (λ _ _ → refl)

productAssociatorᵣ : (c₁ X (c₂ X c₃)) Functor ((c₁ X c₂) X c₃)
productAssociatorᵣ = MkFunctor
  (λ (a , (b , c)) → ((a , b) , c) )
  (λ (f , (g , h)) → ((f , g) , h) )
  refl
  (λ _ _ → refl)

-- project middle two
-- for some reason there have to be a lot of implicit arguments
π₂₃ : {c₁ : Cat n m} {c₂ : Cat n' m'} {c₃ : Cat n'' m''} {c₄ : Cat n''' m'''}
  → ((c₁ X c₂) X (c₃ X c₄)) Functor (c₂ X c₃)
π₂₃ {c₁ = c₁ }{c₂ = c₂} {c₃ = c₃} {c₄ = c₄} =
  ((productAssociatorᵣ{c₁ = (c₁ X c₂)} {c₂ = c₃} {c₃ = c₄} ●F
  Π₁ {c₁ = ((c₁ X c₂) X c₃)}{c₂ = c₄}) ●F
  productAssociatorₗ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃}) ●F
  (Π₂ {c₁ = c₁} {c₂ = (c₂ X c₃)})


_𝕏_ : (c₁ Functor d₁) → (c₂ Functor d₂) → (c₁ X c₂) Functor (d₁ X d₂)
mapObj (F 𝕏 G) (a , a') = mapObj F a , mapObj G a'
mapMor (F 𝕏 G) (f , g) = mapMor F f , mapMor G g
idLaw (F 𝕏 G) = cong₂ _,_ (idLaw F) (idLaw G)
compLaw (F 𝕏 G) (f₁ , f₂) (g₁ , g₂) = cong₂ _,_ (compLaw F f₁ g₁) (compLaw G f₂ g₂)



-- the symbol should be read bottom to top as if branching
_\/_ : c₁ Functor  c₂
     → c₁ Functor       c₃
     → c₁ Functor (c₂ X c₃)
mapObj (F \/ G) = λ a → mapObj F a , mapObj G a
mapMor (F \/ G) = λ f → mapMor F f , mapMor G f
idLaw (F \/ G) = cong₂ _,_ (idLaw F) (idLaw G)
compLaw (F \/ G) f g = cong₂ _,_ (compLaw F f g) (compLaw G f g)

swapFunctor : (c₁ X c₂) Functor (c₂ X c₁)
mapObj swapFunctor = swap
mapMor swapFunctor = swap
idLaw swapFunctor = refl
compLaw swapFunctor = λ _ _ → refl


{-
|   |   |   |
|    \ /    |
|     X‌     |
|    / \    |
|   |   |   |
-}

|⇆| : {a : Set n} {b : Set m} {c : Set n'} {d : Set m'}
  → ((a × b) × (c × d)) → ((a × c) × (b × d))
|⇆| ((a , b) , (c , d)) = (a , c) , (b , d)

|⇆|𝕏 : {c₁ : Cat n m} {c₂ : Cat n' m'} {c₃ : Cat n'' m''} {c₄ : Cat n''' m'''}
  → ((c₁ X c₂) X (c₃ X c₄)) Functor ((c₁ X c₃) X (c₂ X c₄))
|⇆|𝕏 {c₁ = c₁ }{c₂ = c₂} {c₃ = c₃} {c₄ = c₄}
  = productAssociatorᵣ {c₁ = (c₁ X c₂)} {c₂ = c₃} {c₃ = c₄} ●F
    (productAssociatorₗ {c₁ = c₁} {c₂ = c₂} {c₃ = c₃} 𝕏 idFunctor {cat = c₄}) ●F
    ((idFunctor {cat = c₁} 𝕏 (swapFunctor {c₁ = c₂} {c₂ = c₃})) 𝕏 idFunctor {cat = c₄}) ●F
    (((productAssociatorᵣ {c₁ = c₁}  {c₂ = c₃} {c₃ = c₂} ) 𝕏 idFunctor {cat = c₄}) ●F productAssociatorₗ {c₁ = (c₁ X c₃)} {c₂ = c₂} {c₃ = c₄})


⃤ : c₁ Functor (c₁ X c₁)
⃤ = idFunctor \/ idFunctor

-- product of natural transformations
_𝕏ₙ_ : {c₁ : Cat n m} {c₂ : Cat n' m'} {c₃ : Cat n'' m''} {c₄ : Cat n''' m'''}
  → {F : c₁ Functor c₂} → {G : c₁ Functor c₂}
  → {H : c₃ Functor c₄} → {I : c₃ Functor c₄}
  → (α : F NatTrans G) → (β : H NatTrans I)
  → ((F 𝕏 H) NatTrans (G 𝕏 I))
α 𝕏ₙ β = MkNatTrans
  (η α , η β)
  (MkCommSq (cong₂ _,_ (eqPaths□ (naturality α)) (eqPaths□ (naturality β))))
