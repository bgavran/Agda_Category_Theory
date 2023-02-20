{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (Lift)
-- open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit)
open import Data.Unit using (⊤; tt) -- for the terminal category
open import Data.Empty using (⊥) -- for the initial category
open import Function renaming (id to idff)

open import Category
open import Functor

open import AgdaCategories

-- open import Terminal -- probably should move this proof of terminality of oneObjectCat to a different file

open Cat
open _Functor_

module CategoryOfCategories where

-- some stuff for testing
variable
  l : Level
  A B : Type l

apply0 : (p : I → A) → A
apply0 = λ p → p i0

refll : {a : A} → a ≡ a
refll {a = a} = λ i → a

fxt : {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g
fxt p i a = p a i

-- fxt p i0 a = p i0 a = f a
-- fxt p i1 a = p i1 a = g a


-- we've got two interval types, we've got to do some space filling? hfill?

-- F-lUnit : ∀ {o} {m} {o'} {m'} {cat₁ : Cat o m} {cat₂ : Cat o' m'} {f : cat₁ Functor cat₂} {i} {a : obj cat₁} → mapMor f (id cat₁) ≡ id cat₂
-- F-lUnit {f = f} i = {!lUnit ? ?!} -- lUnit (idLaw f) ?
 
-- leftIdFunctor : {o m o' m' : Level} → {cat₁ : Cat o m} {cat₂ : Cat o' m'} {f : cat₁ Functor cat₂} → (f ●F idFunctor) ≡ f
-- leftIdFunctor {cat₂ = cat₂} {f = f} = λ i → MkFunctor (mapObj f) (mapMor f) F-lUnit {!!}

leftIdFunctor : {o m o' m' : Level} → {cat₁ : Cat o m} {cat₂ : Cat o' m'} {f : cat₁ Functor cat₂} → (f ●F idFunctor) ≡ f
leftIdFunctor {cat₁ = cat₁} {cat₂ = cat₂} {f = f} = λ i → MkFunctor (mapObj f) (mapMor f) (λ {a} → {!lemma i!}) {!!}
  where lemma : {a : obj cat₁} → Path (mapMor f (id cat₁ {a}) ≡ id cat₂ {mapObj f a}) (idLaw f ∙ refl) (idLaw f)
        lemma = {!!}




-- Even though we had previously defined a Functor which can go between categories between different levels, here all functors map between categories of levels o and m
ℂ𝕒𝕥 : (o m : Level) → Cat (suc o ⊔ suc m) (o ⊔ m)
ℂ𝕒𝕥 o m = MkCat
  (Cat o m)
  _Functor_
  idFunctor
  _●F_
  leftIdFunctor
  {!!}
  {!!}
  {!!}


ᵒᵖ : {o m : Level} → (ℂ𝕒𝕥 o m) Functor (ℂ𝕒𝕥 o m)
ᵒᵖ = MkFunctor
  (λ c → (MkCat (obj c) (flip (_hom_ c)) (id c) (flip (_●_ c)) (right-id c) (left-id c) (sym (assoc c)) (flip (●-resp-≡ c))))
  (λ F → MkFunctor (mapObj F) (mapMor F) (idLaw F) (λ f g → compLaw F g f))
  (λ {a = cat} → λ i → MkFunctor (λ x → x) (λ x → x) (λ i₁ → id cat) λ f g i₁ → cat [ g ● f ])
  (λ {a = a} {b = b} {c = c} F G → λ i → MkFunctor
    (λ x → mapObj G (mapObj F x))
    (λ f → mapMor G (mapMor F f))
    (λ i₁ → let t = mapMor G (mapMor F (id a)) in {!t!})
    λ f g i₁ → {!c!} [ g ● f ])


_ᵒᵖᶜ : {o m : Level} → (cat : Cat o m) → Cat o m
cat ᵒᵖᶜ = mapObj ᵒᵖ cat


_ᵒᵖᶠ : {o m : Level} {cat₁ cat₂ : Cat o m} → (f : cat₁ Functor cat₂) → ((cat₁ ᵒᵖᶜ) Functor (cat₂ ᵒᵖᶜ))
f ᵒᵖᶠ = mapMor ᵒᵖ f

disc : {n : Level} → Set n → Cat n n
disc {n = n} s = MkCat
  s
  (λ a b → a ≡ b) -- this is like  kron : {n : Level} {s : Set n} → s → s → Set n , i.e. δ : Set × Set → 2 ↦ ((a, a) ↦ 1 | (a, _) ↦ 0)
  (λ {a} → refl)
  (λ f g → f ∙ g)
  {!!}
  {!!}
  {!!}
  {!!}

disc' : {o : Level} → (𝕋𝕪𝕡𝕖 o) Functor (ℂ𝕒𝕥 o o)
disc' {o} = MkFunctor
  (disc {o})
  (λ f → MkFunctor f {!!} {!!} {!!})
  {!!}
  {!!}



-- terminal category
oneObjectCat : {o m : Level} → Cat o m
oneObjectCat {o = o} {m = m} = MkCat
  (Lift o ⊤)
  (λ a b → Lift m ⊤)
  (lift tt)
  (λ _ _ → lift tt)
  refl
  refl
  refl
  λ _ _ → refl


-- oneObjectCatTerminal : {o m : Level} → Terminal {cat = ℂ𝕒𝕥} oneObjectCat
-- oneObjectCatTerminal =
--   MkTerminal (λ anyCat → MkFunctor (λ x → lift tt) (λ x → lift tt) refl λ f g → refl)
--   (MkCommTr {!!})


-- name : {o m : Level} → Cat o m → oneObjectCat {o = o} {m = m} Functor ℂ𝕒𝕥 {o = o} {m = m}
-- name cat = MkFunctor (λ x → cat) (λ x → idFunctor) refl λ f g → refl

emptyCat : {o m : Level} → Cat o m
emptyCat {o = o} {m = m} = MkCat
  (Lift o ⊥)
  (λ a b → Lift m ⊥)
  (lift {!()!})  -- ??
  -- λ { { lift () } }
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}


FamInd : {o : Level} → ((𝕋𝕪𝕡𝕖 o) ᵒᵖᶜ) Functor (ℂ𝕒𝕥 (suc o) o)
FamInd {o} = MkFunctor
  (Fam (𝕋𝕪𝕡𝕖 o))
  (λ f → MkFunctor (λ a' x → a' (f x)) {!!} {!!} {!!})
  {!!}
  {!!}



Fam0Ind : {o : Level} → ((𝕋𝕪𝕡𝕖 o) ᵒᵖᶜ) Functor (ℂ𝕒𝕥 (suc o) o)
Fam0Ind {o} = MkFunctor
  (Fam0 (𝕋𝕪𝕡𝕖 o))
  {!!}
  {!!}
  {!!}
