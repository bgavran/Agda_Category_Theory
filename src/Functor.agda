module Functor where

open import Level
open import Function renaming (id to id→; _∘_ to _●_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category

private
  variable n m n' m' n'' m'' : Level

record _Functor_ (cat1 : Cat n m) (cat2 : Cat n' m') : Set (n ⊔ m ⊔ n' ⊔ m') where
  constructor MkFunctor
  open Cat renaming (_∘_ to _∘₁_)
  field
    mapObj : obj cat1 -> obj cat2
    mapMor : {a b : obj cat1} -> cat1 [ a , b ] -> cat2 [ mapObj a , mapObj b ]
    idLaw : {a : obj cat1} -> mapMor (id cat1) ≡ id cat2 {mapObj a}
    compLaw : {a b c : obj cat1}
      -> (f : cat1 [ a , b ])
      -> (g : cat1 [ b , c ])
      -> mapMor (cat1 [ g ∘ f ]) ≡ cat2 [(mapMor g) ∘ (mapMor f) ]

idFunctor : {cat : Cat n m} -> cat Functor cat
idFunctor = record
  { mapObj = id→ ;
    mapMor = id→;
    idLaw = refl ;
    compLaw = λ _ _ → refl }


_functorComp_ : ∀ {cat1 : Cat n m} -> {cat2 : Cat n' m'} -> {cat3 : Cat n'' m''}
  -> (g :              cat2 Functor cat3)
  -> (f : cat1 Functor cat2)
  -> (    cat1        Functor       cat3)
_functorComp_ {cat1 = cat1} {cat2 = cat2} {cat3 = cat3}
  (MkFunctor mapObj₂ mapMor₂ idLaw₂ compLaw₂)
  (MkFunctor mapObj₁ mapMor₁ idLaw₁ compLaw₁)
  = MkFunctor
    (mapObj₂ ● mapObj₁)
    (mapMor₂ ● mapMor₁)
    idLaw'
    compLaw'
  where
  open Cat
  idLaw' : {a : obj cat1} → mapMor₂ (mapMor₁ {a} {a} (id cat1)) ≡ id cat3
  idLaw' {a = a} =
    begin
      mapMor₂ (mapMor₁ (id cat1))
    ≡⟨ cong mapMor₂ idLaw₁ ⟩
       mapMor₂ (id cat2)
    ≡⟨ idLaw₂ ⟩
       id cat3
    ∎

  compLaw' : {a b c : obj cat1}
    → (f : cat1 [ a , b ])
    → (g : cat1 [ b , c ])
    → mapMor₂ (mapMor₁ (cat1 [ g ∘ f ])) ≡ cat3 [ mapMor₂ (mapMor₁ g) ∘ mapMor₂ (mapMor₁ f) ]
  compLaw' f g =
    begin
      mapMor₂ (mapMor₁ (cat1 [ g ∘ f ]))
    ≡⟨ (cong (mapMor₂) (compLaw₁ f g))    ⟩
      mapMor₂ (cat2 [(mapMor₁ g) ∘ (mapMor₁ f) ] )
    ≡⟨ (compLaw₂ (mapMor₁ f) (mapMor₁ g)) ⟩
      cat3 [ mapMor₂ (mapMor₁ g) ∘ mapMor₂ (mapMor₁ f) ]
    ∎

open Cat
open _Functor_
constFunctor : {cat1 cat2 : Cat n m} → (a : obj cat2) → cat1 Functor cat2
constFunctor {cat2 = cat2} d = MkFunctor
  (λ _ → d)
  (λ _ → id cat2)
  refl
  (λ _ _ → sym (left-id cat2))

