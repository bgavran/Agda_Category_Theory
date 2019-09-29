module Functor where

open import Level
open import Function renaming (id to id→; _∘_ to _∘ᶠ_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category

_●ᶠ_ : {a b c : Level} → ∀ {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c}
  → (g : (x : A) → B x)
  → (∀ {x} (y : B x) → C y)
  → ((x : A) → C (g x))
_●ᶠ_ = flip _∘ᶠ_

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
      → (f : cat1 [ a , b ])
      → (g : cat1 [ b , c ])
      → mapMor (cat1 [ f ● g ]) ≡ cat2 [(mapMor f) ● (mapMor g) ]
    -- F-resp-≡ : {a b : obj cat1} {f g : cat1 [ a , b ]}
    --   → f ≡ g
    --   → mapMor f ≡ mapMor g

idFunctor : {cat : Cat n m} -> cat Functor cat
idFunctor = record
  { mapObj = id→ ;
    mapMor = id→ ;
    idLaw = refl ;
    compLaw = λ _ _ → refl }
    -- F-resp-≡ = id→}


_∘F_ : ∀ {cat1 : Cat n m} -> {cat2 : Cat n' m'} -> {cat3 : Cat n'' m''}
  -> (g :              cat2 Functor cat3)
  -> (f : cat1 Functor cat2)
  -> (    cat1        Functor       cat3)
_∘F_ {cat1 = cat1} {cat2 = cat2} {cat3 = cat3}
  (MkFunctor mapObj₂ mapMor₂ idLaw₂ compLaw₂) --  F-resp-≡₂)
  (MkFunctor mapObj₁ mapMor₁ idLaw₁ compLaw₁) --  F-resp-≡₁)
  = MkFunctor
    (mapObj₂ ∘ᶠ mapObj₁)
    (mapMor₂ ∘ᶠ mapMor₁)
    idLaw'
    compLaw'
    -- (F-resp-≡₂ ∘ᶠ F-resp-≡₁)
  where
  open Cat
  idLaw' : {a : obj cat1} → (mapMor₁ {a} ●ᶠ mapMor₂) (id cat1) ≡ id cat3
  idLaw' {a = a} =
    begin
      (mapMor₁ {a} ●ᶠ mapMor₂) (id cat1)
    ≡⟨ cong mapMor₂ idLaw₁ ⟩
       mapMor₂ (id cat2)
    ≡⟨ idLaw₂ ⟩
       id cat3
    ∎

  compLaw' : {a b c : obj cat1}
    → (f : cat1 [ a , b ])
    → (g : cat1 [ b , c ])
    → (mapMor₁ ●ᶠ mapMor₂) (cat1 [ f ● g ]) ≡ cat3 [ (mapMor₁ ●ᶠ mapMor₂) f ● (mapMor₁ ●ᶠ mapMor₂) g ]
  compLaw' f g =
    begin
     (mapMor₁ ●ᶠ mapMor₂) (cat1 [ f ● g ])
    ≡⟨ (cong (mapMor₂) (compLaw₁ f g))    ⟩
      mapMor₂ (cat2 [ mapMor₁ f ● mapMor₁ g ] )
    ≡⟨ (compLaw₂ (mapMor₁ f) (mapMor₁ g)) ⟩
      cat3 [ (mapMor₁ ●ᶠ mapMor₂) f ● (mapMor₁ ●ᶠ mapMor₂) g ]
    ∎

_●F_ : ∀ {cat1 : Cat n m} -> {cat2 : Cat n' m'} -> {cat3 : Cat n'' m''}
  -> (f : cat1 Functor cat2)
  -> (g :              cat2 Functor cat3)
  -> (    cat1        Functor       cat3)
_●F_ = flip _∘F_

open Cat
open _Functor_
constFunctor : {cat1 cat2 : Cat n m} → (a : obj cat2) → cat1 Functor cat2
constFunctor {cat2 = cat2} d = MkFunctor
  (λ _ → d)
  (λ _ → id cat2)
  refl
  (λ _ _ → sym (left-id cat2))
  -- (λ _ → refl)
