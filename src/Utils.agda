open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

module Utils where

private
  variable
    a b c d e ℓ p : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

-- cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
-- cong₂ f refl refl = refl

cong₃ : ∀ (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl


cong₄ : ∀ (f : A → B → C → D → E) {x y u v w z i j}
  → x ≡ y → u ≡ v → w ≡ z → i ≡ j
  → f x u w i ≡ f y v z j
cong₄ f refl refl refl refl = refl



