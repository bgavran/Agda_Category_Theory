module Category where

open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

catLvl : (o m : Level) → Level
catLvl o m = suc (o ⊔ m)

record Cat (o m : Level) : Set (catLvl o m) where
  constructor MkCat
  infix 4 _hom_
  infixr 9 _∘_
  infixl 9 _●_ -- associate to the left because of reversal of the arguments
  infix 10  _[_,_] _[_∘_]


  field
    obj : Set o
    _hom_ : (a b : obj) → Set m


    id : {a : obj} -> a hom a
    _●_  : {a b c : obj}
      -> (a hom b)
      -> (      b hom c)
      -> (a    hom    c)


  _∘_  : {a b c : obj}
    -> (      b hom c)
    -> (a hom b)
    -> (a    hom    c)
  _∘_ g f = _●_ f g

  _[_,_] : obj -> obj -> Set m
  _[_,_] = _hom_

  _[_∘_] : {a b c : obj}
    -> b hom c -> a hom b -> a hom c
  _[_∘_] = _∘_

  _[_●_] : {a b c : obj}
    -> a hom b -> b hom c -> a hom c
  _[_●_] = _●_

  -- To say that two morphims are equal we're using Agda's built in ≡
  -- We additionally need to say that composing morphisms respects equality
  field
    left-id  : {a b : obj} {f : a hom b} → (     f ● id ≡ f)
    right-id : {a b : obj} {f : a hom b} → (id ● f      ≡ f)
    assoc : {a b c d : obj}
      {f : a hom b}
      {g :       b hom c}
      {h :             c hom d}
      → (f ● g) ● h ≡ f ● (g ● h)
    ●-resp-≡ : {a b c : obj} → {f g : a hom b} → {h i : b hom c}
      → f ≡ g
      → h ≡ i
      → (f ● h ≡ g ● i)
  syntax ●-resp-≡ l r = l ⟨●⟩ r

  dom : {a b : obj} -> (a hom b) -> obj
  dom {a} _ = a

  cod : {a b : obj} -> (a hom b) -> obj
  cod {b} _ = b

  -- -- opposite category
  -- _ᵒᵖ : Cat o m
  -- _ᵒᵖ = record
  --   { obj = obj
  --   ; _hom_ = flip _hom_
  --   ; id = id
  --   ; _●_ = flip _●_
  --   ; left-id = right-id
  --   ; right-id = left-id
  --   ; assoc = sym assoc
  --   ; ●-resp-≡ = flip ●-resp-≡
  --   }


  _⟨●⟩refl : {a b c : obj} {f g : a hom b} {h : b hom c}
    → f ≡ g → f ● h ≡ g ● h
  e ⟨●⟩refl = ●-resp-≡ e refl

  _⟨●⟩refl₂ : {a b c d : obj} {f g : a hom b} {h : b hom c} {i : c hom d}
    → f ≡ g → (f ● h) ● i ≡ (g ● h) ● i
  e ⟨●⟩refl₂ = e ⟨●⟩refl ⟨●⟩refl

  _⟨●⟩refl₃ : {a b c d e : obj} {f g : a hom b} {h : b hom c} {i : c hom d} {j : d hom e}
    → f ≡ g → ((f ● h) ● i) ● j ≡ ((g ● h) ● i) ● j
  e ⟨●⟩refl₃ = e ⟨●⟩refl ⟨●⟩refl ⟨●⟩refl

  _⟨●⟩refl₄ : {a b c d e x : obj} {f g : a hom b} {h : b hom c} {i : c hom d} {j : d hom e} {k : e hom x}
    → f ≡ g → (((f ● h) ● i) ● j) ● k ≡ (((g ● h) ● i) ● j) ● k
  e ⟨●⟩refl₄ = e ⟨●⟩refl ⟨●⟩refl ⟨●⟩refl ⟨●⟩refl

  refl⟨●⟩_ : {a b c : obj} {f : a hom b} {g h : b hom c}
    → g ≡ h → f ● g ≡ f ● h
  refl⟨●⟩ e = ●-resp-≡ refl e

  infixl 2 connect
  connect : {a c : obj}
    → (b : obj) → a hom b → b hom c → a hom c
  connect b f g  = f ● g
  syntax connect b f g = f →⟨ b ⟩ g

  infix 1 begin→⟨_⟩_
  begin→⟨_⟩_ : (a : obj) → {b : obj} → a hom b → a hom b
  begin→⟨ a ⟩ f = f

  end● : {a : obj} → (b : obj) → a hom b → a hom b
  end● b f = f
  syntax end● b f = f →⟨ b ⟩end


  assoc₂ : {a b c d e : obj}
    {f : a hom b}
    {g :       b hom c}
    {h :             c hom d}
    {i :                   d hom e}
    → ((f ● g) ● h) ● i ≡ f ● (g ● (h ● i))
  assoc₂ = assoc ∙ assoc

  assoc₃ : {a b c d e x : obj}
    {f : a hom b}
    {g :       b hom c}
    {h :             c hom d}
    {i :                   d hom e}
    {j :                         e hom x}
    → (((f ● g) ● h) ● i) ● j ≡ f ● (g ● (h ● (i ● j)))
  assoc₃ = assoc ∙ assoc₂

  monomorphism : {b c : obj}
    → (h : b hom c) -> Set (o ⊔ m)
  monomorphism {b = b} h = {a : obj} → {f g : a hom b} → f ● h ≡ g ● h → f ≡ g
