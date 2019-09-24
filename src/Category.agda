module Category where

open import Level
open import Function using (flip)
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Cat (n m : Level) : Set (suc (n ⊔ m)) where
  constructor MkCat
  infixr 9 _∘_
  infix 10  _[_,_] _[_∘_]

  field
    obj : Set n
    _hom_ : (a b : obj) → Set m

    id : {a : obj} -> a hom a
    _∘_  : {a b c : obj}
      -> (      b hom c)
      -> (a hom b)
      -> (a    hom    c)

  _●_  : {a b c : obj}
    -> (a hom b)
    -> (      b hom c)
    -> (a    hom    c)
  _●_ f g = _∘_ g f

  _[_,_] : obj -> obj -> Set m
  _[_,_] = _hom_

  _[_∘_] : {a b c : obj}
    -> b hom c -> a hom b -> a hom c
  _[_∘_] = _∘_


  _[_●_] : {a b c : obj}
    -> a hom b -> b hom c -> a hom c
  _[_●_] = _●_


  field
    left-id  : {a b : obj} {f : a hom b} → (     f ● id ≡ f)
    right-id : {a b : obj} {f : a hom b} → (id ● f      ≡ f)
    assoc : {a b c d : obj}
      {f : a hom b}
      {g :       b hom c}
      {h :             c hom d}
      → (f ● g) ● h ≡ f ● (g ● h)
    ∘-resp-≡ : {a b c : obj} → {f g : a hom b} → {h i : b hom c}
      → f ≡ g
      → h ≡ i
      → (f ● h ≡ g ● i)


  ∘-resp-≡ₗ : {a b c : obj} → {f g : a hom b} → {h : b hom c}
    → f ≡ g
    → f ● h ≡ g ● h
  ∘-resp-≡ₗ e = ∘-resp-≡ e refl

  ∘-resp-≡ᵣ : {a b c : obj} → {f : a hom b} → {g h : b hom c}
    → g ≡ h
    → f ● g ≡ f ● h
  ∘-resp-≡ᵣ e = ∘-resp-≡ refl e

  dom : {a b : obj} -> (a hom b) -> obj
  dom {a} _ = a

  cod : {a b : obj} -> (a hom b) -> obj
  cod {b} _ = b

  op : Cat n m
  op = record
    { obj = obj
    ; _hom_ = flip _hom_
    ; id = id
    ; _∘_ = flip _∘_
    ; left-id = right-id
    ; right-id = left-id
    ; assoc = sym assoc
    ; ∘-resp-≡ = flip ∘-resp-≡
    }

  refl⟨∘⟩_ : {a b c : obj} {f g : a hom b} {h : b hom c}
    → f ≡ g → f ● h ≡ g ● h
  refl⟨∘⟩ e = ∘-resp-≡ e refl

  _⟨∘⟩refl : {a b c : obj} {f : a hom b} {g h : b hom c}
    → g ≡ h → f ● g ≡ f ● h
  e ⟨∘⟩refl = ∘-resp-≡ refl e

  infixl 2 connect
  connect : {a c : obj}
    → (b : obj) → a hom b → b hom c → a hom c
  connect b f g  = f ● g
  syntax connect b g f = f →⟨ b ⟩ g

  infix 1 begin→⟨_⟩_
  begin→⟨_⟩_ : (a : obj) → {b : obj} → a hom b → a hom b
  begin→⟨ a ⟩ f = f

  end∘ : {a : obj} → (b : obj) → a hom b → a hom b
  end∘ b f = f
  syntax end∘ b f = f →⟨ b ⟩end


  record CommutativeSquare {a b c d : obj}
    (f : a hom b)
    (g : b hom d)
    (h : a hom c)
    (i : c hom d)
    : Set m where
    constructor MkCommSq
    field
      eqPaths : f ● g ≡ h ● i


  private
    variable
      a b : obj
      f g h i g' h' i' : a hom b

  -- not really used yet
  {-
  pushComm : CommutativeSquare f g h i
    → CommutativeSquare f (g' ∘ g) h (g' ∘ i)
  pushComm {f = f} {g = g} {h = h} {i = i} {g' = g'} (MkCommSq eqPaths)
    = MkCommSq (
    begin
      (g' ∘ g) ∘ f    ≡⟨ assoc ⟩
      g' ∘ (g ∘ f)    ≡⟨ cong (λ x → (g' ∘ x)) eqPaths ⟩
      g' ∘ (i ∘ h)    ≡⟨ sym assoc ⟩
      (g' ∘ i) ∘ h
    ∎)

  -- not really used yet
  pullComm : CommutativeSquare i g' h' i'
    → CommutativeSquare (i ∘ h) g' (h' ∘ h) i'
  pullComm {i = i} {g' = g'} {h' = h'} {i' = i'} {h = h} (MkCommSq eqPaths)
    = MkCommSq (
      begin
        g' ∘ (i ∘ h)    ≡⟨ sym assoc ⟩
        (g' ∘ i) ∘ h    ≡⟨ cong (λ x → (x ∘ h)) eqPaths ⟩
        (i' ∘ h') ∘ h       ≡⟨ assoc ⟩
        i' ∘ (h' ∘ h)
      ∎)
   -}

  {-

  F A --- f---> F B

   h    c1      g

  G A --- i---> G B

   h'    c2     g'

  H A ---i'---> H B

  -}

  glue
    : CommutativeSquare f g h i
    → CommutativeSquare i g' h' i'
    → CommutativeSquare f (g ● g') (h ● h') i'
  glue {f = f} {g = g} {h = h} {i} {g' = g'} {h' = h'} {i' = i'}
    (MkCommSq eqPaths₁) (MkCommSq eqPaths₂)
    = MkCommSq (
      begin
         f ● (g ● g')       ≡⟨ sym assoc ⟩
         (f ● g) ● g'       ≡⟨ cong (λ x → (g' ∘ x)) eqPaths₁ ⟩
         (h ● i) ● g'       ≡⟨ assoc ⟩
         h ● (i ● g')       ≡⟨ cong (λ x → (x ∘ h)) eqPaths₂ ⟩
         h ● (h' ● i')      ≡⟨ sym assoc  ⟩
         (h ● h') ● i'
      ∎
    )
    -- c1 c2 = let gg = pushComm {g' = g'} c1
    --             hh = pullComm {h = h} c2
    --         in {!!}


  record Isomorphism (a : obj) (b : obj) : Set (n ⊔ m) where
    constructor MkIso
    field
      forward : a hom b
      inverse : b hom a
      leftInverseLaw  : inverse ● forward ≡ id
      rightInverseLaw : forward ● inverse ≡ id
  syntax Isomorphism a b = a ≅ b

