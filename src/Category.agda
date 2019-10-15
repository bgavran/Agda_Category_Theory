module Category where

open import Level
open import Function using (flip)
open import IO
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Cat (n m : Level) : Set (suc (n ⊔ m)) where
  constructor MkCat
  infix 4 _hom_
  infixr 9 _∘_
  infixl 9 _●_ -- associate to the left because of reversal of the arguments
  infix 10  _[_,_] _[_∘_]

  field
    obj : Set n
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

  op : Cat n m
  op = record
    { obj = obj
    ; _hom_ = flip _hom_
    ; id = id
    ; _●_ = flip _●_
    ; left-id = right-id
    ; right-id = left-id
    ; assoc = sym assoc
    ; ●-resp-≡ = flip ●-resp-≡
    }


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

  assoc₂ : {a b c d e : obj}
    {f : a hom b}
    {g :       b hom c}
    {h :             c hom d}
    {i :                   d hom e}
    → ((f ● g) ● h) ● i ≡ f ● (g ● (h ● i))
  assoc₂ = trans assoc assoc

  assoc₃ : {a b c d e x : obj}
    {f : a hom b}
    {g :       b hom c}
    {h :             c hom d}
    {i :                   d hom e}
    {j :                         e hom x}
    → (((f ● g) ● h) ● i) ● j ≡ f ● (g ● (h ● (i ● j)))
  assoc₃ = trans assoc assoc₂

  monomorphism : {b c : obj}
    → (h : b hom c) -> Set (n ⊔ m)
  monomorphism {b = b} h = {a : obj} → {f g : a hom b} → f ● h ≡ g ● h → f ≡ g
