open import Level
open import Function using (flip)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category

module Shapes {n m} (cat : Cat n m) where
  open Cat cat

  record CommutativeTriangle {a b c : obj}
    (f : a hom b)
    (g : b hom c)
    (h : a hom c)
    : Set m where
    pattern
    constructor MkCommTr
    field
      eqPaths▵ : f ● g ≡ h


  private
    variable
      a b c d : obj
      f g h i j g' h' i' f₁ g₁ h₁ i₁ f₂ g₂ h₂ i₂ : a hom b


  -- extends a commutative triangle by postcomposing
  {-
  A ---> C--i--> D
  |     /
  |    /
  |   /
  |  /
  v /
  B


  -}
  extend : CommutativeTriangle {a = a} {b = b} {c = c} f g h → (i : c hom d) → CommutativeTriangle f (g ● i) (h ● i)
  extend {f = f} {g = g} {h = h} (MkCommTr eqPaths) i = MkCommTr (f ● (g ● i) ≡⟨  sym assoc  ⟩ (f ● g) ● i ≡⟨  eqPaths ⟨●⟩refl  ⟩ h ● i ∎)

-- gluing commutative triangles side by side (two different ways of doing so!)
  {-
      B---i-->D
     / \     /
    f   h   j
   /     \ /
  A---g-->C
  -}
  glue▵→''
    : f ● h ≡ g
    → i ● j ≡ h
    → (f ● i) ● j ≡ g
  glue▵→'' {f = f} {h = h} {g = g} {i = i} {j = j} eqPaths▵₁ eqPaths▵₂ =
        (f ● i) ● j
    ≡⟨  assoc ⟩
        f ● (i ● j)
    ≡⟨  (refl⟨●⟩ eqPaths▵₂) ⟩
        f ● h
    ≡⟨  eqPaths▵₁ ⟩
        g
    ∎

  glue▵→s : CommutativeTriangle f h g
         → CommutativeTriangle i j h
         → CommutativeTriangle (f ● i) j g
  glue▵→s (MkCommTr eq₁) (MkCommTr eq₂) = MkCommTr (glue▵→'' eq₁ eq₂)

  -- gluing commutative triangles side by side
  {-
      A---j---D
     / \     /
    f   h   i
   /     \ /
  B---g---C
  -}
  glue▵→'
    : f ● g ≡ h
    → h ● i ≡ j
    → (f ● (g ● i)) ≡ j
  glue▵→' {f = f} {g = g} {h = h} {i = i} {j = j} eqPaths▵₁ eqPaths▵₂ =
        f ● (g ● i)
    ≡⟨  sym assoc ⟩
        (f ● g) ● i
    ≡⟨  eqPaths▵₁ ⟨●⟩refl ⟩
        h ● i
    ≡⟨  eqPaths▵₂ ⟩
        j
    ∎

  glue▵→ : CommutativeTriangle f g h
         → CommutativeTriangle h i j
         → CommutativeTriangle f (g ● i) j
  glue▵→ (MkCommTr eq₁) (MkCommTr eq₂) = MkCommTr (glue▵→' eq₁ eq₂)



  record CommutativeSquare {a b c d : obj}
    (f : a hom b)
    (g : b hom d)
    (h : a hom c)
    (i : c hom d)
    : Set m where
    pattern
    constructor MkCommSq
    field
      eqPaths□ : f ● g ≡ h ● i

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




  -- remove the redundant record of "CommutativeSquare" and just use its field everywhere?

  {-
  ● ---g--- ● ---g'--- ●
  |         |          |
  f         i          i'
  |         |          |
  ● ---h--- ● ---h'--- ●
  -}

  glue□↓
    : CommutativeSquare f g h i
    → CommutativeSquare i g' h' i'
    → CommutativeSquare f (g ● g') (h ● h') i'
  glue□↓ {f = f} {g = g} {h = h} {i} {g' = g'} {h' = h'} {i' = i'}
    (MkCommSq eqPaths₁) (MkCommSq eqPaths₂)
    = MkCommSq (
      
         f ● (g ● g')       ≡⟨ sym assoc ⟩
         (f ● g) ● g'       ≡⟨ cong (λ x → (g' ∘ x)) eqPaths₁ ⟩
         (h ● i) ● g'       ≡⟨ assoc ⟩
         h ● (i ● g')       ≡⟨ cong (λ x → (x ∘ h)) eqPaths₂ ⟩
         h ● (h' ● i')      ≡⟨ sym assoc  ⟩
         (h ● h') ● i'
      ∎
    )


  {-

  ● ---g₂-- ●
  |         |
  f₂        i₂
  |         |
  ● ---g₁-- ● 
  |         | 
  f₁        i₁
  |         | 
  ● ---h₁-- ● 
  -}
  
  -- glue□→
  --   : CommutativeSquare f₁ g₁ h₁ i₁
  --   → CommutativeSquare f₂ g₂ g₁ i₂
  --   → CommutativeSquare (f₁ ● f₂) g₂ h₁ (i₁ ● i₂)
  -- glue□→ (MkCommSq eqPaths₁) (MkCommSq eqPaths₂) = {!!}
    -- c1 c2 = let gg = pushComm {g' = g'} c1
    --             hh = pullComm {h = h} c2
    --         in {!!}

{-

  glue□↓
    : CommutativeSquare f g h i
    → CommutativeSquare j k l o
    → (i ≡ j)
    → CommutativeSquare f (g ● k) (h ● l) o
  glue□↓ {f = f} {g = g} {h = h} {i} {k = k} {l = l} {o = o}
    (MkCommSq eqPaths₁) (MkCommSq eqPaths₂)
    = MkCommSq (
      begin
         f ● (g ● k)       ≡⟨ sym assoc ⟩
         (f ● g) ● k       ≡⟨ cong (λ x → (k ∘ x)) eqPaths₁ ⟩
         (h ● i) ● k       ≡⟨ assoc ⟩
         h ● (i ● k)       ≡⟨ cong (λ x → (x ∘ h)) eqPaths₂ ⟩
         h ● (l ● m)      ≡⟨ sym assoc  ⟩
         (h ● l) ● m
      ∎
    )
  -}

  glue□↓'
    : f ● g ≡ h ● i
    → i ● g' ≡ h' ● i'
    → f ● (g ● g') ≡ (h ● h') ● i'
  glue□↓' {f = f} {g = g} {h = h} {i} {g' = g'} {h' = h'} {i' = i'} eqPaths₁ eqPaths₂
    = 
         f ● (g ● g')       ≡⟨ sym assoc ⟩
         (f ● g) ● g'       ≡⟨ cong (λ x → (g' ∘ x)) eqPaths₁ ⟩
         (h ● i) ● g'       ≡⟨ assoc ⟩
         h ● (i ● g')       ≡⟨ cong (λ x → (x ∘ h)) eqPaths₂ ⟩
         h ● (h' ● i')      ≡⟨ sym assoc  ⟩
         (h ● h') ● i'
      ∎
