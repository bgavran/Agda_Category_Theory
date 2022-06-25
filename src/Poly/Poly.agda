module Poly.Poly where 
open import Cubical.Foundations.Everything renaming (Iso to _≅_)
open import Cubical.Data.Sum.Base 
open import Cubical.Data.Prod
open import Cubical.Data.Unit


record Poly : Set₁ where
  constructor _▹_
  field
    pos : Set
    dir : pos -> Set

_；_ : {A B C : Set} → (A → B) → (B → C) → A → C
f ； g = λ x → (g (f x))

-- maps poly to the F₀ map of a Set Endofunctor
⦅_⦆ : Poly → Set → Set
⦅ P ▹ D ⦆ X = Σ[ p ∈ P ] (D p → X)

_⊎ₚ_ : Poly → Poly → Poly
p ⊎ₚ q = (pos ⊎ pos') ▹ λ {(inl x) → dir x
                         ; (inr x) → dir' x}
    where 
        open Poly p 
        open Poly q renaming (pos to pos'; dir to dir')

-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ
_×ₚ_ : Poly → Poly → Poly
p ×ₚ q = (pos × pos') ▹ λ{(x , y) →  dir x ⊎ dir' y} 
    where 
        open Poly p 
        open Poly q renaming (pos to pos'; dir to dir')
        
--tensor \ox
-- Ayᴮ × Cyᴰ = ACyᴮᴰ
_⊗ₚ_ : Poly → Poly → Poly
p ⊗ₚ q = (pos × pos') ▹ λ{(x , y) → dir x × dir' y}
    where 
        open Poly p 
        open Poly q renaming (pos to pos'; dir to dir')

-- composition product
_◃_ : Poly → Poly → Poly
(p⑴ ▹ p[_] ) ◃ (q⑴ ▹ q[_]) = pos ▹ dir
    where 
        pos = (Σ[ i ∈ p⑴ ] (p[ i ] → q⑴))

        dir : pos → Type
        dir (i , ĵ) = Σ[ d ∈ p[ i ] ]  q[ (ĵ d) ]


-- map between poly
record Poly[_,_](p q : Poly) : Set where
    constructor _⇒ₚ_
    open Poly p 
    open Poly q renaming (pos to pos'; dir to dir')
    field
        onPos : pos → pos'
        onDir : (p : pos) → dir' (onPos p) → dir p

-- composition of poly maps
_⇒∘ₚ_ : {p q r : Poly} → Poly[ p , q ] → Poly[ q , r ] → Poly[ p , r ]
_⇒∘ₚ_ {p} {q} {r} pq qr = (onPos ； onPos') -- forward composition on positions
                            ⇒ₚ 
                          λ ppos → let 
                                    qpos = onPos ppos
                                    in onDir ppos ∘ onDir' qpos -- backward composition on directions
    where 
        open Poly[_,_] pq 
        open Poly[_,_] qr renaming(onPos to onPos'; onDir to onDir')

yˢ : (S : Set) → Poly
yˢ S = Unit ▹ λ _ → S

yoneda : {S : Set} → {q : Poly} → Poly[ yˢ S , q ] ≅  ⦅ q ⦆ S
yoneda {S} {q} = i 
    where 
        open _≅_ 

        i : Poly[ yˢ S , q ] ≅ ⦅ q ⦆ S
        i .fun poly[,]              = onPos tt , onDir tt 
                                        where open Poly[_,_] poly[,]
        i .inv (pm , dm)            = (λ x → pm) ⇒ₚ λ x → dm
        i .rightInv (pm , dm)       = refl
        i .leftInv (onPos ⇒ₚ onDir) = refl

-- multivariate polynomials
record Polyₘ (Vars : Set) : Set₁ where
    constructor _▹ₘ_
    field
        Pos : Set
        Dir : Pos → ∀ (var : Vars) → Set

⦅_⦆⋆_ : {Vars : Set} → Polyₘ Vars → (Vars → Set) → Set 
(⦅_⦆⋆_) {Vars} (Pos ▹ₘ Dir) f = Σ[ p ∈ Pos ] (∀ (var : Vars) → (Dir p var → f var ))