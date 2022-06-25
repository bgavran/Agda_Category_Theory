module Poly.PolyCat where 

open import Level
open import Category
open import Poly.Poly
open import Cubical.Foundations.Everything renaming (Iso to _≅_) hiding (id;assoc)
open Cat

PolyCat : Cat (suc zero) zero
PolyCat .obj = Poly
PolyCat ._hom_ = Poly[_,_]
PolyCat .id = (λ x → x) ⇒ₚ (λ i x → x)
PolyCat ._●_ = _⇒∘ₚ_
PolyCat .left-id = refl
PolyCat .right-id = refl
PolyCat .assoc = refl
PolyCat .●-resp-≡ p q = {!   !}

-- can also show mapping into Agda EndoFunctor category
-- can also show displayed category based over poly

