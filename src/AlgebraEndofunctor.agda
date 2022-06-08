open import Level
open import Function renaming (id to id→; _∘_ to _∘ᶠ_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Category
open import Functor

module AlgebraEndofunctor
  {n m}
  {cat : Cat n m}
  where

module cat = Cat cat
open cat



record _Algebra
  (F : cat Functor cat) : Set (n ⊔ m) where
  constructor MkAlgebra
  module F = _Functor_ F
  open F

  field
    carrier : obj
    a : carrier hom (mapObj carrier)

module AlgebraStuff (F : cat Functor cat) where

  module F = _Functor_ F
  open F

  record _AlgebraHom_
    (alg1 alg2 : F Algebra) : Set (n ⊔ m) where
    constructor MkAlgHom
    module alg1 = _Algebra alg1
    module alg2 = _Algebra alg2
    open alg1
    open alg2 renaming (carrier to carrier'; a to a')
    field
      f : carrier hom carrier'
      naturalitySquare : CommutativeSquare f a' a (mapMor f)
  
  open _Algebra
  
  idAlgebra : {alg : F Algebra} → alg AlgebraHom alg
  idAlgebra {alg} = MkAlgHom
    (id {carrier alg}  )
    (MkCommSq (
      begin
        id {carrier alg} ● a alg
      ≡⟨ right-id ⟩
        a alg 
      ≡⟨ sym left-id ⟩
         a alg ● id {mapObj (carrier alg)}
      ≡⟨ refl⟨●⟩ (sym idLaw)  ⟩
        a alg ● mapMor (id {carrier alg})
     ∎))



  composeAlgebras : {a b c : F Algebra} → a AlgebraHom b → b AlgebraHom c → a AlgebraHom c
  composeAlgebras (MkAlgHom f₁ nat₁) (MkAlgHom f₂ nat₂)= MkAlgHom (f₁ ● f₂) {!!}

  leftIdentityAlgebra : {a : F Algebra} {b : F Algebra}
                        {f : a AlgebraHom b} → composeAlgebras f idAlgebra ≡ f
  leftIdentityAlgebra = {!!} 


  categoryOfAlgebras : Cat (n ⊔ m) (n ⊔ m)
  categoryOfAlgebras = MkCat
    (F Algebra)
    _AlgebraHom_
    idAlgebra
    composeAlgebras
    leftIdentityAlgebra
    {!!}
    {!!}
    {!!}
