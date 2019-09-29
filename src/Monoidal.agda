{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Function using (flip)
open import Data.Product
open import IO
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning

open import Category

module Monoidal {n m} (cat : Cat n m) where

private
  module cc = Cat cat
  variable n' m' n'' m'' : Level

open import Isomorphism
open import Functor
open import Product
open import NaturalTransformation
open cc hiding (_[_,_])
open Isomorphism._≅_
open Cat using (_[_,_])
open Cat.CommutativeSquare
open _Functor_
open _NatTrans_



record Monoidal : Set (n ⊔ m) where
  constructor MkMonoidal

  field
    ⊗ : (cat X cat) Functor cat
    𝟙 : obj


  x⊗[y⊗z] : (cat X (cat X cat)) Functor cat
  x⊗[y⊗z] = (idFunctor 𝕏 ⊗) ●F ⊗

  [x⊗y]⊗z : (cat X (cat X cat)) Functor cat
  [x⊗y]⊗z = (productAssociatorᵣ ●F (⊗ 𝕏 idFunctor {cat = cat}))  ●F ⊗

  [𝟙⊗x] : cat Functor cat
  [𝟙⊗x] = (constFunctor 𝟙 /\ idFunctor {cat = cat}) ●F (⊗)

  [x⊗𝟙] : cat Functor cat
  [x⊗𝟙] = (idFunctor /\ constFunctor 𝟙) ●F ⊗

  field
    associator  : _≅_ {cat = functorCategory} [x⊗y]⊗z x⊗[y⊗z]
    leftUnitor  : _≅_ {cat = functorCategory} [𝟙⊗x] idFunctor
    rightUnitor : _≅_ {cat = functorCategory} [x⊗𝟙] idFunctor
    --▵-identity : associator ●≅ (? ⊗≅ ?)

  infixl 10 _⊗ₒ_ _⊗ₘ_
  _⊗ₒ_ : obj → obj → obj
  _⊗ₒ_ = curry (mapObj ⊗)

  _⊗ₘ_ : {a b c d : obj}
    → a hom b
    → c hom d
    → (a ⊗ₒ c) hom (b ⊗ₒ d)
  f ⊗ₘ g = mapMor ⊗ (f , g)



  λₘ : {a : obj}
    → (𝟙 ⊗ₒ a) hom  a
  λₘ = η (forward leftUnitor)


  ρₘ : {a : obj}
    → (a ⊗ₒ 𝟙) hom  a
  ρₘ = η (forward rightUnitor)

  αₘ : {a b c : obj}
    → ((a ⊗ₒ b) ⊗ₒ c)
    hom (a ⊗ₒ(b ⊗ₒ c))
  αₘ = η (forward associator)


  αₘ' : {a b c : obj}
    → (a ⊗ₒ (b ⊗ₒ c))
    hom ((a ⊗ₒ b) ⊗ₒ c)
  αₘ' = η (inverse associator)

  λ□ : {a : obj} {f : cat [ a , a ]}
    → mapMor ((constFunctor 𝟙 /\ idFunctor) ●F ⊗) f ● λₘ
    ≡ λₘ ● f
  λ□ = eqPaths (naturality (forward leftUnitor))

  ρ□ : {a : obj} {f : cat [ a , a ]}
    → mapMor ((idFunctor /\ constFunctor 𝟙) ●F ⊗) f ● ρₘ
    ≡ ρₘ ● f
  ρ□ = eqPaths (naturality (forward rightUnitor))

  α□ : {a b c d e i : obj}
    → {f : (cat X (cat X cat)) [ (a , (b , c)) , (d , (e , i)) ]}
    → mapMor ((productAssociatorᵣ ●F (⊗ 𝕏 idFunctor)) ●F ⊗) f ● αₘ
    ≡ αₘ ● mapMor ((idFunctor 𝕏 ⊗) ●F ⊗) f
  α□ = eqPaths (naturality (forward associator))

  α□' : {a b c d e i : obj}
    → {f : (cat X (cat X cat)) [ (a , (b , c)) , (d , (e , i)) ]}
    → mapMor ((idFunctor 𝕏 ⊗) ●F ⊗) f ● αₘ'
    ≡ αₘ' ● mapMor ((productAssociatorᵣ ●F (⊗ 𝕏 idFunctor)) ●F ⊗) f
  α□' = eqPaths (naturality (inverse associator))


  distribute⊗ : {a b c d e j : obj}
    → {f : a hom c} {g : c hom e} {h : b hom d} {i : d hom j}
    → (f ● g) ⊗ₘ (h ● i) ≡ (f ⊗ₘ h) ● (g ⊗ₘ i)
  distribute⊗ {f = f} {g = g} {h = h} {i = i} = compLaw ⊗ (f , h) (g , i)


  distribute⊗₃ : {a b c d e o p q : obj}
    → {f : a hom c} {g : c hom e} {h : b hom d} {i : d hom o}  {j : e hom q } {k : o hom p}
    → (f ● g ● j) ⊗ₘ (h ● i ● k) ≡ (f ⊗ₘ h) ● (g ⊗ₘ i) ● (j ⊗ₘ k)
  distribute⊗₃ {f = f} {g = g} {h = h} {i = i} {j = j} {k = k} =
    begin
      ((f ● g) ● j) ⊗ₘ ((h ● i) ● k)
    ≡⟨  compLaw ⊗ (f ● g , (h ● i)) (j , k)  ⟩
         ((f ● g) ⊗ₘ (h ● i)) ● (j ⊗ₘ k)
    ≡⟨   distribute⊗ ⟨●⟩refl    ⟩
      (f ⊗ₘ h) ● (g ⊗ₘ i) ● (j ⊗ₘ k)
    ∎

  ⊗-resp-≡ : {a b c d : obj} {f g : a hom b} {h i : c hom d}
    → f ≡ g → h ≡ i → f ⊗ₘ h ≡ g ⊗ₘ i
  ⊗-resp-≡ l r = cong₂ _⊗ₘ_ l r

  ⊗-resp-≡ₗ : {a b c d : obj} {f g : a hom b} {h : c hom d}
    → f ≡ g → f ⊗ₘ h ≡ g ⊗ₘ h
  ⊗-resp-≡ₗ l = ⊗-resp-≡ l refl

  ⊗-resp-≡ᵣ : {a b c d : obj} {f : a hom b} {g h : c hom d}
    → g ≡ h → f ⊗ₘ g ≡ f ⊗ₘ h
  ⊗-resp-≡ᵣ r = ⊗-resp-≡ refl r

  -- Monoidal product of isomorphisms is an isomorphism
  -- Action of a bifunctor on two isomorphisms should also be an isomorphism?
  _⊗≅_ : {a b c d : obj}
    → _≅_ {cat = cat} a b → _≅_ {cat = cat} c d → _≅_ {cat = cat} (a ⊗ₒ c) (b ⊗ₒ d)
  f ⊗≅ g = MkIso
    (forward f ⊗ₘ forward g)
    (inverse f ⊗ₘ inverse g)
    (begin
       (inverse f ⊗ₘ inverse g) ● (forward f ⊗ₘ forward g)
    ≡⟨ sym distribute⊗ ⟩
       (inverse f ● forward f) ⊗ₘ (inverse g ● forward g)
    ≡⟨ ⊗-resp-≡ (leftInverseLaw f) (leftInverseLaw g) ⟩
       (id ⊗ₘ id)
    ≡⟨   idLaw ⊗   ⟩
        id
    ∎)
    (begin
        (forward f ⊗ₘ forward g) ● (inverse f ⊗ₘ inverse g)
      ≡⟨ sym distribute⊗ ⟩
        (forward f ● inverse f) ⊗ₘ (forward g ● inverse g)
      ≡⟨ ⊗-resp-≡ (rightInverseLaw f) (rightInverseLaw g) ⟩
        (id ⊗ₘ id)
      ≡⟨   idLaw ⊗   ⟩
        id
    ∎)

  -- TODO can't add triangle identity as a field since Agda seems to be broken...
  --field
  --  triangleIdentity : obj -- {x y : obj}
  --  -- → αₘ {a = x} {b = 𝟙} {c = y} ● (id ⊗ λₘ) ≡ ρₘ ⊗ₘ id


  ▵-identity : {a c : obj}
    → αₘ {a = a} {b = 𝟙} {c = c} ● (id ⊗ₘ λₘ) ≡ ρₘ ⊗ₘ id
  ▵-identity = {!!}

  ⬠-identity : {a b c d : obj}
    → αₘ {a = (a ⊗ₒ b)} {b = c} {c = d} ● αₘ {a = a} {b = b} {c = (c ⊗ₒ d)}
    ≡ (αₘ {a = a} {b = b} {c = c} ⊗ₘ id) ● αₘ {a = a} {b = (b ⊗ₒ c)} {c = d} ● (id ⊗ₘ αₘ {a = b} {b = c} {c = d})
  ⬠-identity = {!!}


  distribute⊗ₗ : {a b c d e j : obj}
    → (f : a hom e)
    → (g : b hom d)
    → (i : d hom j)
    → f ⊗ₘ (g ● i) ≡ (id ⊗ₘ i) ∘ (f ⊗ₘ g )
  distribute⊗ₗ f g i =
    begin
      f ⊗ₘ (g ● i)
    ≡⟨  {!!}  ⟩ -- [ ⊗ ] -resp-≡ !!
      (f ● id) ⊗ₘ (g ● i)
    ≡⟨  {!!}  ⟩
      (f ⊗ₘ g ) ● (id ⊗ₘ i)
    ∎
    --compLaw ⊗ (f , g) (id , i)

  assocApply : {a b c c' d : obj}
    → {x : a hom b} {f : b hom c} {g : c hom d} {h : b hom c'} {i : c' hom d}
    → f ● g ≡ h ● i
    → x ● f ● g ≡ x ● h ● i
  assocApply {x = x} {f = f} {g = g} {h = h} {i = i} e =
    begin
       (x ● f) ● g   ≡⟨   assoc     ⟩
       x ● (f ● g)   ≡⟨  refl⟨●⟩ e  ⟩
       x ● (h ● i)   ≡⟨  sym assoc  ⟩
       (x ● h) ● i
    ∎

  assocMoveₗ : {a b c d e i l : obj}
    → {x : l hom ((a ⊗ₒ b) ⊗ₒ c)}
    → {f : a hom d} {g : b hom e} {h : c hom i}
    → x ● ((f ⊗ₘ g) ⊗ₘ h) ● αₘ ≡ x ● αₘ ● (f ⊗ₘ (g ⊗ₘ h))
  assocMoveₗ = assocApply α□



   -- TODO coherence conditions
