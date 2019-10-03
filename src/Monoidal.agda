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

  ⇆ : {a b c d : obj} {f : a hom b} {g : c hom d}
    → (id ⊗ₘ g) ● (f ⊗ₘ id) ≡ (f ⊗ₘ id) ● (id ⊗ₘ g)
  ⇆ {f = f} {g = g} =
    begin
      (id ⊗ₘ g) ● (f ⊗ₘ id)
    ≡⟨  sym distribute⊗ ⟩
      (id ● f) ⊗ₘ (g ● id)
    ≡⟨  ⊗-resp-≡ right-id left-id  ⟩
          f ⊗ₘ g
    ≡⟨  ⊗-resp-≡ (sym left-id) (sym right-id)  ⟩
      (f ● id) ⊗ₘ  (id ● g)
    ≡⟨  distribute⊗  ⟩
      (f ⊗ₘ id) ● (id ⊗ₘ g)
    ∎



  -- should be a useful combinator for sliding stuff through the associator
  moveThroughAssoc : {a b c d e f g : obj}
    {x : a hom (c ⊗ₒ d)} {y : b hom e} {z : c hom f} {w : (d ⊗ₒ e) hom g}
    → (x ⊗ₘ y) ● αₘ ● (z ⊗ₘ w) ≡ ((x ● (z ⊗ₘ id)) ⊗ₘ y) ● αₘ ● (id ⊗ₘ w)
  moveThroughAssoc {x = x} {y = y} {z = z} {w = w} =
    begin
      (x ⊗ₘ y) ● αₘ ● (z ⊗ₘ w)
    ≡⟨  refl⟨●⟩ ⊗-resp-≡ (sym left-id) (sym right-id)   ⟩
      (x ⊗ₘ y) ● αₘ ● ((z ● id) ⊗ₘ (id ● w))
    ≡⟨  refl⟨●⟩ distribute⊗   ⟩
      (x ⊗ₘ y) ● αₘ ● ((z ⊗ₘ id) ● (id ⊗ₘ w))
    ≡⟨  refl⟨●⟩ (⊗-resp-≡ᵣ(sym (idLaw ⊗)) ⟨●⟩refl)   ⟩
      (x ⊗ₘ y) ● αₘ ● ((z ⊗ₘ (id ⊗ₘ id)) ● (id ⊗ₘ w))
    ≡⟨  sym assoc   ⟩
      (x ⊗ₘ y) ● αₘ ● (z ⊗ₘ (id ⊗ₘ id)) ● (id ⊗ₘ w)
    ≡⟨  assocApply (sym α□) ⟨●⟩refl   ⟩
      (x ⊗ₘ y) ● ((z ⊗ₘ id) ⊗ₘ id) ● αₘ ● (id ⊗ₘ w)
    ≡⟨  sym distribute⊗ ⟨●⟩refl₂  ⟩
      ((x ● (z ⊗ₘ id)) ⊗ₘ (y ● id)) ● αₘ ● (id ⊗ₘ w)
    ≡⟨  (⊗-resp-≡ᵣ left-id ) ⟨●⟩refl₂  ⟩
      ((x ● (z ⊗ₘ id)) ⊗ₘ y) ● αₘ ● (id ⊗ₘ w)
    ∎

  factorId : {x a b c : obj}
    {f : a hom b} {g : b hom c}
    → (f ⊗ₘ id {a = x}) ● (g ⊗ₘ id) ≡ (f ● g) ⊗ₘ id
  factorId {f = f} {g = g} =
    begin
       (f ⊗ₘ id) ● (g ⊗ₘ id)
    ≡⟨  sym distribute⊗   ⟩
       (f ● g) ⊗ₘ (id ● id)
    ≡⟨  ⊗-resp-≡ᵣ left-id  ⟩
       (f ● g) ⊗ₘ id
    ∎
  factorId₃ : {x a b c d : obj}
    {f : a hom b} {g : b hom c} {h : c hom d}
    → (f ⊗ₘ id {a = x}) ● (g ⊗ₘ id) ● (h ⊗ₘ id) ≡ (f ● g ● h) ⊗ₘ id
  factorId₃ {f = f} {g = g} {h = h} =
    begin
       (f ⊗ₘ id) ● (g ⊗ₘ id) ● (h ⊗ₘ id)
    ≡⟨  factorId ⟨●⟩refl  ⟩
       ((f ● g) ⊗ₘ id) ● (h ⊗ₘ id)
    ≡⟨  factorId  ⟩
      (f ● g ● h) ⊗ₘ id
    ∎

  factorId₄ : {x a b c d e : obj}
    {f : a hom b} {g : b hom c} {h : c hom d} {i : d hom e}
    → (f ⊗ₘ id {a = x}) ● (g ⊗ₘ id) ● (h ⊗ₘ id) ● (i ⊗ₘ id) ≡ (f ● g ● h ● i) ⊗ₘ id
  factorId₄ {f = f} {g = g} {h = h} {i = i} =
    begin
       (f ⊗ₘ id) ● (g ⊗ₘ id) ● (h ⊗ₘ id) ● (i ⊗ₘ id)
    ≡⟨  factorId ⟨●⟩refl₂  ⟩
       ((f ● g) ⊗ₘ id) ● (h ⊗ₘ id) ● (i ⊗ₘ id)
    ≡⟨  factorId₃  ⟩
       (f ● g ● h ● i) ⊗ₘ id
    ∎

  --assocFn : {a b c d e : obj} {f : (c ⊗ₒ d) hom e}
  --  → (id ⊗ₘ f) ● αₘ {a = a} {b = b} {c = e} ≡ {!!} -- (αₘ ● (id ⊗ₘ f))
    --→ (id ⊗ₘ f) ● αₘ ≡ id  ⊗ₘ (αₘ ● (id ⊗ₘ f))
