{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)
open ≡-Reasoning
open import Data.Product

open import Category
open import Functor
import Shapes
open Cat

-- calling it catE for no apparent reasons, usually I saw "E" to be the name of this cat
module Comma
  {o o' o'' m m' m'' : Level}
  {cat₁ : Cat o m}
  {cat₂ : Cat o' m'}
  {catE : Cat o'' m''}
  (S : cat₁ Functor catE)
  (T : cat₂ Functor catE)
  where

module fun1 = _Functor_ S
module fun2 = _Functor_ T
open fun1 renaming (mapObj to S₀; mapMor to S₁) -- F₀ is mapping on objects, F₁ is mapping on morphisms
open fun2 renaming (mapObj to T₀; mapMor to T₁)

module commashp = Shapes catE
open commashp

record CommaObj  : Set (o ⊔ o' ⊔ m'') where
  constructor MkCommaObj
  field
    obj1 : obj cat₁
    obj2 : obj cat₂
    mmap : catE [ (S₀ obj1) , (T₀ obj2) ]

record _commaHom_ (f g : CommaObj) : Set (m ⊔ m' ⊔ m'') where
  constructor MkCommaHom
  private
    module F = CommaObj f
    module G = CommaObj g
  field
    map1 : cat₁ [ F.obj1 , G.obj1 ]
    map2 : cat₂ [ F.obj2 , G.obj2 ]
    sqq : CommutativeSquare (S₁ map1) (G.mmap) F.mmap (T₁ map2)

    
commaComp : {a b c : CommaObj} → a commaHom b → b commaHom c → a commaHom c
commaComp (MkCommaHom mapf1 mapf2 sqqf1) (MkCommaHom mapg1 mapg2 sqqg1) = MkCommaHom
  (cat₁ [ mapf1 ● mapg1 ])
  (cat₂ [ mapf2 ● mapg2 ])
  {!!}


_⇒_ : Cat (o ⊔ o' ⊔ m'') (m ⊔ m' ⊔ m'')
_⇒_ = MkCat
  CommaObj
  _commaHom_
  (MkCommaHom (id cat₁ ) (id cat₂) {!!})
  commaComp
  {!!}
  {!!}
  {!!}
  {!!}
