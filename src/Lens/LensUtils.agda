open import Level
open import Function using (flip)
open import Data.Product
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import Product
open import NaturalTransformation
open import Monoidal
open import SymmetricMonoidal
open import CD-Category
open import CDAffine-Category
open import Cartesian
open import Span
open import Lens.LensCategory

module Lens.LensUtils
  {o m}
  {cat : Cat o m}
  {mc : Monoidal cat}
  {smc : SymmetricMonoidal mc}
  {cd : CD-Category smc}
  {cda : CDAffine-Category cd}
  (cart : Cartesian cda) where


ff : ((lensCategory cart) Functor span cat)
ff = MkFunctor
  (λ (x , x') → {! !})
  {!!}
  {!!}
  {!!}
