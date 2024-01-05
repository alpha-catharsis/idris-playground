---------------------
-- Module declaration
---------------------

module Fn.Iso

-------------------
-- Internal imports
-------------------

import Data.Bool
import Data.Prod
import Data.Sum
import Data.Unit
import Data.Void
import Fn.Comp
import Fn.Const
import Fn.Either
import Fn.Eq
import Fn.Id
import Rel.Equal

-----------------------
-- Function isomorphism
-----------------------

public export
data Iso : (f : a -> b) -> (f' : b -> a) -> Type where
  MkIso : (f : a -> b) -> (f' : b -> a) -> FnEq (f' . f) Id.id ->
          FnEq (f . f') Id.id -> Iso f f'

public export
data Iso2 : (f : (a -> b) -> (c -> d)) ->
            (f' : (c -> d) -> (a -> b)) -> Type where
  MkIso2 : (f : (a -> b) -> (c -> d)) -> (f' : (c -> d) -> (a -> b)) ->
           FnEq2 (f' . f) Id.id -> FnEq2 (f . f') Id.id -> Iso2 f f'

----------------------
-- Isomorpism theorems
----------------------

export
isoLeftCancel : Iso f f' -> FnEq (f . f') Id.id
isoLeftCancel (MkIso f f' _ prf') x = prf' x

export
isoRightCancel : Iso f f' -> FnEq (f' . f) Id.id
isoRightCancel (MkIso f f' prf _) x = prf x

export
isoCommutative : Iso f f' -> Iso f' f
isoCommutative (MkIso f f' prf1 prf2) = MkIso f' f prf2 prf1

export
isoLeftShunt : Iso f f' -> FnEq (f . g) h -> FnEq g (f' . h)
isoLeftShunt isoPrf eqPrf x =
  rewrite sym (eqPrf x) in
  rewrite isoRightCancel isoPrf (g x) in Refl

export
isoRightShunt : Iso f f' -> FnEq (g . f) h -> FnEq g (h . f')
isoRightShunt (MkIso f f' prf prf') eqPrf x =
  rewrite sym (eqPrf (f' x)) in
  rewrite isoLeftCancel (MkIso f f' prf prf') x in Refl

-----------------------
-- Product isomorphisms
-----------------------

export
prodZero : Prod a Void -> Void
prodZero (MkProd _ _) impossible

export
prodZero' : Void -> Prod a Void
prodZero' _ impossible

export
prodZeroIso : Iso Iso.prodZero Iso.prodZero'
prodZeroIso = MkIso prodZero prodZero' (\(MkProd _ x) => absurd x)
                    (\x => absurd x)

export
prodOne : Prod a Unit -> a
prodOne (MkProd x _) = x

export
prodOne' : a -> Prod a Unit
prodOne' x = MkProd x MkUnit

export
prodOneIso : Iso Iso.prodOne Iso.prodOne'
prodOneIso = MkIso prodOne prodOne'
                   (\(MkProd x MkUnit) => Refl)
                   (\x => Refl)

-------------------
-- Sum isomorphisms
-------------------

export
sumZero : Sum a Void -> a
sumZero (Inj1 x) = x
sumZero (Inj2 _) impossible

export
sumZero' : a -> Sum a Void
sumZero' = Inj1

export
sumZeroIso : Iso Iso.sumZero Iso.sumZero'
sumZeroIso = MkIso sumZero sumZero'
                   (\e => case e of
                      Inj1 x => Refl
                      Inj2 y => absurd y)
                   (\x => Refl)

-----------------------
-- Boolean isomorphisms
-----------------------

export
boolProd : Prod Bool a -> Sum a a
boolProd (MkProd False x) = Inj1 x
boolProd (MkProd True y) = Inj2 y

export
boolProd' : Sum a a -> Prod Bool a
boolProd' (Inj1 x) = MkProd False x
boolProd' (Inj2 y) = MkProd True y

export
boolProdIso : Iso Iso.boolProd Iso.boolProd'
boolProdIso = MkIso boolProd boolProd'
                    (\(MkProd b _) => case b of
                      False => Refl
                      True => Refl)
                    (\e => case e of
                      Inj1 _ => Refl
                      Inj2 _ => Refl)
