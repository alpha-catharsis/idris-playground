---------------------
-- Module declaration
---------------------

module ScratchPad

-------------------
-- Internal imports
-------------------

import Data.Exp
import Data.List
import Data.Nat
import Data.Prod
import Data.Sum
import Data.Unit
import Fn.Comp
import Fn.ComposeWith
import Fn.Const
import Fn.Either
import Fn.Eq
import Fn.Id
import Fn.Iso
import Fn.Prod
import Fn.Split
import Fn.Sum
import Fn.Transpose
import Rel.Equal

----------
-- Functor
----------

Functor : (Type -> Type) -> Type
Functor f = {a : Type} -> {b : Type} -> (a -> b) -> f a -> f b

---------
-- Monad
---------

Monad : (Type -> Type) -> Type
Monad t = Prod (Functor t) (Prod ({a : Type} -> a -> t a)
                                 ({a : Type} -> t (t a) -> t a))

map : Monad t -> {a : Type} -> {b : Type} -> (a -> b) -> t a -> t b
map = proj1

unit : Monad t -> {a : Type} -> a -> t a
unit = proj1 . proj2

mult : Monad t -> {a : Type} -> t (t a) -> t a
mult = proj2 . proj2

infixl 1 >>=, >>

(>>=) : {auto t : Type -> Type} -> {auto m : Monad t} -> {a : Type} ->
         {b : Type} -> t a -> (a -> t b) -> t b
x >>= f = mult m (map m f x)

(>>) : {auto t : Type -> Type} -> {auto m : Monad t} -> {a : Type} ->
       {b : Type} -> t a -> t b -> t b
x >> y = (>>=) {t} {m} {a} {b} x (const y)

-----------------
-- Identity monad
-----------------

data IdMonad : Type -> Type where
  MkIdMonad : (x : a) -> IdMonad a

idExtr : IdMonad a -> a
idExtr (MkIdMonad x) = x

%hint
idMonad : Monad IdMonad
idMonad = MkProd (\f, (MkIdMonad x) => MkIdMonad (f x))
          (MkProd MkIdMonad (\(MkIdMonad (MkIdMonad x)) => MkIdMonad x))

idTest1 : Nat -> Nat
idTest1 x = idExtr (unit idMonad x)

idTest2 : Monad Nat
idTest2 = MkIdMonad Z >>= ?a
