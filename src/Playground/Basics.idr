---------------------
-- Module declaration
---------------------

module Playground.Basics

-------------------
-- External imports
-------------------

import Builtin

------
-- Not
------

public export
Not : Type -> Type
Not a = a -> Void

-------
-- Void
-------

%extern
prim__void : (0 x : Void) -> a

public export
void : (0 x : Void) -> a
void = prim__void

-------------
-- Congruence
-------------

public export
cong : (0 f : t -> u) -> (p : a = b) -> f a = f b
cong f Refl = Refl

---------
-- Either
---------

public export
data Either : Type -> Type -> Type where
  Left  : (x : a) -> Either a b
  Right : (x : b) -> Either a b

------
-- Dec
------

public export
data Dec : Type -> Type where
  Yes : (prf : prop) -> Dec prop
  No  : (contra : Not prop) -> Dec prop

---------
-- Subset
---------

public export
  record Subset type pred where
    constructor Element
    fst : type
    0 snd : pred fst
