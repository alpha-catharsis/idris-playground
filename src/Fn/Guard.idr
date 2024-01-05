---------------------
-- Module declaration
---------------------

module Fn.Guard

-------------------
-- Internal imports
-------------------

import Data.Bool
import Data.Sum
import Fn.Comp
import Fn.Eq
import Fn.Either
import Fn.Sum
import Rel.Equal

-----------------
-- Guard function
-----------------

public export
guard : (a -> Bool) -> a -> Sum a a
guard c x = case c x of
  False => Inj1 x
  True => Inj2 x

--------------------------
-- Guard function theorems
--------------------------

export
guardFact : (c : a -> Bool) -> (f : a -> a) ->
            FnEq (guard c . f) ((sum f f) . (guard (c . f)))
guardFact c f x with (c (f x))
  guardFact c f x | False = Refl
  guardFact c f x | True = Refl

----------------------
-- Conditinal function
----------------------

public export
cond : (a -> Bool) -> (f : a -> b) -> (g : a -> b) -> a -> b
cond c f g = either f g . guard c

-------------------------------
-- Conditinal function theorems
-------------------------------

export
condFusion : (c : a -> Bool) -> FnEq (f . cond c g h) (cond c (f . g) (f . h))
condFusion c x with (c x)
  condFusion c x | False = Refl
  condFusion c x | True = Refl

