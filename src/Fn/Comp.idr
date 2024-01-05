---------------------
-- Module declaration
---------------------

module Fn.Comp

-------------------
-- Internal imports
-------------------

import Fn.Eq
import Fn.Id
import Rel.Equal

-----------------------
-- Function composition
-----------------------

infixr 9 .

public export
(.) : (g : b -> c) -> (f : a -> b) -> a -> c
(.) g f x = g (f x)

--------------------
-- Function theorems
--------------------

export
compAssociative : (h : c -> d) -> (g : b -> c) -> (f : a -> b) ->
                  FnEq ((h . g) . f) (h . (g . f))
compAssociative _ _ _ _ = Refl

export
leftIdNeutral : {f : a -> b} -> FnEq (Id.id . f) f
leftIdNeutral _ = Refl

export
rightIdNeutral : {f : a -> b} -> FnEq (f . Id.id) f
rightIdNeutral _ = Refl
