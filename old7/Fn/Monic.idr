---------------------
-- Module declaration
---------------------

module Fn.Monic

-------------------
-- Internal imports
-------------------

import Fn.Comp
import Fn.Eq
import Fn.Id
import Rel.Equal

-----------------
-- Monic function
-----------------

public export
data Monic : (f : a -> b) -> Type where
  MkMonic : (f : a -> b) ->
            ({c : Type} -> (h : c -> a) -> (k : c -> a) ->
             FnEq (f . h) (f . k) -> FnEq h k) -> Monic f

-----------------
-- Monic theorems
-----------------

idMonic : Monic Id.id
idMonic = MkMonic Id.id (\h, k, eqPrf, x => eqPrf x)
