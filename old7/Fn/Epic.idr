---------------------
-- Module declaration
---------------------

module Fn.Epic

-------------------
-- Internal imports
-------------------

import Fn.Comp
import Fn.Eq
import Fn.Id
import Rel.Equal

-----------------
-- Epic function
-----------------

public export
data Epic : (f : a -> b) -> Type where
  MkEpic : (f : b -> a) ->
            ({c : Type} -> (h : a -> c) -> (k : a -> c) ->
             FnEq (h . f) (k . f) -> FnEq h k) -> Epic f

-----------------
-- Epic theorems
-----------------

idEpic : Epic Id.id
idEpic = MkEpic Id.id (\h, k, eqPrf, x => eqPrf x)

