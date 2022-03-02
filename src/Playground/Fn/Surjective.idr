---------------------
-- Module declaration
---------------------

module Playground.Fn.Surjective

-------------------
-- Internal imports
-------------------

import Playground.Data.DPair.DPair
import Playground.Rel.Equal.Equal
import Playground.Fn.Fn

-----------------------
-- Surjective functions
-----------------------

public export
data Surjective : (f : a -> b) -> Type where
  IsSurjective : {0 a : Type} -> {0 b : Type} -> (f : a -> b) ->
                 ((y : b) -> DPair a (\x => Equal (f x) y)) ->
                 Surjective f
