---------------------
-- Module declaration
---------------------

module Playground.Fn.Injective

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Fn.Fn

----------------------
-- Injective functions
----------------------

public export
data Injective : (f : a -> b) -> Type where
  IsInjective : {0 a : Type} -> {0 b : Type} -> (f : a -> b) ->
                ({x : a} -> { y : a} -> Equal (f x) (f y) -> Equal x y) ->
                Injective f
