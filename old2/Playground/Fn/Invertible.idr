---------------------
-- Module declaration
---------------------

module Playground.Fn.Invertible

-------------------
-- Internal imports
-------------------

import Playground.Fn.Fn
import Playground.Fn.Injective
import Playground.Fn.Surjective
import Playground.Prop.Prop
import Playground.Rel.Equal.Equal

-----------------------
-- Invertible functions
-----------------------

public export
data Invertible : (f : a -> b) -> Type where
  IsInvertible : {0 a : Type} -> {0 b : Type} -> (f : a -> b) ->
                 Injective f => Surjective f => (g : b -> a) ->
                 ((x : a) -> Equal (g (f x)) x) ->
                 ((y : b) -> Equal (f (g y)) y) ->
                 Invertible f

inv : (f : a -> b) -> Invertible f => (b -> a)
inv f @{IsInvertible _ g _ _} = g
