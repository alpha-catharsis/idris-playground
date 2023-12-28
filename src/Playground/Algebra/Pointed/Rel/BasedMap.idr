---------------------
-- Module declaration
---------------------

module Playground.Algebra.Pointed.Rel.BasedMap

-------------------
-- Internal imports
-------------------

import Playground.Algebra.Pointed.Rel.Pointed
import Playground.Data.List.List
import Playground.Fn.Fn
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

---------------------
-- Based Map property
---------------------

public export
data BasedMap : (0 a : Type) -> (0 b : Type) -> UnyFn a b -> Type where
  IsBasedMap : Pointed a x -> Pointed b y -> (f : UnyFn a b) ->
               f x = y -> BasedMap a b f
