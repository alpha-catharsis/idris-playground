---------------------
-- Module declaration
---------------------

module Playground.Algebra.Magma.Rel.MagmaMorphism

-------------------
-- Internal imports
-------------------

import Playground.Algebra.Magma.Rel.Magma
import Playground.Data.List.List
import Playground.Fn.Fn
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

--------------------
-- Magma interface
--------------------

public export
data MagmaMorphism : (s1 : Type) -> (s2 : Type) -> UnyFn s1 s2 -> Type where
  IsMagmaMorphism : Magma s1 f -> Magma s2 g -> (h : UnyFn s1 s2) ->
                    ((x : s1) -> (y : s1) -> h (f x y) = g (h x) (h y)) ->
                    MagmaMorphism s1 s2 h

