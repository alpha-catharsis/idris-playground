---------------------
-- Module declaration
---------------------

module Playground.Fn.Rel.Identity

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Fn.Fn
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

-----------------------------------
-- Operation left identity property
-----------------------------------

public export
data LeftIdentity : BinOp a -> a -> Type where
  IsLeftIdentity : (f : BinOp a) -> (e : a) ->
                   ((x : a) -> f e x = x) ->
                   LeftIdentity f e

------------------------------------
-- Operation right identity property
------------------------------------

public export
data RightIdentity : BinOp a -> a -> Type where
  IsRightIdentity : (f : BinOp a) -> (e : a) ->
                    ((x : a) -> f x e = x) ->
                    RightIdentity f e
