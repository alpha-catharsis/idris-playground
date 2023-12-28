---------------------
-- Module declaration
---------------------

module Playground.Fn.Rel.Associative

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Fn.Fn
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

---------------------------------
-- Operation associative property
---------------------------------

public export
data Associative : BinOp a -> Type where
  IsAssociative : (f : BinOp a) ->
                  ((x, y, z : a) -> f x (f y z) = f (f x y) z) ->
                  Associative f
