---------------------
-- Module declaration
---------------------

module Playground.Algebra.Magma.Rel.Magma

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Fn.Fn
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

--------------------
-- Magma interface
--------------------

public export
data Magma : (0 s : Type) -> BinOp s -> Type where
  IsMagma : (f : BinOp s) -> Magma s f

public export
binop : Magma s f -> BinOp s
binop (IsMagma f) = f

export
binopExact : (m : Magma s f) -> binop m = f
binopExact (IsMagma _) = Refl
