---------------------
-- Module declaration
---------------------

module Playground.Algebra.UnarySystem.Rel.UnarySystem

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

------------------------
-- UnarySystem interface
------------------------

public export
data UnarySystem : (0 s : Type) -> (s -> s) -> Type where
  IsUnarySystem : (f : s -> s) -> UnarySystem s f

public export
unop : UnarySystem s f -> (s -> s)
unop (IsUnarySystem f) = f

public export
unopExact : (us : UnarySystem s f) -> unop us = f
unopExact (IsUnarySystem _) = Refl
