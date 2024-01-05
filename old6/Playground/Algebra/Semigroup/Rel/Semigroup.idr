---------------------
-- Module declaration
---------------------

module Playground.Algebra.Semigroup.Rel.Semigroup

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Fn.Fn
import Playground.Fn.Rel.Associative
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

--------------------
-- Semigroup interface
--------------------

public export
data Semigroup : (0 s : Type) -> BinOp s -> Type where
  IsSemigroup : (f : BinOp s) -> Associative f -> Semigroup s f

public export
binop : Semigroup s f -> BinOp s
binop (IsSemigroup f _) = f

public export
binopAssociative : Semigroup s f -> Associative f
binopAssociative (IsSemigroup _ prf) = prf

export
binopExact : (m : Semigroup s f) -> binop m = f
binopExact (IsSemigroup _ _) = Refl
