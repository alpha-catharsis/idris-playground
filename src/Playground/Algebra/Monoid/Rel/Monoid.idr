---------------------
-- Module declaration
---------------------

module Playground.Algebra.Monoid.Rel.Monoid

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Fn.Fn
import Playground.Fn.Rel.Associative
import Playground.Fn.Rel.Identity
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

-------------------
-- Monoid interface
-------------------

public export
data Monoid : (0 s : Type) -> BinOp s -> s -> Type where
  IsMonoid : (f : BinOp s) -> (e : s) -> Associative f -> LeftIdentity f e ->
             RightIdentity f e -> Monoid s f e

public export
binop : Monoid s f e -> BinOp s
binop (IsMonoid f _ _ _ _) = f

export
binopExact : (m : Monoid s f e) -> binop m = f
binopExact (IsMonoid _ _ _ _ _) = Refl

public export
binopIdElem : Monoid s f e -> s
binopIdElem (IsMonoid _ e _ _ _) = e

public export
binopIdElemExact : (m : Monoid s f e) -> binopIdElem m = e
binopIdElemExact (IsMonoid _ _ _ _ _) = Refl

public export
binopAssociative : Monoid s f e -> Associative f
binopAssociative (IsMonoid _ _ prf _ _) = prf

public export
binopLeftIdentity : Monoid s f e -> LeftIdentity f e
binopLeftIdentity (IsMonoid _ _ _ prf _) = prf

public export
binopRightIdentity : Monoid s f e -> RightIdentity f e
binopRightIdentity (IsMonoid _ _ _ _ prf) = prf
