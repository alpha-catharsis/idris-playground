---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Rel.LT

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

-----
-- LT
-----

public export
data LT : (m : Nat) -> (n : Nat) -> Type where
  LTZero : LT Z (S n)
  LTSucc : LT m n -> LT (S m) (S n)
