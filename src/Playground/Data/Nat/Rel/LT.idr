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
data LT : (n : Nat) -> (m : Nat) -> Type where
  LTZero   : LT Z (S n)
  LTSucc : LT n m -> LT (S n) (S m)
