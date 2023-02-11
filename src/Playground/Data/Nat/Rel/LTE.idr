---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Rel.LTE

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

------
-- LTE
------

public export
data LTE : (n : Nat) -> (m : Nat) -> Type where
  LTEZero : LTE Z m
  LTESucc : LTE n m -> LTE (S n) (S m)
