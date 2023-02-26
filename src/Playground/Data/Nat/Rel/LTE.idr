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
data LTE : (m : Nat) -> (n : Nat) -> Type where
  LTEZero : LTE Z n
  LTESucc : LTE m n -> LTE (S m) (S n)
