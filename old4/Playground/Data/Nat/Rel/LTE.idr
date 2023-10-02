---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Rel.LTE

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Succ

------
-- LTE
------

-- public export
-- data LTE : (m : Nat) -> (n : Nat) -> Type where
--   LTEZero : LTE Z n
--   LTESucc : LTE m n -> LTE (succ m) (succ n)
