---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Rel.LT

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Succ

-----
-- LT
-----

-- public export
-- data LT : (m : Nat) -> (n : Nat) -> Type where
--   LTZero : LT Z (succ n)
--   LTSucc : LT m n -> LT (succ m) (succ n)
