---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Prop.Odd

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Succ

------
-- Odd
------

-- public export
-- data Odd : (m : Nat) -> Type where
--   OddO : Odd (S Z)
--   OddS : (prf : Odd m) -> Odd (succ (succ m))
