---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Pow

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper

-----------------
-- pow operation
-----------------

public export
pow : Nat -> Nat -> Nat
pow m n = hyper (S (S (S Z))) m n
