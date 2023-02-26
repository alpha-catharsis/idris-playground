---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Prev

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LT

-----------------
-- prev operation
-----------------

public export
prev : (m : Nat) -> {auto 0 prf : LT Z m} -> Nat
prev (S m') = m'
