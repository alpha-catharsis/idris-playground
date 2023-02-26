---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Plus

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Fn.Repeat.Repeat

-----------------
-- plus operation
-----------------

public export
plus : Nat -> Nat -> Nat
plus m = repeat S m
