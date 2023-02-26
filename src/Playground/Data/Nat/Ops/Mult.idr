---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Mult

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Plus
import Playground.Fn.Repeat.Repeat

-----------------
-- mult operation
-----------------

public export
mult : Nat -> Nat -> Nat
mult m n = repeat (plus m) n Z
