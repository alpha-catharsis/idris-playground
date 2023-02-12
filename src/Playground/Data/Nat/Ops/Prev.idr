---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Prev

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LT

-----------------
-- plus operation
-----------------

public export
prev : (n : Nat) -> {auto 0 prfLT : LT Z n} -> Nat
prev Z      impossible
prev (S n') = n'
