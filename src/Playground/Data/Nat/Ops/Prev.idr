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

-- public export
-- prev : (m : Nat) -> {auto 0 prfLT : LT Z m} -> Nat
-- prev Z      impossible
-- prev (S m') = m'
