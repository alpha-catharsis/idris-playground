---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Minus

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LTE
import Playground.Data.Nat.Theorems.Ord

-----------------
-- minus operation
-----------------

public export
minus : (n : Nat) -> (m : Nat) -> {auto 0 prfLTE : LTE m n} -> Nat
minus Z (S m')      impossible
minus n Z           = n
minus (S n') (S m') = minus n' m' {prfLTE=bothPrevLTE prfLTE}
