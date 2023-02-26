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
import Playground.Fn.Unrepeat.Unrepeat

-----------------
-- minus operation
-----------------

-- public export
-- minus : (m : Nat) -> (n : Nat) -> {auto 0 prfLTE : LTE n m} -> Nat
-- minus Z (S n')      impossible
-- minus m Z           = n
-- minus (S m') (S n') = minus m' n' {prfLTE=bothPrevLTE prfLTE}
