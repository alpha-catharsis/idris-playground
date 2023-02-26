---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Succ

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

-----------------
-- succ operation
-----------------

public export
%inline
succ : Nat -> Nat
succ = S
