---------------------
-- Module declaration
---------------------

module Playground.Fun.Repeat.Repeat

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

--------------------
-- repeat definition
--------------------

public export
repeat : (f : a -> a) -> (j : Nat) -> (x : a) -> a
repeat f Z      x = x
repeat f (S j') x = f (repeat f j' x)
