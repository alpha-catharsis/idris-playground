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
repeat : (n : Nat) -> (f : a -> a) -> (x : a) -> a
repeat Z      f  x = x
repeat (S n') f  x = f (repeat n' f x)
