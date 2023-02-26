---------------------
-- Module declaration
---------------------

module Playground.Fn.Repeat.Repeat

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Fn.Identity.Identity

------------------
-- Repeat function
------------------

public export
repeat : (a -> a) -> Nat -> a -> a
repeat _ Z     x = x
repeat f (S m) x = repeat f m (f x)
