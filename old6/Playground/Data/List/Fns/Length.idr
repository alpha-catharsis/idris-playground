---------------------
-- Module declaration
---------------------

module Playground.Data.List.Fns.Length

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Data.Nat.Nat

-------------------
-- Length operation
-------------------

public export
length : List a -> Nat
length [] = Z
length (_::xs) = S (length xs)

