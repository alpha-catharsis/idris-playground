---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Prop.Odd

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

------
-- Odd
------

public export
data Odd : (m : Nat) -> Type where
  OddO : Odd (S Z)
  OddS : (prf : Odd m) -> Odd (S (S m))
