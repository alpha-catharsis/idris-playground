---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Props.Odd

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

------
-- Odd
------

public export
data Odd : (n : Nat) -> Type where
  OddO : Odd (S Z)
  OddS : (prf : Odd n) -> Odd (S (S n))
