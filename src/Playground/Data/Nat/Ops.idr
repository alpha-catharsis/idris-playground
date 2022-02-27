---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

-----------------
-- Plus operation
-----------------

public export
plus : Nat -> Nat -> Nat
plus m Z = m
plus m (S n) = S (plus m n)
