---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Plus

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

-----------------
-- plus operation
-----------------

public export
plus : Nat -> Nat -> Nat
plus Z m      = m
plus (S n') m = S (plus n' m)
