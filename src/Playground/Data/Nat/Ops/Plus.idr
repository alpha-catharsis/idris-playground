---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Plus

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper

-----------------
-- plus operation
-----------------

public export
plus : Nat -> Nat -> Nat
plus m n = hyper (S Z) m n
