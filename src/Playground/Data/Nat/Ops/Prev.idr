---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Prev

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LT
import Playground.Fn.Inverse.Inverse

-----------------
-- prev operation
-----------------

public export
prev : (m : Nat) -> {auto 0 prf : LT Z m} -> Nat
prev Z      {prf=LTZero} impossible
prev (S m') = fst (inverse S (S m') (Element m' Refl))

