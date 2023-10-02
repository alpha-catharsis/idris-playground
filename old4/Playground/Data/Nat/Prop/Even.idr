---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Prop.Even

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Succ

-------
-- Even
-------

-- public export
-- data Even : (m : Nat) -> Type where
--   EvenZ : Even Z
--   EvenS : (prf : Even m) -> Even (succ (succ m))
