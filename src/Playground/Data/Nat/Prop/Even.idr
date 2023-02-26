---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Prop.Even

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

-------
-- Even
-------

public export
data Even : (m : Nat) -> Type where
  EvenZ : Even Z
  EvenS : (prf : Even m) -> Even (S (S m))
