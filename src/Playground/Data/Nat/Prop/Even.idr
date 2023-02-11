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
data Even : (n : Nat) -> Type where
  EvenZ : Even Z
  EvenS : (prf : Even n) -> Even (S (S n))
