---------------------
-- Module declaration
---------------------

module Playground.Rel.Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void
import Playground.Rel.Rel

---------------------
-- Decidable property
---------------------

public export
data Dec : Type -> Type where
  No : (contra : Not prop) -> Dec prop
  Yes : (prf : prop) -> Dec prop
