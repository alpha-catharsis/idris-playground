---------------------
-- Module declaration
---------------------

module Playground.Prop.Decidable

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void

------------------
-- Dec declaration
------------------

public export
data Dec : Type -> Type where
  No : (0 contra : p -> Void) -> Dec p
  Yes : (0 prf : p) -> Dec p
