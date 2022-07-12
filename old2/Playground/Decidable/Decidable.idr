---------------------
-- Module declaration
---------------------

module Playground.Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Playground.Data.Bool.Bool
import Playground.Data.Void.Void

------------------
-- Dec declaration
------------------

public export
data Dec : Type -> Type where
  No : (contra : p -> Void) -> Dec p
  Yes : (prf : p) -> Dec p

public export
isYes : Dec p -> Bool
isYes (No _) = False
isYes (Yes _) = True
