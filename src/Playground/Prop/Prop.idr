---------------------
-- Module declaration
---------------------

module Playground.Prop.Prop

-------------------
-- Internal imports
-------------------

import Playground.Data.Bool.Bool
import Playground.Decidable.Decidable

----------------------
-- Property definition
----------------------

public export
Prop : Type -> Type
Prop a = a -> Type

-------------------------------
-- Decidable property interface
-------------------------------

public export
interface DecProp a (0 p : Prop a) where
  decProp : (x : a) -> Dec (p x)

public export
prop : (0 p : Prop a) -> DecProp a p => (x : a) -> Bool
prop p x = isYes (decProp {p} x)
