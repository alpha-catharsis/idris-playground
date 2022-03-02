---------------------
-- Module declaration
---------------------

module Playground.Prop.Prop

-------------------
-- Internal imports
-------------------

import Playground.Data.Bool.Bool
import Playground.Data.Void.Void
import Playground.Decidable.Decidable
import Playground.Logic.Logic

----------------------
-- Property definition
----------------------

public export
Prop : Type -> Type
Prop a = a -> Type

----------------------------
-- Proven property interface
----------------------------

public export
interface ProvenProp (0 p : Prop a) (0 x : a) where
  prvn : p x

-------------------------------
-- Disproven property interface
-------------------------------

public export
interface DisprovenProp (0 p : Prop a) (0 x : a) where
  disp : Not (p x)

-------------------------------
-- Decidable property interface
-------------------------------

public export
interface DecProp a (0 p : Prop a) where
  decProp : (x : a) -> Dec (p x)

public export
prop : (0 p : Prop a) -> DecProp a p => (x : a) -> Bool
prop p x = isYes (decProp {p} x)
