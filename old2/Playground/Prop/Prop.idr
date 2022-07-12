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
import Playground.Logic.Inhabited
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
  provenProp : p x

public export
prvn : (0 p : Prop a) -> (0 x : a) -> ProvenProp p x => p x
prvn p x = provenProp {p} {x}

public export
ProvenProp p x => Inhabited (p x) where
  inhabited = prvn p x

-------------------------------
-- Disproven property interface
-------------------------------

public export
interface DisprovenProp (0 p : Prop a) (0 x : a) where
  disprovenProp : Not (p x)

public export
disp : (0 p : Prop a) -> (0 x : a) -> DisprovenProp p x => Not (p x)
disp p x = disprovenProp {p} {x}

public export
DisprovenProp p x => Uninhabited (p x) where
  uninhabited = disp p x

-------------------------------
-- Decidable property interface
-------------------------------

public export
interface DecProp a (0 p : Prop a) where
  decProp : (x : a) -> Dec (p x)

public export
prop : (0 p : Prop a) -> DecProp a p => (x : a) -> Bool
prop p x = isYes (decProp {p} x)
