---------------------
-- Module declaration
---------------------

module Playground.Rel.Rel

-------------------
-- Internal imports
-------------------

import Playground.Data.Bool.Bool
import Playground.Data.Void.Void
import Playground.Decidable.Decidable
import Playground.Logic.Inhabited
import Playground.Logic.Logic

----------------------
-- Relation definition
----------------------

public export
0 Rel : Type -> Type -> Type
Rel a b = a -> b -> Type

----------------------------
-- Proven relation interface
----------------------------

public export
interface ProvenRel (0 r : Rel a b) (0 x : a) (0 y : b) where
  provenRel : r x y

public export
prvn : (0 r : Rel a b) -> (0 x : a) -> (0 y : b) -> ProvenRel r x y => r x y
prvn r x y = provenRel {r} {x} {y}

public export
ProvenRel r x y => Inhabited (r x y) where
  inhabited = prvn r x y

-------------------------------
-- Disproven relation interface
-------------------------------

public export
interface DisprovenRel (0 r : Rel a b) (0 x : a) (0 y : b) where
  disprovenRel : Not (r x y)

public export
disp : (0 r : Rel a b) -> (0 x : a) -> (0 y : b) -> DisprovenRel r x y => Not (r x y)
disp r x y = disprovenRel {r} {x} {y}

public export
DisprovenRel r x y => Uninhabited (r x y) where
  uninhabited = disp r x y

-------------------------------
-- Decidable relation interface
-------------------------------

public export
interface DecRel a b (0 r : Rel a b) where
  decRel : (x : a) -> (y : b) -> Dec (r x y)

public export
rel : (0 r : Rel a b) -> DecRel a b r => (x : a) -> (y : b) -> Bool
rel r x y = isYes (decRel {r} x y)
