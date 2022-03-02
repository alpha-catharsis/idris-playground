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
  prvn : r x y

-------------------------------
-- Disproven relation interface
-------------------------------

public export
interface DisprovenRel (0 r : Rel a b) (0 x : a) (0 y : b) where
  disp : Not (r x y)

-------------------------------
-- Decidable relation interface
-------------------------------

public export
interface DecRel a b (0 r : Rel a b) where
  decRel : (x : a) -> (y : b) -> Dec (r x y)

public export
rel : (0 r : Rel a b) -> DecRel a b r => (x : a) -> (y : b) -> Bool
rel r x y = isYes (decRel {r} x y)
