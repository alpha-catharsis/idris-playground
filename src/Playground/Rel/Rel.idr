---------------------
-- Module declaration
---------------------

module Playground.Rel.Rel

-------------------
-- Internal imports
-------------------

import Playground.Data.Bool.Bool
import Playground.Decidable.Decidable

----------------------
-- Relation definition
----------------------

public export
Rel : Type -> Type -> Type
Rel a b = a -> b -> Type

-------------------------------
-- Decidable relation interface
-------------------------------

public export
interface DecRel a b (0 r : Rel a b) where
  decRel : (x : a) -> (y : b) -> Dec (r x y)

public export
rel : (0 r : Rel a b) -> DecRel a b r => (x : a) -> (y : b) -> Bool
rel r x y = isYes (decRel {r} x y)
