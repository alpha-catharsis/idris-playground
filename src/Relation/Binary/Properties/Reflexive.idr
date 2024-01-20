---------------------
-- Module declaration
---------------------

module Relation.Binary.Properties.Reflexive

----------
-- Imports
----------

import Relation.Binary.Binary

---------------------
-- Reflexive relation
---------------------

public export
data Reflexive : (0 a : Type) -> (0 r : HRel a) -> Type where
  [noHints]
  MkReflexive : ({x : a} -> r x x) -> Reflexive a r

public export
refl : Reflexive a r => {x : a} -> r x x
refl @{MkReflexive reflPrf} = reflPrf
