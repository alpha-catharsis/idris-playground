---------------------
-- Module declaration
---------------------

module Relation.Binary.Properties.Transitive

----------
-- Imports
----------

import Relation.Binary.Binary

---------------------
-- Transitive relation
---------------------

public export
data Transitive : (0 a : Type) -> (0 r : HRel a) -> Type where
  [noHints]
  MkTransitive : ({x, y, z : a} -> r x y -> r y z -> r x z) -> Transitive a r

public export
trans : Transitive a r => {x, y, z : a} -> r x y -> r y z -> r x z
trans @{MkTransitive transPrf} = transPrf
