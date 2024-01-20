---------------------
-- Module declaration
---------------------

module Relation.Binary.Properties.Symmetric

----------
-- Imports
----------

import Relation.Binary.Binary

---------------------
-- Symmetric relation
---------------------

public export
data Symmetric : (0 a : Type) -> (0 r : HRel a) -> Type where
  [noHints]
  MkSymmetric : ({x, y : a} -> r x y -> r y x) -> Symmetric a r

public export
sym : Symmetric a r => {x, y : a} -> r x y -> r y x
sym @{MkSymmetric symPrf} = symPrf
