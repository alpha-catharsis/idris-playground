---------------------
-- Module declaration
---------------------

module Playground.Rel.Truth.Truth

----------
-- Imports
----------

import Playground.Data.HList.HList
import Playground.Data.List.List
import Playground.Data.Unit.Unit
import Playground.Decidable.Decidable
import Playground.Rel.Rel

--------
-- Truth
--------

public export
data Truth : Type where
 MkTruth : Truth

public export
Rel tys Truth where
  RelTy _ _ = Unit

public export
DecRel tys Truth where
  decRel _ _ = Yes MkUnit

