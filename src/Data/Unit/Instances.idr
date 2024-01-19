---------------------
-- Module declaration
---------------------

module Data.Unit.Instances

----------
-- Imports
----------

import Data.Unit.Unit
import Types.Inhabited

--------------------------
-- Unit inhabited instance
--------------------------

%hint
public export
InhabitedUnit : Inhabited Unit
InhabitedUnit = MkInhabited MkUnit
