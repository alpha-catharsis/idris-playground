---------------------
-- Module declaration
---------------------

module Fn.Bang

-------------------
-- Internal imports
-------------------

import Data.Unit
import Fn.Const

----------------
-- Bang function
----------------

public export
bang : a -> Unit
bang = const MkUnit
