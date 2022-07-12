---------------------
-- Module declaration
---------------------

module Playground.Data.Word.Bitwise

-------------------
-- Internal imports
-------------------

import Playground.Data.Bit.Ops
import Playground.Data.Word.Word

------
-- Not
------

public export
not : Word k -> Word k
not (LSB b) = LSB (not b)
not (NB b rw) = (NB (not b) (not rw))
