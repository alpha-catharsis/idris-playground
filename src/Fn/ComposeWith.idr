---------------------
-- Module declaration
---------------------

module Fn.ComposeWith

-------------------
-- Internal imports
-------------------

import Data.Exp
import Fn.Comp
import Fn.Eq
import Fn.Id
import Rel.Equal

-------------------------------------
-- Compose with functional combinator
-------------------------------------

public export
composeWith : (f : b -> c) -> Exp b a -> Exp c a
composeWith f g = f . g

----------------------------------------------
-- Compose with functional combinator theorems
----------------------------------------------

