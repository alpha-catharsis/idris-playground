---------------------
-- Module declaration
---------------------

module Fn.Ap

-------------------
-- Internal imports
-------------------

import Data.Exp
import Data.Prod

-----------------
-- apply operator
-----------------

public export
ap : Prod (Exp b a) a -> b
ap (MkProd (MkExp f) x) = f x
