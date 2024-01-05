---------------------
-- Module declaration
---------------------

module Playground.Fn.Fns.Apply

-------------------
-- Internal imports
-------------------

import Playground.Data.HList.HList
import Playground.Data.List.List
import Playground.Fn.Fn

-----------------
-- Apply function
-----------------

apply : HList as -> Fn as r -> r
apply [] r = r
apply (x::xs) f = apply xs (f x)
