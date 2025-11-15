---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.StartsWith

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.First
import Playground.Data.List.Props.StartsWith

-----------------------------
-- StartsWith append theorems
-----------------------------

export
startsWithLeftAppendStartsWith : StartsWith xs ys -> StartsWith (xs ++ zs) ys
startsWithLeftAppendStartsWith StartsNil = StartsNil
startsWithLeftAppendStartsWith (StartsNext startsPrf) = StartsNext (startsWithLeftAppendStartsWith startsPrf)

-----------------------------
-- StartsWith first theorems
-----------------------------

export
firstStartsWith : First x xs -> StartsWith xs [x]
firstStartsWith IsFirst = StartsNext StartsNil
