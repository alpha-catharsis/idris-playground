---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Proper

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.First
import Playground.Data.List.Props.Proper

-------------------------
-- Proper append theorems
-------------------------

export
properLeftAppendProper : Proper xs -> Proper (xs ++ ys)
properLeftAppendProper IsProper = IsProper

export
properRightAppendProper : (xs : List a) -> Proper ys -> Proper (xs ++ ys)
properRightAppendProper [] IsProper = IsProper
properRightAppendProper (x::xs) IsProper = IsProper

--------------------------
-- Proper element theorems
--------------------------

export
elemProper : Elem x xs -> Proper xs
elemProper Here = IsProper
elemProper (There elemPrf) = IsProper

------------------------
-- Proper first theorems
------------------------

export
firstProper : First x xs -> Proper xs
firstProper IsFirst = IsProper
