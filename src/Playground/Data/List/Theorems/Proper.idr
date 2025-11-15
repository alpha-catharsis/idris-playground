---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Proper

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Count
import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.EndsWith
import Playground.Data.List.Props.First
import Playground.Data.List.Props.HasLength
import Playground.Data.List.Props.Last
import Playground.Data.List.Props.Proper
import Playground.Data.List.Props.StartsWith

------------------
-- Proper theorems
------------------

export
notProperNil : {xs : List a} -> Not (Proper xs) -> xs = []
notProperNil {xs=[]} properContra = Refl
notProperNil {xs=x::xs'} properContra = void (properContra IsProper)

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

-----------------------
-- Proper last theorems
-----------------------

export
lastProper : Last x xs -> Proper xs
lastProper LastHere = IsProper
lastProper (LastThere lastPrf) = IsProper

-----------------------------
-- Proper has length theorems
-----------------------------

export
zeroLengthNotProper : HasLength xs Z -> Not (Proper xs)
zeroLengthNotProper ZeroLen IsProper impossible

export
hasPosLengthProper : HasLength xs (S m) -> Proper xs
hasPosLengthProper (SuccLen lenPrf) = IsProper

------------------------------
-- Proper starts with theorems
------------------------------

export
properStartsWithProper : Proper ys -> StartsWith xs ys -> Proper xs
properStartsWithProper IsProper (StartsNext startPrf) = IsProper

------------------------------
-- Proper ends with theorems
------------------------------

export
properEndsWithProper : Proper ys -> EndsWith xs ys -> Proper xs
properEndsWithProper IsProper EndsSame = IsProper
properEndsWithProper IsProper (EndsPrev endsPrf) = IsProper

------------------------
-- Proper count theorems
------------------------

export
posCountProper : Count (S m) x xs -> Proper xs
posCountProper (CountSucc cntPrf) = IsProper
posCountProper (CountNext cntPrf eqContra) = IsProper
