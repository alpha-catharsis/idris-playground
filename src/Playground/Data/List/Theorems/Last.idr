---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Last

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Last
import Playground.Data.List.Props.Proper

-----------------------
-- Last append theorems
-----------------------

export
lastRightAppendLast : (xs : List a) -> Last x ys -> Last x (xs ++ ys)
lastRightAppendLast [] LastHere = LastHere
lastRightAppendLast [] (LastThere lastPrf) = LastThere lastPrf
lastRightAppendLast (x::xs) LastHere = LastThere (lastRightAppendLast xs LastHere)
lastRightAppendLast (x::xs) (LastThere lastPrf) = LastThere (lastRightAppendLast xs (LastThere lastPrf))

-----------------------
-- Last proper theorems
-----------------------

export
notProperNotLast : Not (Proper xs) -> Not (Last x xs)
notProperNotLast properContra LastHere = properContra IsProper
notProperNotLast properContra (LastThere lastPrf) = properContra IsProper

export
properExistLast : (xs : List a) -> Proper xs -> (x : a ** Last x xs)
properExistLast [x] IsProper = (x ** LastHere)
properExistLast (x::x'::xs) IsProper = let (xlast ** lastPrf) = properExistLast (x'::xs) IsProper
                                       in (xlast ** LastThere lastPrf)
