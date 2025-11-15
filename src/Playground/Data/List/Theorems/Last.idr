---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Last

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Count
import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.HasLength
import Playground.Data.List.Props.Last
import Playground.Data.List.Props.Proper

import Playground.Data.List.Theorems.Elem

----------------
-- Last theorems
----------------

export
lastPrf : (xs : List a) -> (properPrf : Proper xs) -> Last (last xs properPrf) xs
lastPrf [x] IsProper = LastHere
lastPrf (x::x'::xs) IsProper = LastThere (lastPrf (x' :: xs) IsProper)

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

---------------------
-- Last elem theorems
---------------------
  
export
notElemNotLast : Not (Elem x xs) -> Not (Last x xs)
notElemNotLast elemContra LastHere = elemContra Here
notElemNotLast elemContra (LastThere lastPrf) = notElemNotLast (notElemUncons elemContra) lastPrf

---------------------------
-- Last has length theorems
---------------------------

export
zeroLengthNotLast : HasLength xs Z -> Not (Last x xs)
zeroLengthNotLast ZeroLen LastHere impossible
zeroLengthNotLast ZeroLen (LastThere lastPrf) impossible


