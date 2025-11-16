---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Last

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Count
import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.Last
import Playground.Data.List.Props.Proper

import Playground.Data.List.Theorems.Elem
import Playground.Data.List.Theorems.Proper

----------------
-- Last theorems
----------------

export
lastPrf : {xs : List a} -> (properPrf : Proper xs) -> Last (last xs properPrf) xs
lastPrf {xs=[x]} IsProper = LastHere
lastPrf {xs=x::x'::xs'} IsProper = LastThere (lastPrf IsProper)

-----------------------
-- Last append theorems
-----------------------

export
lastRightAppendLast : {xs : List a} -> Last x ys -> Last x (xs ++ ys)
lastRightAppendLast {xs=[]} LastHere = LastHere
lastRightAppendLast {xs=[]} (LastThere lastPrf) = LastThere lastPrf
lastRightAppendLast {xs=x::xs'} LastHere = LastThere (lastRightAppendLast LastHere)
lastRightAppendLast {xs=x::xs'} (LastThere lastPrf) = LastThere (lastRightAppendLast (LastThere lastPrf))

-----------------------
-- Last proper theorems
-----------------------

export
notProperNotLast : Not (Proper xs) -> Not (Last x xs)
notProperNotLast properContra LastHere = properContra IsProper
notProperNotLast properContra (LastThere lastPrf) = properContra IsProper

export
properExistLast : {xs : List a} -> Proper xs -> (x : a ** Last x xs)
properExistLast {xs=[x]} IsProper = (x ** LastHere)
properExistLast {xs=x::x'::xs'} IsProper = let (xlast ** lastPrf) = properExistLast IsProper
                                           in (xlast ** LastThere lastPrf)

---------------------
-- Last elem theorems
---------------------
  
export
notElemNotLast : Not (Elem x xs) -> Not (Last x xs)
notElemNotLast elemContra LastHere = elemContra Here
notElemNotLast elemContra (LastThere lastPrf) = notElemNotLast (notElemUncons elemContra) lastPrf

