---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Elem

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

import Playground.Data.List.Theorems.EndsWith

-------------------
-- Element theorems
-------------------

export
notElemUncons : Not (Elem x (y::xs)) -> Not (Elem x xs)
notElemUncons elemContra Here = elemContra (There Here)
notElemUncons elemContra (There elemPrf) = elemContra (There (There elemPrf))

--------------------------
-- Element append theorems
--------------------------

export
elemLeftAppendElem : Elem x xs -> Elem x (xs ++ ys)
elemLeftAppendElem Here = Here
elemLeftAppendElem (There elemPrf) = There (elemLeftAppendElem elemPrf)

export
elemRightAppendElem : {xs : List a} -> Elem x ys -> Elem x (xs ++ ys)
elemRightAppendElem {xs=[]} Here = Here
elemRightAppendElem {xs=[]} (There elemPrf) = There elemPrf
elemRightAppendElem {xs=x::xs'} Here = There (elemRightAppendElem Here)
elemRightAppendElem {xs=x::xs'} (There elemPrf) = There (elemRightAppendElem (There elemPrf))

--------------------------
-- Element proper theorems
--------------------------

export
notProperNotElem : Not (Proper xs) -> Not (Elem x xs)
notProperNotElem properContra Here = properContra IsProper
notProperNotElem properContra (There elemPrf) = properContra IsProper

export
properExistElem : {xs : List a} -> Proper xs -> (x : a ** Elem x xs)
properExistElem {xs=x::xs'} IsProper = (x ** Here)

-------------------------
-- Element first theorems
-------------------------

export
firstElem : First x xs -> Elem x xs
firstElem IsFirst = Here

------------------------
-- Element last theorems
------------------------

export 
lastElem : Last x xs -> Elem x xs
lastElem LastHere = Here
lastElem (LastThere lastPrf)  = There (lastElem lastPrf)

------------------------------
-- Element starts with theorems
------------------------------

export
elemStartsWithElem : Elem x ys -> StartsWith xs ys -> Elem x xs
elemStartsWithElem Here (StartsNext startsPrf) = Here
elemStartsWithElem (There elemPrf) (StartsNext startsPrf) = There (elemStartsWithElem elemPrf startsPrf)

------------------------------
-- Element ends with theorems
------------------------------

export
elemEndsWithElem : Elem z ys -> EndsWith xs ys -> Elem z xs
elemEndsWithElem Here EndsSame = Here
elemEndsWithElem Here (EndsPrev endsPrf) = There (elemEndsWithElem Here endsPrf)
elemEndsWithElem (There elemPrf) EndsSame = There (elemEndsWithElem elemPrf EndsSame)
elemEndsWithElem (There elemPrf {xs=as}) (EndsPrev endsPrf {xs=bs}) = There (elemEndsWithElem elemPrf (endsWithUnsnoc endsPrf))

------------------------------
-- Element has length theorems
------------------------------

export
zeroLengthNotElem : HasLength xs Z -> Not (Elem x xs)
zeroLengthNotElem ZeroLen elemPrf = void (uninhabited elemPrf)

-------------------------
-- Element count theorems
-------------------------

export
zeroCountNotElem : Count Z x xs -> Not (Elem x xs)
zeroCountNotElem (CountNext cntPrf eqContra) Here = eqContra Refl
zeroCountNotElem (CountNext cntPrf eqContra) (There elemPrf) = zeroCountNotElem cntPrf elemPrf

export
posCountElem : Count (S m) x xs -> Elem x xs
posCountElem (CountSucc cntPrf) = Here
posCountElem (CountNext cntPrf eqContra) = There (posCountElem cntPrf)
