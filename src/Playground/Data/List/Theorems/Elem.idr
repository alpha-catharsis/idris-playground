---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Elem

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.First
import Playground.Data.List.Props.Last
import Playground.Data.List.Props.Proper

--------------------------
-- Element append theorems
--------------------------

export
elemLeftAppendElem : Elem x xs -> Elem x (xs ++ ys)
elemLeftAppendElem Here = Here
elemLeftAppendElem (There elemPrf) = There (elemLeftAppendElem elemPrf)

export
elemRightAppendElem : (xs : List a) -> Elem x ys -> Elem x (xs ++ ys)
elemRightAppendElem [] Here = Here
elemRightAppendElem [] (There elemPrf) = There elemPrf
elemRightAppendElem (x::xs) Here = There (elemRightAppendElem xs Here)
elemRightAppendElem (x::xs) (There elemPrf) = There (elemRightAppendElem xs (There elemPrf))

--------------------------
-- Element proper theorems
--------------------------

export
notProperNotElem : Not (Proper xs) -> Not (Elem x xs)
notProperNotElem properContra Here = properContra IsProper
notProperNotElem properContra (There elemPrf) = properContra IsProper

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
