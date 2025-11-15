---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.First

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.First
import Playground.Data.List.Props.Proper

-----------------
-- First theorems
-----------------

export
firstPrf : (properPrf : Proper xs) -> First (first xs properPrf) xs
firstPrf IsProper = IsFirst

------------------------
-- First append theorems
------------------------

export
firstLeftAppendFirst : First x xs -> First x (xs ++ ys)
firstLeftAppendFirst IsFirst = IsFirst

------------------------
-- First proper theorems
------------------------

export
notProperNotFirst : Not (Proper xs) -> Not (First x xs)
notProperNotFirst properContra IsFirst = properContra IsProper

export
properExistFirst : (xs : List a) -> Proper xs -> (x : a ** First x xs)
properExistFirst (x::xs) IsProper = (x ** IsFirst)
