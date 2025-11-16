---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.First

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Count
import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.First
import Playground.Data.List.Props.Proper

import Playground.Data.List.Theorems.Proper

-----------------
-- First theorems
-----------------

export
firstPrf : (properPrf : Proper xs) -> First (first xs properPrf) xs
firstPrf IsProper = IsFirst

export
prfToFirst : (firstPrf : First x xs) -> first xs (firstProper firstPrf) = x
prfToFirst firstPrf with (firstProper firstPrf)
  prfToFirst IsFirst | IsProper = Refl

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

----------------------
-- First elem theorems
----------------------

export
notElemNotFirst : Not (Elem x xs) -> Not (First x xs)
notElemNotFirst elemContra IsFirst = elemContra Here

