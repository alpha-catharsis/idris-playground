---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.First

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.First
import Playground.Data.List.Props.Proper

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

