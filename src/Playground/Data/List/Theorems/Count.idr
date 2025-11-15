---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.Count

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Count
import Playground.Data.List.Props.Proper

import Playground.Data.List.Theorems.Proper

-----------------
-- Count theorems
-----------------

export
countPrf : DecEq a => (x : a) -> (xs : List a) -> Count (count x xs) x xs
countPrf x [] = CountZero
countPrf x (x'::xs) with (decEq x x')
  countPrf x (x'::xs) | No eqContra = CountNext (countPrf x xs) eqContra
  countPrf x (x'::xs) | Yes eqPrf = rewrite eqPrf in CountSucc (countPrf x' xs)

------------------------
-- Count append theorems
------------------------

export
countAppend : Count m x xs -> Count n x ys -> Count (m + n) x (xs ++ ys)
countAppend CountZero CountZero = CountZero
countAppend CountZero (CountSucc cntPrf') = CountSucc cntPrf'
countAppend CountZero (CountNext cntPrf' eqContra') = CountNext cntPrf' eqContra'
countAppend (CountSucc cntPrf) CountZero = CountSucc (countAppend cntPrf CountZero)
countAppend (CountSucc cntPrf) (CountSucc cntPrf') = CountSucc (countAppend cntPrf (CountSucc cntPrf'))
countAppend (CountSucc cntPrf) (CountNext cntPrf' eqContra') = CountSucc (countAppend cntPrf (CountNext cntPrf' eqContra'))
countAppend (CountNext cntPrf eqContra) CountZero = CountNext (countAppend cntPrf CountZero) eqContra
countAppend (CountNext cntPrf eqContra) (CountSucc cntPrf') = CountNext (countAppend cntPrf (CountSucc cntPrf')) eqContra
countAppend (CountNext cntPrf eqContra) (CountNext cntPrf' eqContra') = CountNext (countAppend cntPrf (CountNext cntPrf' eqContra')) eqContra

------------------------
-- Count proper theorems
------------------------

export
notProperZeroCount : {xs : List a} -> Not (Proper xs) -> Count Z x xs
notProperZeroCount properContra = rewrite notProperNil properContra in CountZero


