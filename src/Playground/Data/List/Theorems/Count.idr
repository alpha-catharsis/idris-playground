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
import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.First
import Playground.Data.List.Props.Last
import Playground.Data.List.Props.Proper

import Playground.Data.List.Theorems.Elem
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

----------------------
-- Count elem theorems
----------------------

export
notElemZeroCount : DecEq a => (x : a) -> (xs : List a) -> Not (Elem x xs) -> Count Z x xs
notElemZeroCount x [] elemContra = CountZero
notElemZeroCount x (y::xs) elemContra with (decEq x y)
  notElemZeroCount x (y::xs) elemContra | No eqContra = CountNext (notElemZeroCount x xs (notElemUncons elemContra))  eqContra
  notElemZeroCount x (y::xs) elemContra | Yes eqPrf = void (elemContra (rewrite eqPrf in Here))

export
elemExistPosCount : DecEq a => {x : a} -> {xs : List a} -> Elem x xs -> (m : Nat ** Count (S m) x xs)
elemExistPosCount {xs=x::xs'} Here = (count x xs' ** CountSucc (countPrf x xs'))
elemExistPosCount {xs=y::xs'} (There elemPrf) with (decEq x y)
  elemExistPosCount {xs=y::xs'} (There elemPrf) | No eqContra = let (m ** cntPrf) = elemExistPosCount elemPrf
                                                                in (m ** CountNext cntPrf eqContra)   
  elemExistPosCount {xs=y::xs'} (There elemPrf) | Yes eqPrf = rewrite sym eqPrf in let (m ** cntPrf) = elemExistPosCount elemPrf
                                                                            in (S m ** CountSucc cntPrf)   

-----------------------
-- Count first theorems
-----------------------

export
firstExistPosCount : DecEq a => {x : a} -> {xs : List a} -> First x xs -> (m : Nat ** Count (S m) x xs)
firstExistPosCount {xs=x::xs'} IsFirst = (count x xs' ** CountSucc (countPrf x xs'))

----------------------
-- Count last theorems
----------------------

export
lastExistPosCount : DecEq a => {x : a} -> {xs : List a} -> Last x xs -> (m : Nat ** Count (S m) x xs)
lastExistPosCount {xs=[x]} LastHere = (0 ** CountSucc CountZero)
lastExistPosCount {xs=y::xs'} (LastThere lastPrf) with (decEq x y)
  lastExistPosCount {xs=y::xs'} (LastThere lastPrf) | No eqContra = let (m ** cntPrf) = lastExistPosCount lastPrf
                                                                    in (m ** CountNext cntPrf eqContra)
  lastExistPosCount {xs=y::xs'} (LastThere lastPrf) | Yes eqPrf = rewrite sym eqPrf in let (m ** cntPrf) = lastExistPosCount lastPrf
                                                                                       in (S m ** CountSucc cntPrf)   


