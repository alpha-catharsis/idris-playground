---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.HasLength

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.HasLength
import Playground.Data.List.Props.Proper

----------------------
-- Has length theorems
----------------------

hasLengthPrf : (xs : List a) -> HasLength xs (length xs)
hasLengthPrf [] = ZeroLen
hasLengthPrf (x::xs) = SuccLen (hasLengthPrf xs)

-----------------------------
-- Has length append theorems
-----------------------------

export
hasLengthAppend : (xs : List a) -> HasLength xs m -> HasLength ys n -> HasLength (xs ++ ys) (m + n)
hasLengthAppend [] ZeroLen ZeroLen = ZeroLen
hasLengthAppend [] ZeroLen (SuccLen lenPrf') = SuccLen lenPrf'
hasLengthAppend (x::xs) (SuccLen lenPrf) ZeroLen = SuccLen (hasLengthAppend xs lenPrf ZeroLen)
hasLengthAppend (x::xs) (SuccLen lenPrf) (SuccLen lenPrf') = SuccLen (hasLengthAppend xs lenPrf (SuccLen lenPrf'))

-----------------------------
-- Has length proper theorems
-----------------------------

export
properExistPosLength : (xs : List a) -> Proper xs -> (m : Nat ** HasLength xs (S m))
properExistPosLength [x] IsProper = (0 ** SuccLen ZeroLen)
properExistPosLength (x::x'::xs) IsProper = let (m ** lenPrf) = properExistPosLength (x'::xs) IsProper
                                            in (S m ** SuccLen lenPrf)

