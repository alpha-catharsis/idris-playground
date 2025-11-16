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

export
hasLengthPrf : {xs : List a} -> HasLength xs (length xs)
hasLengthPrf {xs=[]} = ZeroLen
hasLengthPrf {xs=x::xs'} = SuccLen hasLengthPrf

export
prfToLength : HasLength xs m -> length xs = m
prfToLength ZeroLen = Refl
prfToLength (SuccLen lenPrf) = cong S (prfToLength lenPrf)

-----------------------------
-- Has length append theorems
-----------------------------

export
hasLengthAppend : {xs : List a} -> HasLength xs m -> HasLength ys n -> HasLength (xs ++ ys) (m + n)
hasLengthAppend {xs=[]} ZeroLen ZeroLen = ZeroLen
hasLengthAppend {xs=[]} ZeroLen (SuccLen lenPrf') = SuccLen lenPrf'
hasLengthAppend {xs=x::xs'} (SuccLen lenPrf) ZeroLen = SuccLen (hasLengthAppend lenPrf ZeroLen)
hasLengthAppend {xs=x::xs'} (SuccLen lenPrf) (SuccLen lenPrf') = SuccLen (hasLengthAppend lenPrf (SuccLen lenPrf'))

-----------------------------
-- Has length proper theorems
-----------------------------

export
properExistPosLength : {xs : List a} -> Proper xs -> (m : Nat ** HasLength xs (S m))
properExistPosLength {xs=[x]} IsProper = (0 ** SuccLen ZeroLen)
properExistPosLength {xs=x::x'::xs'} IsProper = let (m ** lenPrf) = properExistPosLength IsProper
                                                in (S m ** SuccLen lenPrf)


