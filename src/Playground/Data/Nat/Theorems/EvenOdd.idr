---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.EvenOdd

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd

----------------------
-- Even basic theorems
----------------------

%hint
public export
notEvenSuccSucc : Not (Even m) -> Not (Even (S (S m)))
notEvenSuccSucc contra (EvenS prf) = contra prf

--------------------------
-- Even uninhabited values
--------------------------

%hint
public export
notEvenOne : Not (Even (S Z))
notEvenOne _ impossible

---------------------
-- Odd basic theorems
---------------------

%hint
public export
notOddSuccSucc : Not (Odd m) -> Not (Odd (S (S m)))
notOddSuccSucc contra (OddS prf) = contra prf

-------------------------
-- Odd uninhabited values
-------------------------

%hint
public export
notOddZero : Not (Odd Z)
notOddZero _ impossible

----------------------------
-- Even and Odd are disjunct
----------------------------

%hint
public export
evenNotOdd : Even m -> Not (Odd m)
evenNotOdd EvenZ       = notOddZero
evenNotOdd (EvenS prf) = notOddSuccSucc (evenNotOdd prf)

%hint
public export
oddNotEven : Odd m -> Not (Even m)
oddNotEven OddO       = notEvenOne
oddNotEven (OddS prf) = notEvenSuccSucc (oddNotEven prf)
