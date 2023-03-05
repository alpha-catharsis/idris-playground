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
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Succ
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd

----------------------
-- Even basic theorems
----------------------

public export
evenPred : (m : Nat) -> Even (S (S m)) -> Even m
evenPred Z         _           = EvenZ
evenPred (S Z)     EvenZ       impossible
evenPred (S (S _)) (EvenS prf) = prf

public export
notEvenSuccSucc : Not (Even m) -> Not (Even (succ (succ m)))
notEvenSuccSucc contra (EvenS prf) = contra prf

--------------------------
-- Even uninhabited values
--------------------------

public export
notEvenOne : Not (Even (succ Z))
notEvenOne _ impossible

---------------------
-- Odd basic theorems
---------------------

public export
oddPred : (m : Nat) -> Odd (S (S m)) -> Odd m
oddPred Z         OddO       impossible
oddPred (S Z)     _          = OddO
oddPred (S (S _)) (OddS prf) = prf

public export
notOddSuccSucc : Not (Odd m) -> Not (Odd (succ (succ m)))
notOddSuccSucc contra (OddS prf) = contra prf

-------------------------
-- Odd uninhabited values
-------------------------

public export
notOddZero : Not (Odd Z)
notOddZero _ impossible

----------------------------
-- Even and Odd are disjunct
----------------------------

public export
evenNotOdd : Even m -> Not (Odd m)
evenNotOdd EvenZ       = notOddZero
evenNotOdd (EvenS prf) = notOddSuccSucc (evenNotOdd prf)

public export
oddNotEven : Odd m -> Not (Even m)
oddNotEven OddO       = notEvenOne
oddNotEven (OddS prf) = notEvenSuccSucc (oddNotEven prf)
