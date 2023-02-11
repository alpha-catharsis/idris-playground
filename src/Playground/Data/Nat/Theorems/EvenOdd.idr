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
import Playground.Data.Nat.Props.Even
import Playground.Data.Nat.Props.Odd

----------------------------------
-- Even and Odd uninhabited values
----------------------------------

public export
notEvenOne : Not (Even (S Z))
notEvenOne _ impossible

public export
notOddZero : Not (Odd Z)
notOddZero _ impossible

public export
notEvenSuccSucc : Not (Even n) -> Not (Even (S (S n)))
notEvenSuccSucc contra (EvenS prf) = contra prf

public export
notOddSuccSucc : Not (Odd n) -> Not (Odd (S (S n)))
notOddSuccSucc contra (OddS prf) = contra prf

----------------------------
-- Even and Odd are disjunct
----------------------------

public export
evenNotOdd : Even n -> Not (Odd n)
evenNotOdd EvenZ       = notOddZero
evenNotOdd (EvenS prf) = notOddSuccSucc (evenNotOdd prf)

public export
oddNotEven : Odd n -> Not (Even n)
oddNotEven OddO       = notEvenOne
oddNotEven (OddS prf) = notEvenSuccSucc (oddNotEven prf)
