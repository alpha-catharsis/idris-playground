---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Ord

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LT
import Playground.Data.Nat.Rel.LTE

--------------------------------
-- LT and LTE uninhabited values
--------------------------------

sameNotLT : Not (LT n n)
sameNotLT LTZero impossible
sameNotLT (LTSucc prf) = sameNotLT prf

notLTELeftSucc : Not (LTE (S n) n)
notLTELeftSucc LTEZero impossible
notLTELeftSucc (LTESucc prf) = notLTELeftSucc prf

