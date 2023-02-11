---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Succ

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

----------------
-- succ Even/Odd
----------------

succEvenIsOdd : Even n -> Odd (S n)
succEvenIsOdd EvenZ       = OddO
succEvenIsOdd (EvenS prf) = OddS (succEvenIsOdd prf)

succOddIsEven : Odd n -> Even (S n)
succOddIsEven OddO       = EvenS EvenZ
succOddIsEven (OddS prf) = EvenS (succOddIsEven prf)
