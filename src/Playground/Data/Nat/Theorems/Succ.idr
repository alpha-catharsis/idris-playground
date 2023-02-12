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
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd

-----------------
-- succ injective
-----------------

%hint
public export
succInjective : n = m -> (S n = S m)
succInjective Refl = Refl

----------------
-- succ Even/Odd
----------------

%hint
public export
succEvenIsOdd : Even n -> Odd (S n)
succEvenIsOdd EvenZ       = OddO
succEvenIsOdd (EvenS prf) = OddS (succEvenIsOdd prf)

%hint
public export
succOddIsEven : Odd n -> Even (S n)
succOddIsEven OddO       = EvenS EvenZ
succOddIsEven (OddS prf) = EvenS (succOddIsEven prf)
