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

------------
-- succ cong
------------

%hint
public export
succCong : m = n -> S m = S n
succCong prf = cong S prf

-----------------
-- succ injective
-----------------

%hint
public export
succInjective : S m = S n -> m = n
succInjective Refl = Refl

---------------
-- no succ cong
---------------

%hint
public export
noSuccCong : Not (m = n) -> Not (S m = S n)
noSuccCong contra prf = contra (succInjective prf)

--------------------
-- no succ injective
--------------------

%hint
public export
noSuccInjective : Not (S m = S n) -> Not (m = n)
noSuccInjective contra prf = contra (succCong prf)

----------------
-- succ Even/Odd
----------------

%hint
public export
succEvenIsOdd : Even m -> Odd (S m)
succEvenIsOdd EvenZ       = OddO
succEvenIsOdd (EvenS prf) = OddS (succEvenIsOdd prf)

%hint
public export
succOddIsEven : Odd m -> Even (S m)
succOddIsEven OddO       = EvenS EvenZ
succOddIsEven (OddS prf) = EvenS (succOddIsEven prf)
