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
succInjective : S n = S m -> n = m
succInjective Refl = Refl

%hint
public export
noSuccInjective : Not (S n = S m) -> Not (n = m)
noSuccInjective contra prf = contra (cong S prf)

------------
-- succ cong
------------

%hint
public export
succCong : n = m -> S n = S m
succCong prf = cong S prf

%hint
public export
noSuccCong : Not (n = m) -> Not (S n = S m)
noSuccCong contra prf = contra (succInjective prf)

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
