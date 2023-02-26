---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Prev

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Prev
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd
import Playground.Data.Nat.Rel.LT

-----------------
-- prev injective
-----------------

%hint
public export
prevCong : S m = S n -> prev (S m) = prev (S n)
prevCong Refl = Refl

%hint
public export
prevInjective : prev (S m) = prev (S n) -> S m = S n
prevInjective Refl = Refl

%hint
public export
noPrevCong : Not (S m = S n) -> Not (prev (S m) = prev (S n))
noPrevCong contra prf = contra (prevInjective prf)

%hint
public export
noPrevInjective : Not (prev (S m) = prev (S n)) -> Not (S m = S n)
noPrevInjective contra prf = contra (prevCong prf)

----------------
-- prev Even/Odd
----------------

%hint
public export
succEvenIsOdd : Even (S m) -> Odd (prev (S m))
succEvenIsOdd EvenZ               impossible
succEvenIsOdd (EvenS EvenZ)       = OddO
succEvenIsOdd (EvenS (EvenS prf)) = OddS (succEvenIsOdd (EvenS prf))

%hint
public export
succOddIsEven : Odd (S m) -> Even (prev (S m))
succOddIsEven OddO              = EvenZ
succOddIsEven (OddS OddO)       = EvenS (succOddIsEven OddO)
succOddIsEven (OddS (OddS prf)) = EvenS (succOddIsEven (OddS prf))
