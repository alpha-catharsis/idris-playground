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

-- %hint
-- public export
-- prevInjective : S n = S m -> prev (S n) = prev (S m)
-- prevInjective Refl = Refl

----------------
-- prev Even/Odd
----------------

-- %hint
-- public export
-- succEvenIsOdd : Even (S n) -> Odd (prev (S n))
-- succEvenIsOdd EvenZ               impossible
-- succEvenIsOdd (EvenS EvenZ)       = OddO
-- succEvenIsOdd (EvenS (EvenS prf)) = OddS (succEvenIsOdd (EvenS prf))

-- %hint
-- public export
-- succOddIsEven : Odd (S n) -> Even (prev (S n))
-- succOddIsEven OddO              = EvenZ
-- succOddIsEven (OddS OddO)       = EvenS (succOddIsEven OddO)
-- succOddIsEven (OddS (OddS prf)) = EvenS (succOddIsEven (OddS prf))
