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

------------------
-- succ impossible
------------------

public export
notZeroSucc : (0 n : Nat) -> Not (Z = S n)
notZeroSucc _ _ impossible

public export
notSuccZero : (0 n : Nat) -> Not (S n = Z)
notSuccZero _ _ impossible

--------------------------
-- succ cong and injective
--------------------------

public export
succCong : (0 prf : m = n) -> S m = S n
succCong prf = cong S prf

public export
succInjective : (0 prf : S m = S n) -> m = n
succInjective Refl = Refl

public export
notSuccCong : Not (m = n) -> Not (S m = S n)
notSuccCong contra prf = contra (succInjective prf)

public export
notSuccInjective : Not (S m = S n) -> Not (m = n)
notSuccInjective contra prf = contra (succCong prf)

----------------
-- succ Even/Odd
----------------

-- public export
-- succEvenIsOdd : Even m -> Odd (succ m)
-- succEvenIsOdd EvenZ       = OddO
-- succEvenIsOdd (EvenS prf) = OddS (succEvenIsOdd prf)

-- public export
-- succOddIsEven : Odd m -> Even (succ m)
-- succOddIsEven OddO       = EvenS EvenZ
-- succOddIsEven (OddS prf) = EvenS (succOddIsEven prf)
