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
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Succ
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd

------------------
-- succ impossible
------------------

-- public export
-- notZeroSucc : (0 n : Nat) -> Not (Z = S n)
-- notZeroSucc _ _ impossible

-- public export
-- notSuccZero : (0 n : Nat) -> Not (S n = Z)
-- notSuccZero _ _ impossible

--------------------------
-- succ cong and injective
--------------------------

-- public export
-- succCong : m = n -> succ m = succ n
-- succCong prf = cong succ prf

-- public export
-- succInjective : succ m = succ n -> m = n
-- succInjective Refl = Refl

-- public export
-- noSuccCong : Not (m = n) -> Not (succ m = succ n)
-- noSuccCong contra prf = contra (succInjective prf)

-- public export
-- noSuccInjective : Not (succ m = succ n) -> Not (m = n)
-- noSuccInjective contra prf = contra (succCong prf)

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
