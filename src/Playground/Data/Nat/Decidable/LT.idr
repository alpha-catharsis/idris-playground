---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Decidable.LT

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LT
import Playground.Data.Nat.Theorems.Ord

---------------
-- Decidable LT
---------------

public export
decLT : (n : Nat) -> (m : Nat) -> Dec (LT n m)
decLT Z      Z      = No notLTEq
decLT Z      (S m') = Yes LTZero
decLT (S n') Z      = No notLeftSuccRightZeroLT
decLT (S n') (S m') = case decLT n' m' of
  No contra => No (notBothNextLT contra)
  Yes prf   => Yes (LTSucc prf)
